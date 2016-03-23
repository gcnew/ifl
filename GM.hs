{-# OPTIONS_GHC -Wall #-}

module GM where

import AST
import Heap
import Iseq
import Utils
import Parser (parse)
import Main (preludeDefs, lambdaPreludeDefs)

type GmStats = Int
type GmStack = [Addr]
type GmHeap = Heap Node
type GmCode = [Instruction]
type GmGlobals = ASSOC Name Addr

type GmEnvironment = ASSOC Name Int
type GmCompiledSC = (Name, Int, GmCode)
type GmCompiler = CoreExpr -> GmEnvironment -> GmCode

data Node = NNum Int            -- Numbers
          | NAp Addr Addr       -- Applications
          | NGlobal Int GmCode  -- Globals
          | NInd Addr           -- Indirection

data Instruction = Unwind
                 | PushGlobal Name
                 | PushInt Int
                 | Push Int
                 | MkAp
                 | Update Int
                 | Pop Int
                 | Slide Int
                 | Alloc Int
                 deriving (Eq, Show)

data GmState = GmState { gmCode    :: GmCode,     -- Current instruction stream
                         gmStack   :: GmStack,    -- Current stack
                         gmHeap    :: GmHeap,     -- Heap of nodes
                         gmGlobals :: GmGlobals,  -- Global addresses in heap
                         gmStats   :: GmStats     -- Statistics
                       }

data ShowStateOptions = ShowStateOptions { ssHeap     :: Bool
                                         , ssEnv      :: Bool
                                         , ssDump     :: Bool
                                         , ssLastOnly :: Bool
                                         , ssSCCode   :: Bool
                                         }

dbgOpts :: ShowStateOptions
dbgOpts = ShowStateOptions True True True False False

compactOpts :: ShowStateOptions
compactOpts = ShowStateOptions False False False True False

statInitial :: GmStats
statInitial = 0

statIncSteps :: GmStats -> GmStats
statIncSteps s = s + 1

statGetSteps :: GmStats -> Int
statGetSteps s = s

runProg :: String -> String
runProg = showResults compactOpts . eval . compile . parse

runDebugProg :: String -> String
runDebugProg = showResults dbgOpts . eval . compile . parse

eval :: GmState -> [GmState]
eval state = state : restStates
    where restStates | gmFinal state = []
                     | otherwise     = eval nextState
          nextState = doAdmin (step state)

doAdmin :: GmState -> GmState
doAdmin s = s { gmStats = statIncSteps (gmStats s) }

gmFinal :: GmState -> Bool
gmFinal s | [] <- gmCode s = True
          | otherwise      = False

step :: GmState -> GmState
step state = dispatch i (state { gmCode = is })
    where (i:is) = gmCode state

          dispatch (PushGlobal f) = pushGlobal f
          dispatch (PushInt n)    = pushInt n

          dispatch (Pop n)    = pop n
          dispatch (Push n)   = push n
          dispatch (Update n) = update n

          dispatch (Slide n)  = slide n
          dispatch (Alloc n)  = alloc n

          dispatch MkAp   = mkAp
          dispatch Unwind = unwind

pushGlobal :: Name -> GmState -> GmState
pushGlobal name state = state { gmStack = addr : (gmStack state) }
    where addr = aLookup (gmGlobals state) name (error ("Undeclared global " ++ name))

pushInt :: Int -> GmState -> GmState
pushInt n state = state { gmStack = addr : (gmStack state), gmHeap = heap' }
    where (heap', addr) = hAlloc (gmHeap state) (NNum n)

pushIntMemo :: Int -> GmState -> GmState
pushIntMemo n state = state {
                        gmStack = addr : (gmStack state),
                        gmHeap = heap',
                        gmGlobals = globals'
                      }
    where heap    = gmHeap state
          globals = gmGlobals state
          found   = aLookup globals (show n) hNull

          (globals', (heap', addr))
              | hIsNull found = ((show n, addr) : globals, hAlloc heap (NNum n))
              | otherwise     = (globals, (heap, found))


mkAp :: GmState -> GmState
mkAp state = state { gmStack = addr : rest, gmHeap = heap' }
    where (f:arg:rest)  = gmStack state
          (heap', addr) = hAlloc (gmHeap state) (NAp f arg)

push :: Int -> GmState -> GmState
push n state = state { gmStack = addr : stack }
    where stack = gmStack state
          addr  = stack !! n

pop :: Int -> GmState -> GmState
pop n state = state { gmStack = drop n (gmStack state) }

update :: Int -> GmState -> GmState
update n state = state { gmStack = rest, gmHeap = heap' }
    where (addr:rest) = gmStack state
          heap'       = hUpdate (gmHeap state) (rest !! n) (NInd addr)

slide :: Int -> GmState -> GmState
slide n state = state { gmStack = addr : drop n rest }
    where (addr:rest) = gmStack state

alloc :: Int -> GmState -> GmState
alloc n state = state { gmStack = addrs ++ gmStack state, gmHeap = heap' }
    where allocNode      = (\h _ -> hAlloc h $ NInd hNull)
          (heap', addrs) = mapAccuml allocNode (gmHeap state) [1..n]

unwind :: GmState -> GmState
unwind state = newState (hLookup (gmHeap state) addr)
    where heap  = gmHeap state
          stack = gmStack state

          (addr:rest) = stack

          newState (NNum _)   = state
          newState (NInd a1)  = state { gmCode = [ Unwind ], gmStack = a1:rest }
          newState (NAp a1 _) = state { gmCode = [ Unwind ], gmStack = a1:stack }

          newState (NGlobal n code)
            | length rest < n = error "Unwinding with too few arguments"
            | otherwise       = state { gmCode = code, gmStack = rearrange n heap stack }

rearrange :: Int -> GmHeap -> GmStack -> GmStack
rearrange n heap stack = take n (map getArg (tail stack)) ++ drop n stack
    where getArg addr | (NAp _ arg) <- hLookup heap addr = arg
                      | otherwise = error "Broken spine: non NAp node encountered"

compile :: CoreProgram -> GmState
compile program = GmState initialCode [] heap globals statInitial
    where scDefs = program ++ preludeDefs ++ lambdaPreludeDefs
          (heap, globals) = buildInitialHeap scDefs

initialCode :: GmCode
initialCode = [ PushGlobal "main", Unwind ]

buildInitialHeap :: CoreProgram -> (GmHeap, GmGlobals)
buildInitialHeap prog = mapAccuml allocateSc hInitial compiled
    where compiled = map compileSc prog

allocateSc :: GmHeap -> GmCompiledSC -> (GmHeap, (Name, Addr))
allocateSc heap (name, nargs, instns) = (heap', (name, addr))
    where (heap', addr) = hAlloc heap (NGlobal nargs instns)

compileSc :: (Name, [Name], CoreExpr) -> GmCompiledSC
compileSc (name, env, body) = (name, length env, compileR body (zip env [0..]))

compileR :: GmCompiler
compileR e env = compileC e env ++ [ Update n, Pop n, Unwind ]
    where n = length env

argOffset :: Int -> GmEnvironment -> GmEnvironment
argOffset n env = [(v, n+m) | (v,m) <- env]

compileC :: GmCompiler
compileC (EVar v) env
    | elem v (aDomain env) = [Push n]
    | otherwise            = [PushGlobal v]
    where n = aLookup env v (error "Can’t happen")

compileC (ENum n) _      = [PushInt n]

compileC (EAp e1 e2) env = compileC e2 env ++ compileC e1 (argOffset 1 env) ++ [ MkAp ]

compileC (ELet rec defs expr) env
    | rec       = [ Alloc n ]
                    ++ compileDefs True defs env'
                    ++ replicate n (Update $ n - 1)
                    ++ compileC expr env'
                    ++ [ Slide n ]

    | otherwise = compileDefs False defs env
                    ++ compileC expr env'
                    ++ [ Slide n ]

    where n    = length defs
          env' = zip (map fst defs) [n-1, n-2 .. 0] ++ argOffset n env

compileC (EConstr _ _) _ = error "EConstr: not yet implemented"
compileC (ECase _ _) _   = error "ECase: not yet implemented"
compileC (ELam _ _) _    = error "ELam: not yet implemented"

compileDefs :: Bool -> [(Name, CoreExpr)] -> GmEnvironment -> GmCode
compileDefs _ [] _ = []

compileDefs rec ((name, expr):defs) env = compileC expr env ++ compileDefs rec defs env'
    where env' | rec       = env
               | otherwise = (name, 0) : argOffset 1 env

compiledPrimitives :: [GmCompiledSC]
compiledPrimitives = []

showResults :: ShowStateOptions -> [GmState] -> [Char]
showResults opts states = iDisplay $ iConcat [
                                scDefOutp,
                                iStr "State transitions",
                                iNewline, iNewline,
                                stateOutp,
                                iNewline,
                                showStats lastState
                            ]
    where (s:_) = states
          lastState = last states

          nl2 = iNewline `iAppend` iNewline

          scDefOutp | ssSCCode opts   = iInterleave iNewline [
                                            iStr "Supercombinator definitions",
                                            iInterleave nl2 (map (showSC s) (gmGlobals s)),
                                            iNewline
                                        ]
                    | otherwise       = iNil

          stateOutp | ssLastOnly opts = showState dbgOpts lastState `iAppend` iNewline
                    | otherwise       = iLayn (map (showState opts) states)

showFWAddr :: Addr -> Iseq -- Show address in field of width 4
showFWAddr addr = iStr (space (4 - length str) ++ str)
    where str = showaddr addr

showSC :: GmState -> (Name, Addr) -> Iseq
showSC s (name, addr) = iConcat [ iStr "Code for ",
                                  iStr name, iNewline,
                                  showInstructions code ]

    where (NGlobal _ code) = (hLookup (gmHeap s) addr)

showInstructions :: GmCode -> Iseq
showInstructions [] = iStr "Empty"
showInstructions is = iInterleave iNewline (map showInstruction is)

showInstruction :: Instruction -> Iseq
showInstruction Unwind  = iStr  "Unwind"
showInstruction MkAp    = iStr  "MkAp"

showInstruction (PushInt n)    = (iStr "PushInt ") `iAppend` (iNum n)
showInstruction (PushGlobal f) = (iStr "PushGlobal ") `iAppend` (iStr f)

showInstruction (Pop n)    = (iStr "Pop ")    `iAppend` (iNum n)
showInstruction (Push n)   = (iStr "Push ")   `iAppend` (iNum n)
showInstruction (Update n) = (iStr "Update ") `iAppend` (iNum n)

showInstruction (Slide n)  = (iStr "Slide ")  `iAppend` (iNum n)
showInstruction (Alloc n)  = (iStr "Alloc ")  `iAppend` (iNum n)

showState :: ShowStateOptions -> GmState -> Iseq
showState opts s | null views = iNil
                 | otherwise  = iSplitView views `iAppend` iNewline

    where stackLines = showStack s

          codeLines  = showInstructions (gmCode s)

          heapLines | ssHeap opts = showHeap s
                    | otherwise   = iNil

          envLines  | ssEnv opts  = showEnv (gmGlobals s)
                    | otherwise   = iNil

          views = filter (not . iIsNil) [ heapLines,
                                          envLines,
                                          codeLines,
                                          stackLines ]

showStack :: GmState -> Iseq
showStack s = iInterleave iNewline stackItems
    where stackItems = (map (showStackItem s) (reverse (gmStack s)))

showStackItem :: GmState -> Addr -> Iseq
showStackItem s a = iConcat [ showFWAddr a,
                              iStr ": ",
                              showNode s a (hLookup (gmHeap s) a) ]

showNode :: GmState -> Addr -> Node -> Iseq
showNode _ _ (NNum n)    = iNum n
showNode _ _ (NInd addr) = iStr "NInd " `iAppend` showFWAddr addr

showNode s a (NGlobal _ _) = iConcat [ iStr "Global ", iStr v ]
    where v = head [n | (n,b) <- gmGlobals s, a == b]

showNode _ _ (NAp a1 a2) = iConcat [ iStr "Ap ", showFWAddr a1,
                                     iStr " ",   showFWAddr a2 ]

showHeap :: GmState -> Iseq
showHeap state = iInterleave iNewline (map formatter tuples)
    where formatter (addr, node) = iConcat [ showFWAddr addr,
                                             iStr " -> ",
                                             showNode state addr node ]

          heap   = gmHeap state
          tuples =  [ (addr, hLookup heap addr) | addr <- hAddresses heap ]

showEnv :: GmGlobals -> Iseq
showEnv = iInterleave iNewline . map formatter
    where formatter (name, addr) = iConcat [ iStr name, iStr " -> ", showFWAddr addr ]

showStats :: GmState -> Iseq
showStats s = iConcat [ iStr "Steps taken = ", iNum (statGetSteps (gmStats s)) ]
