{-# OPTIONS_GHC -Wall #-}

module GM where

import Control.Monad (foldM)
import Control.Monad.Trans.State hiding (state)

import Data.List (find, isPrefixOf)

import AST
import Heap
import Iseq
import Utils
import Lexer (clex)
import Parser (parse, pPack)
import Main (preludeDefs, extraPreludeDefs, casePreludeDefs)

type GmStats = Int
type GmStack = [Addr]
type GmOutput = [Int]
type GmHeap = Heap Node
type GmDump = [GmDumpItem]
type GmCode = [Instruction]
type GmGlobals = ASSOC Name Addr

type GmDumpItem = (GmCode, GmStack)

type GmEnvironment = ASSOC Name Int
type GmCompiledSC = (Name, Int, GmCode)
type GmCompiler = CoreExpr -> GmEnvironment -> State GmGlobals GmCode

data Node = NNum Int            -- Numbers
          | NAp Addr Addr       -- Applications
          | NGlobal Int GmCode  -- Globals
          | NInd Addr           -- Indirection
          | NConstr Int [Addr]  -- Tag, list of components

data Instruction = Unwind
                 | PushGlobal Name
                 | PushInt Int
                 | Push Int
                 | MkAp
                 | Update Int
                 | Pop Int
                 | Slide Int
                 | Alloc Int
                 | Eval
                 | Pack Int Int
                 | CaseJump [(Int, GmCode)]
                 | Split Int
                 | Print
                 | Abort
                 | Add | Sub | Mul | Div | Neg
                 | Eq | Ne | Lt | Le | Gt | Ge
                 deriving (Eq, Show)

data GmState = GmState { gmCode    :: GmCode,     -- Current instruction stream
                         gmStack   :: GmStack,    -- Current stack
                         gmDump    :: GmDump,     -- Stack of Code/Stack pairs
                         gmHeap    :: GmHeap,     -- Heap of nodes
                         gmGlobals :: GmGlobals,  -- Global addresses in heap
                         gmOutput  :: GmOutput,   -- Execution output
                         gmStats   :: GmStats     -- Statistics
                       }

data ShowStateOptions = ShowStateOptions { ssHeap     :: Bool
                                         , ssEnv      :: Bool
                                         , ssDump     :: Bool
                                         , ssLastOnly :: Bool
                                         , ssSCCode   :: Bool
                                         }

dbgOpts :: ShowStateOptions
dbgOpts = ShowStateOptions True True True False True

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
          dispatch Eval   = forceEval
          dispatch Print  = primPrint

          dispatch Abort  = error "Core: abort"

          dispatch Neg = aritmetic1 negate

          dispatch Add = aritmetic2 (+)
          dispatch Sub = aritmetic2 (-)
          dispatch Mul = aritmetic2 (*)
          dispatch Div = aritmetic2 div

          dispatch Eq = comparison (==)
          dispatch Ne = comparison (/=)
          dispatch Lt = comparison (<)
          dispatch Le = comparison (<=)
          dispatch Gt = comparison (>)
          dispatch Ge = comparison (>=)

          dispatch (Pack tag arity) = pack tag arity
          dispatch (CaseJump jl)    = caseJump jl
          dispatch (Split n)        = constrSplit n

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

-- update should create NInd node according to the book.
-- the current implementation directly updates the node
-- saving clutter and.. <indirections>
-- are there any negative consequences I have missed?
update :: Int -> GmState -> GmState
update n state = state { gmStack = rest, gmHeap = heap' }
    where (addr:rest) = gmStack state
          heap        = gmHeap state
          -- node        = NInd addr
          node        = hLookup heap addr
          heap'       = hUpdate heap (rest !! n) node

slide :: Int -> GmState -> GmState
slide n state = state { gmStack = addr : drop n rest }
    where (addr:rest) = gmStack state

alloc :: Int -> GmState -> GmState
alloc n state = state { gmStack = addrs ++ gmStack state, gmHeap = heap' }
    where allocNode      = (\h _ -> hAlloc h $ NInd hNull)
          (heap', addrs) = mapAccuml allocNode (gmHeap state) [1..n]

isDataNode :: Node -> Bool
isDataNode (NNum _)      = True
isDataNode (NConstr _ _) = True
isDataNode _             = False

forceEval :: GmState -> GmState
forceEval state
    | isDataNode node = state
    | otherwise       = state { gmCode  = [ Unwind ],
                                gmStack = [ addr ],
                                gmDump  = (code, rest) : dump }
    where stack = gmStack state
          code  = gmCode state
          dump  = gmDump state

          (addr:rest) = stack
          node        = hLookup (gmHeap state) addr

primPrint :: GmState -> GmState
primPrint state = state { gmStack = rest, gmOutput = out : gmOutput state }
    where (addr:rest) = gmStack state
          node = hLookup (gmHeap state) addr

          out | (NNum n) <- node = n
              | otherwise        = error "Print: number expected"

pack :: Int -> Int -> GmState -> GmState
pack tag arity state
    | length parts /= arity = error "NConstr: not enough arguments"
    | otherwise             = state { gmStack = addr : rest, gmHeap = heap' }

    where stack = gmStack state
          parts = take arity stack
          rest  = drop arity stack

          (heap', addr) = hAlloc (gmHeap state) (NConstr tag parts)

caseJump :: [(Int, GmCode)] -> GmState -> GmState
caseJump jumpLocs state = state { gmCode = code' ++ gmCode state }
    where (addr:_) = gmStack state
          node = hLookup (gmHeap state) addr

          code' | (NConstr tag _) <- node
                    = aLookup jumpLocs tag (error "Case: no handler matched")

                | otherwise = error "Case: not a constructor node"

constrSplit :: Int -> GmState -> GmState
constrSplit n state = state { gmStack = parts ++ rest }
    where (addr:rest) = gmStack state
          node = hLookup (gmHeap state) addr

          parts | (NConstr _ as) <- node, length as == n
                    = as
                | otherwise = error "Split: not a constructor node or wrong arity"

unwind :: GmState -> GmState
unwind state = newState (hLookup heap addr)
    where heap  = gmHeap state
          stack = gmStack state
          dump  = gmDump state

          (addr:rest) = stack

          unwindData
            | ((code, stack') : dump') <- dump
                = state { gmCode = code, gmStack = addr : stack', gmDump = dump' }
            | otherwise = state

          newState (NNum _)      = unwindData
          newState (NConstr _ _) = unwindData

          newState (NInd a1)  = state { gmCode = [ Unwind ], gmStack = a1:rest }
          newState (NAp a1 _) = state { gmCode = [ Unwind ], gmStack = a1:stack }

          newState (NGlobal n code)
            | nArgs < n = case dump of
                ((code', stack') : dump') -> state { gmCode = code',
                                                     gmStack = last stack : stack',
                                                     gmDump = dump' }

                _                         -> error "Unwinding with too few arguments"

            | otherwise = state { gmCode = code, gmStack = rearrange n heap stack }
            where nArgs = length rest

rearrange :: Int -> GmHeap -> GmStack -> GmStack
rearrange n heap stack = take n (map getArg (tail stack)) ++ drop n stack
    where getArg addr | (NAp _ arg) <- hLookup heap addr = arg
                      | otherwise = error "Broken spine: non NAp node encountered"

compile :: CoreProgram -> GmState
compile program = GmState initialCode [] [] heap globals [] statInitial
    where scDefs = program ++ preludeDefs ++ extraPreludeDefs ++ casePreludeDefs
          (heap, globals) = buildInitialHeap scDefs

initialCode :: GmCode
initialCode = [ PushGlobal "main", Unwind ] -- no idea why we need Eval,
                                            -- Unwind works just fine..

buildInitialHeap :: CoreProgram -> (GmHeap, GmGlobals)
buildInitialHeap prog = mapAccuml allocateSc hInitial compiled
    where globalsMap = foldr (\(name, _, _) acc -> (name, hNull) : acc) [] prog
          (cSc, globalsMap') = runState (mapM compileSc prog) globalsMap
          synth = filter (isPrefixOf "$") (map fst globalsMap')
          cSynth = map compileS synth
          compiled = cSc ++ cSynth ++ compiledPrimitives

allocateSc :: GmHeap -> GmCompiledSC -> (GmHeap, (Name, Addr))
allocateSc heap (name, nargs, instns) = (heap', (name, addr))
    where (heap', addr) = hAlloc heap (NGlobal nargs instns)

compileSc :: (Name, [Name], CoreExpr) -> State GmGlobals GmCompiledSC
compileSc (name, env, body) = do code <- compileR body (zip env [0..])
                                 return (name, length env, code)

compileR :: GmCompiler
compileR e env = do code <- compileE e env
                    return $ code ++ [ Update n, Pop n, Unwind ]
    where n = length env

argOffset :: Int -> GmEnvironment -> GmEnvironment
argOffset n env = [(v, n+m) | (v,m) <- env]

compileS :: String -> GmCompiledSC
compileS name = (name, arity, [ Pack tag arity, Update 0, Unwind ])
    where (EConstr tag arity) = fst . head . pPack . clex 1 $ tail name

compileC :: GmCompiler
compileC (EVar v) env
    | aHasKey v env = return [Push n]
    | otherwise     = return [PushGlobal v]
    where n = aLookup env v (error "Can’t happen")

compileC (ENum n) _      = return [PushInt n]

compileC node@(EAp _ _) env
    -- saturated ctor
    | (EConstr tag arity : aps) <- spine,
      n - 1 == arity
        = do (_, code) <- foldM (compileAp env compileC) (n - 2, []) aps
             return $ code ++ [Pack tag arity]

    -- not-saturated ctor
    | (EConstr tag arity : aps) <- spine,
      n - 1 /= arity
        = do ctorName <- getCtorName tag arity
             (_, code) <- foldM (compileAp env compileC) (n - 2, []) aps
             return $ code ++ (PushGlobal ctorName : replicate (n - 1) MkAp)

    | otherwise
        = do (_, code) <- foldM (compileAp env compileC) (n - 1, []) spine
             return $ code ++ replicate (n - 1) MkAp

    where spine = unfoldAp node
          n     = length spine


compileC (ELet rec defs expr) env = compileLet compileC rec defs expr env

compileC (EConstr tag arity) _
    | arity == 0 = return [Pack tag arity]
    | otherwise  = do ctorName <- getCtorName tag arity
                      return [PushGlobal ctorName]

compileC (ECase _ _) _   = error "compileC: ECase: not yet implemented"
compileC (ELam _ _) _    = error "compileC: ELam: not yet implemented"

compileE :: GmCompiler
compileE (ENum n) _               = return [PushInt n]
compileE (ELet rec defs expr) env = compileLet compileE rec defs expr env

compileE (ECase expr alts) env    = do cExpr <- compileE expr env
                                       cAlts <- mapM compileA alts

                                       return $ cExpr ++ [CaseJump cAlts]

    where compileA (tag, vars, body) = do let n    = length vars
                                              env' = zip vars [0..] ++ argOffset n env

                                          cBody <- compileE body env'
                                          return (tag, Split n : cBody ++ [Slide n])

compileE expr env
    = do globals <- get
         case () of
          _ | (EVar op : aps)        <- unfoldAp expr,
              Just (_, arity, instr) <- findBuiltIn op,  -- it is a built-in
              not (aHasKey op env),                      -- and not a local variable
              not (aHasKey op globals)                   -- and not a global variable

                -> do let strictAps = take arity aps
                          lazyAps   = drop arity aps

                      strictRes <- foldM (compileAp env compileE) (length aps - 1, instr) strictAps
                      (_, code) <- foldM (compileAp env compileC) strictRes lazyAps

                      return (code ++ replicate (length lazyAps) MkAp)

            | otherwise
                -> do cExpr <- compileC expr env
                      return (cExpr ++ [ Eval ])

compileAp :: GmEnvironment
             -> GmCompiler
             -> (Int, GmCode)
             -> CoreExpr
             -> State GmGlobals (Int, GmCode)
compileAp env cc (offset, code) expr = do cExpr <- cc expr env'
                                          return (offset - 1, cExpr ++ code)
    where env' = argOffset offset env

findBuiltIn :: String -> Maybe (Name, Int, GmCode)
findBuiltIn op = find (\(name, _, _) -> name == op) buildIns

unfoldAp :: CoreExpr -> [CoreExpr]
unfoldAp expr = unfold expr []
    where unfold (EAp e1 e2) acc = unfold e1 (e2 : acc)
          unfold n acc           = n : acc

getCtorName :: Int -> Int -> State GmGlobals String
getCtorName tag arity = do globals <- get

                           if aHasKey name globals
                              then return ()
                              else put ((name, hNull) : globals)

                           return name

    where name = "$Pack{" ++ show tag ++ "," ++ show arity ++ "}"

compileLet :: GmCompiler -> Bool -> [(Name, CoreExpr)] -> GmCompiler
compileLet compiler rec defs expr env
    | rec       = do cDefs <- compileDefs True defs env'
                     cExpr <- compiler expr env'

                     return $ [ Alloc n ]
                                ++ cDefs
                                ++ replicate n (Update $ n - 1)
                                ++ cExpr
                                ++ [ Slide n ]

    | otherwise = do cDefs <- compileDefs False defs env
                     cExpr <- compiler expr env'

                     return $ cDefs ++ cExpr ++ [ Slide n ]

    where n    = length defs
          env' = zip (map fst defs) [n-1, n-2 .. 0] ++ argOffset n env

compileDefs :: Bool -> [(Name, CoreExpr)] -> GmEnvironment -> State GmGlobals GmCode
compileDefs _ [] _ = return []

compileDefs rec ((name, expr):defs) env = do cExpr <- compileC expr env
                                             cDefs <- compileDefs rec defs env'

                                             return $ cExpr ++ cDefs
    where env' | rec       = env
               | otherwise = (name, 0) : argOffset 1 env

boxInteger :: Int -> GmState -> GmState
boxInteger n state = state { gmStack = addr : gmStack state, gmHeap = heap' }
    where (heap', addr) = hAlloc (gmHeap state) (NNum n)

unboxInteger :: Addr -> GmState -> Int
unboxInteger addr state = case hLookup (gmHeap state) addr of
        (NNum n) -> n
        _        -> error "Unboxing a non-integer"

boxBoolean :: Bool -> GmState -> GmState
boxBoolean b state = state { gmStack = addr : gmStack state, gmHeap = heap' }
    where (heap', addr) = hAlloc (gmHeap state) (findPrimDef key)

          findPrimDef prim = NInd (aLookup (gmGlobals state) prim err)
              where err = error $ "Primitive definition `" ++ prim ++ "` not found!"

          key | b         = "True"
              | otherwise = "False"

unboxBoolean :: Addr -> GmState -> Bool
unboxBoolean addr state = case hLookup (gmHeap state) addr of
        (NNum 1) -> True
        (NNum 0) -> False
        _        -> error "Unboxing a non-boolean"

primitive1 :: (a -> GmState -> GmState)  -- boxing function
              -> (Addr -> GmState -> b)  -- unboxing function
              -> (b -> a)                -- operator
              -> GmState -> GmState      -- in state & retval
primitive1 box unbox op state = box (op (unbox addr state)) (state { gmStack = stack' })
    where (addr:stack') = gmStack state

primitive2 :: (a -> GmState -> GmState)  -- boxing function
              -> (Addr -> GmState -> b)  -- unboxing function
              -> (b -> b -> a)           -- operator
              -> GmState -> GmState      -- in state & retval
primitive2 box unbox op state = box result (state { gmStack = stack' })
    where (a1:a2:stack') = gmStack state
          result         = unbox a1 state `op` unbox a2 state

aritmetic1 :: (Int -> Int) -> GmState -> GmState
aritmetic1 = primitive1 boxInteger unboxInteger

aritmetic2 :: (Int -> Int -> Int) -> GmState -> GmState
aritmetic2 = primitive2 boxInteger unboxInteger

comparison :: (Int -> Int -> Bool) -> GmState -> GmState
comparison = primitive2 boxBoolean unboxInteger

buildIns :: [(Name, Int, GmCode)]  -- (name, arity, instruction)
buildIns = [ ("negate", 1, [Neg]),

             ("+", 2, [Add]), ("-", 2, [Sub]),
             ("*", 2, [Mul]), ("/", 2, [Div]),

             ( ">", 2, [Gt, Eval]), (">=", 2, [Ge, Eval]),
             ( "<", 2, [Lt, Eval]), ("<=", 2, [Le, Eval]),
             ("==", 2, [Eq, Eval]), ("/=", 2, [Ne, Eval]) ]

compiledPrimitives :: [GmCompiledSC]
compiledPrimitives = map builtInCC buildIns ++ [
        ("abort", 0, [ Abort ]),
        ("print", 2, [ Eval, Print, Update 0, Unwind ])
        -- naive:
        -- ("print", 2, [ Push 0, Eval, Print, Push 1, Update 2, Pop 2, Unwind ])
    ]

builtInCC :: (Name, Int, GmCode) -> GmCompiledSC
builtInCC (name, arity, ins) = (name, arity, force ++ ins ++ clean)
    where force = concat $ replicate arity [ Push (arity - 1), Eval ]
          clean = [ Update arity, Pop arity, Unwind ]

showResults :: ShowStateOptions -> [GmState] -> String
showResults opts states = iDisplay $ iConcat [
                                scDefOutp,
                                iStr "State transitions",
                                iNewline, iNewline,
                                stateOutp,
                                iNewline,
                                showOutput lastState,
                                iNewline,
                                showStats lastState
                            ]
    where (s:_) = states
          lastState = last states

          nl2 = iNewline `iAppend` iNewline

          scDefOutp | ssSCCode opts   = iInterleave iNewline [
                                            iStr "Supercombinator definitions:\n",
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
showInstruction Unwind  = iStr "Unwind"
showInstruction MkAp    = iStr "MkAp"
showInstruction Abort   = iStr "Abort"

showInstruction (PushInt n)    = (iStr "PushInt ") `iAppend` (iNum n)
showInstruction (PushGlobal f) = (iStr "PushGlobal ") `iAppend` (iStr f)

showInstruction (Pop n)    = (iStr "Pop ")    `iAppend` (iNum n)
showInstruction (Push n)   = (iStr "Push ")   `iAppend` (iNum n)
showInstruction (Update n) = (iStr "Update ") `iAppend` (iNum n)

showInstruction (Slide n)  = (iStr "Slide ")  `iAppend` (iNum n)
showInstruction (Alloc n)  = (iStr "Alloc ")  `iAppend` (iNum n)

showInstruction Eval  = iStr "Eval"
showInstruction Print = iStr "Print"

showInstruction (Pack tag arity) = iConcat [ iStr "Pack{",
                                             iNum tag, iStr ", ",
                                             iNum arity, iStr "}" ]

showInstruction (CaseJump _)  = iStr "CaseJump"
showInstruction (Split n)     = iStr "Split " `iAppend` iNum n

showInstruction Add  = iStr "Add"
showInstruction Sub  = iStr "Sub"
showInstruction Mul  = iStr "Mul"
showInstruction Div  = iStr "Div"
showInstruction Neg  = iStr "Neg"

showInstruction Eq   = iStr "Eq"
showInstruction Ne   = iStr "Ne"
showInstruction Lt   = iStr "Lt"
showInstruction Le   = iStr "Le"
showInstruction Gt   = iStr "Gt"
showInstruction Ge   = iStr "Ge"

showState :: ShowStateOptions -> GmState -> Iseq
showState opts s | null views = iNil
                 | otherwise  = iSplitView views `iAppend` iNewline

    where stackLines = showStack s

          dumpLines = showDump s

          codeLines  = showInstructions (gmCode s)

          heapLines | ssHeap opts = showHeap s
                    | otherwise   = iNil

          envLines  | ssEnv opts  = showEnv (gmGlobals s)
                    | otherwise   = iNil

          views = filter (not . iIsNil) [ heapLines,
                                          envLines,
                                          codeLines,
                                          stackLines,
                                          dumpLines ]

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
    where v | (name:_) <- [n | (n,b) <- gmGlobals s, a == b] = name

            -- happens with lambda prelude and direct updates instead
            -- of indirection
            | otherwise                                      = "Unknown"

showNode _ _ (NAp a1 a2) = iConcat [ iStr "Ap ", showFWAddr a1,
                                     iStr " ",   showFWAddr a2 ]

showNode _ _ (NConstr tag dta) = iConcat [ iStr "NConstr ", iNum tag, iStr " [",
                                           iIndent $ iInterleave (iStr ",\n") (map showFWAddr dta),
                                           iStr "]" ]

showDump :: GmState -> Iseq
showDump s = iConcat [ iStr " Dump: [",
                       iIndent (iInterleave iNewline dumpItems),
                       iStr "]" ]
    where dumpItems = map showDumpItem (reverse (gmDump s))

showDumpItem :: GmDumpItem -> Iseq
showDumpItem (code, stack) = iConcat [ iStr "<",
                                       shortShowInstructions 3 code,
                                       iStr ", ",
                                       shortShowStack stack, iStr ">" ]

shortShowInstructions :: Int -> GmCode -> Iseq
shortShowInstructions n code = iConcat [ iStr "{",
                                         iInterleave (iStr "; ") dotcodes,
                                         iStr "}" ]
    where codes = map showInstruction (take n code)
          dotcodes | length code > n = codes ++ [ iStr "..." ]
                   | otherwise = codes

showHeap :: GmState -> Iseq
showHeap state = iInterleave iNewline (map formatter tuples)
    where formatter (addr, node) = iConcat [ showFWAddr addr,
                                             iStr " -> ",
                                             showNode state addr node ]

          heap   = gmHeap state
          tuples =  [ (addr, hLookup heap addr) | addr <- hAddresses heap ]

shortShowStack :: GmStack -> Iseq
shortShowStack stack = iConcat [ iStr "[",
                                 iInterleave (iStr ", ") (map showFWAddr stack),
                                 iStr "]" ]

showEnv :: GmGlobals -> Iseq
showEnv = iInterleave iNewline . map formatter
    where formatter (name, addr) = iConcat [ iStr name, iStr " -> ", showFWAddr addr ]

showOutput :: GmState -> Iseq
showOutput s = iConcat [ iStr "Output: ",
                          iInterleave (iStr ", ") (reverse $ map iNum (gmOutput s)) ]

showStats :: GmState -> Iseq
showStats s = iConcat [ iStr "Steps taken = ", iNum (statGetSteps (gmStats s)) ]
