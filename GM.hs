{-# OPTIONS_GHC -Wall #-}

module GM where

import AST
import Heap
import Iseq
import Utils
import Parser (parse)
import Main (preludeDefs)

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

data Instruction = Unwind
                 | PushGlobal Name
                 | PushInt Int
                 | Push Int
                 | MkAp
                 | Slide Int
                 deriving (Eq)

data GmState = GmState { gmCode    :: GmCode,     -- Current instruction stream
                         gmStack   :: GmStack,    -- Current stack
                         gmHeap    :: GmHeap,     -- Heap of nodes
                         gmGlobals :: GmGlobals,  -- Global addresses in heap
                         gmStats   :: GmStats     -- Statistics
                       }


statInitial :: GmStats
statInitial = 0

statIncSteps :: GmStats -> GmStats
statIncSteps s = s + 1

statGetSteps :: GmStats -> Int
statGetSteps s = s

runProg :: String -> String
runProg = showResults . eval . compile . parse

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

          dispatch (Push n)  = push n
          dispatch (Slide n) = slide n

          dispatch MkAp   = mkAp
          dispatch Unwind = unwind

pushGlobal :: Name -> GmState -> GmState
pushGlobal name state = state { gmStack = addr : (gmStack state) }
    where addr = aLookup (gmGlobals state) name (error ("Undeclared global " ++ name))

pushInt :: Int -> GmState -> GmState
pushInt n state = state { gmStack = addr : (gmStack state), gmHeap = heap' }
    where (heap', addr) = hAlloc (gmHeap state) (NNum n)

mkAp :: GmState -> GmState
mkAp state = state { gmStack = addr : rest, gmHeap = heap' }
    where (f:arg:rest)  = gmStack state
          (heap', addr) = hAlloc (gmHeap state) (NAp f arg)

push :: Int -> GmState -> GmState
push n state = state { gmStack = addr : stack }
    where stack        = gmStack state
          (NAp _ addr) = hLookup (gmHeap state) (stack !! (n + 1))

slide :: Int -> GmState -> GmState
slide n state = state { gmStack = addr : drop n rest }
    where (addr:rest) = gmStack state

unwind :: GmState -> GmState
unwind state = newState (hLookup (gmHeap state) addr)
    where (addr:rest) = gmStack state

          newState (NNum _)   = state
          newState (NAp a1 _) = state { gmCode = [ Unwind ], gmStack = a1:addr:rest }

          newState (NGlobal n code)
            | length rest < n = error "Unwinding with too few arguments"
            | otherwise       = state { gmCode = code }

compile :: CoreProgram -> GmState
compile program = GmState initialCode [] heap globals statInitial
    where scDefs = program ++ preludeDefs
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
compileR e env = compileC e env ++ [Slide (length env + 1), Unwind]

argOffset :: Int -> GmEnvironment -> GmEnvironment
argOffset n env = [(v, n+m) | (v,m) <- env]

compileC :: GmCompiler
compileC (EVar v) env
    | elem v (aDomain env) = [Push n]
    | otherwise = [PushGlobal v]
    where n = aLookup env v (error "Can’t happen")

compileC (ENum n) _      = [PushInt n]

compileC (EAp e1 e2) env = compileC e2 env ++ compileC e1 (argOffset 1 env) ++ [ MkAp ]

compileC (EConstr _ _) _ = error "EConstr: not yet implemented"
compileC (ELet _ _ _) _  = error "ELet: not yet implemented"
compileC (ECase _ _) _   = error "ECase: not yet implemented"
compileC (ELam _ _) _    = error "ELam: not yet implemented"

compiledPrimitives :: [GmCompiledSC]
compiledPrimitives = []

showResults :: [GmState] -> [Char]
showResults states = iDisplay (iConcat [
                                iStr "Supercombinator definitions", iNewline,
                                iInterleave iNewline (map (showSC s) (gmGlobals s)),
                                iNewline, iNewline,
                                iStr "State transitions",
                                iNewline, iNewline,
                                iLayn (map showState states),
                                iNewline, iNewline,
                                showStats (last states)
                            ])
    where (s:_) = states

showSC :: GmState -> (Name, Addr) -> Iseq
showSC s (name, addr) = iConcat [ iStr "Code for ",
                                  iStr name, iNewline,
                                  showInstructions code,
                                  iNewline, iNewline ]

    where (NGlobal _ code) = (hLookup (gmHeap s) addr)

showInstructions :: GmCode -> Iseq
showInstructions is = iConcat [ iStr " Code:{",
                                iIndent (iInterleave iNewline (map showInstruction is)),
                                iStr "}", iNewline ]
showInstruction :: Instruction -> Iseq
showInstruction Unwind  = iStr  "Unwind"
showInstruction MkAp    = iStr  "MkAp"

showInstruction (PushInt n)    = (iStr "PushInt ") `iAppend` (iNum n)
showInstruction (PushGlobal f) = (iStr "PushGlobal ") `iAppend` (iStr f)

showInstruction (Push n)  = (iStr "Push ")  `iAppend` (iNum n)
showInstruction (Slide n) = (iStr "Slide ") `iAppend` (iNum n)

showState :: GmState -> Iseq
showState s = iInterleave iNewline [ showStack s,
                                     showInstructions (gmCode s) ]

showStack :: GmState -> Iseq
showStack s = iConcat [ iStr " Stack:[",
                        iIndent (iInterleave iNewline stackItems),
                        iStr "]" ]

    where stackItems = (map (showStackItem s) (reverse (gmStack s)))

showStackItem :: GmState -> Addr -> Iseq
showStackItem s a = iConcat [ iStr (showaddr a),
                              iStr ": ",
                              showNode s a (hLookup (gmHeap s) a) ]

showNode :: GmState -> Addr -> Node -> Iseq
showNode _ _ (NNum n) = iNum n

showNode s a (NGlobal _ _) = iConcat [ iStr "Global ", iStr v ]
    where v = head [n | (n,b) <- gmGlobals s, a == b]

showNode _ _ (NAp a1 a2) = iConcat [ iStr "Ap ", iStr (showaddr a1),
                                     iStr " ",   iStr (showaddr a2) ]

showStats :: GmState -> Iseq
showStats s = iConcat [ iStr "Steps taken = ", iNum (statGetSteps (gmStats s))]
