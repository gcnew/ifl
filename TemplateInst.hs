{-# OPTIONS_GHC -Wall #-}

module TeamplateInst where

import AST
import Iseq
import Utils
import Parser (parse)
import Main (preludeDefs)

type TiStack = [Addr]
type TiHeap = Heap Node
type TiGlobals = ASSOC Name Addr

type TiState = (TiStack, TiDump, TiHeap, TiGlobals, TiStats)

data Node = NAp Addr Addr                    -- Application
          | NSupercomb Name [Name] CoreExpr  -- Supercombinator
          | NNum Int                         -- A number

data TiDump = DummyTiDump

initialTiDump :: TiDump
initialTiDump = DummyTiDump

type TiStats = Int

tiStatInitial :: TiStats
tiStatInitial = 0

tiStatIncSteps :: TiStats -> TiStats
tiStatIncSteps s = s + 1

tiStatGetSteps :: TiStats -> Int
tiStatGetSteps s = s

applyToStats :: (TiStats -> TiStats) -> TiState -> TiState
applyToStats statsFun (stack, dump, heap, scDefs, stats)
    = (stack, dump, heap, scDefs, statsFun stats)

showResults :: Bool -> [TiState] -> String
showResults withHeap states = iDisplay $ iConcat [ iLayn (map (showState withHeap) states),
                                                   showStats (last states) ]

showState :: Bool -> TiState -> Iseq
showState withHeap (stack, _, heap, _, _)
    = iConcat [ showStack heap stack, iNewline, heapSeq ]
    where heapSeq | withHeap  = showHeap heap `iAppend` iNewline
                  | otherwise = iNil

showHeap :: TiHeap -> Iseq
showHeap heap = iInterleave iNewline $ map formatter tuples
    where formatter (addr, node) = iConcat [ showFWAddr addr, iStr " -> ", showNode node ]
          tuples =  [ (addr, hLookup heap addr) | addr <- hAddresses heap ]

showStack :: TiHeap -> TiStack -> Iseq
showStack heap stack
    = iConcat [ iStr "Stk [",
                iIndent (iInterleave iNewline (map showStackItem stack)),
                iStr " ]" ]
    where showStackItem addr = iConcat [ showFWAddr addr, iStr ": ",
                showStkNode heap (hLookup heap addr) ]

showStkNode :: TiHeap -> Node -> Iseq
showStkNode heap (NAp funAddr argAddr)
    = iConcat [ iStr "NAp ", showFWAddr funAddr,
                iStr " ", showFWAddr argAddr, iStr " (",
                showNode (hLookup heap argAddr), iStr ")" ]
showStkNode _ node = showNode node

showNode :: Node -> Iseq
showNode (NAp a1 a2) = iConcat [ iStr "NAp ", showAddr a1,
                                 iStr " ", showAddr a2 ]

showNode (NSupercomb name _ _) = iStr ("NSupercomb " ++ name)
showNode (NNum n) = (iStr "NNum ") `iAppend` (iNum n)

showAddr :: Addr -> Iseq
showAddr addr = iStr (showaddr addr)

showFWAddr :: Addr -> Iseq -- Show address in field of width 4
showFWAddr addr = iStr (space (4 - length str) ++ str)
    where str = showaddr addr

showStats :: TiState -> Iseq
showStats (_, _, _, _, stats)
    = iConcat [ iNewline, iNewline, iStr "Total number of steps = ",
                iNum (tiStatGetSteps stats) ]

eval :: TiState -> [TiState]
eval state = state : restStates
    where restStates | tiFinal state = []
                     | otherwise     = eval nextState
          nextState = doAdmin (step state)

runProg :: String -> String
runProg = showResults False . eval . compile . parse

runDebugProg :: String -> String
runDebugProg = showResults True . eval . compile . parse

extraPreludeDefs :: CoreProgram
extraPreludeDefs = []

compile :: CoreProgram -> TiState
compile program = (initialStack, initialTiDump, initialHeap, globals, tiStatInitial)
    where scDefs = program ++ preludeDefs ++ extraPreludeDefs

          (initialHeap, globals) = buildInitialHeap scDefs

          initialStack = [ addressOfMain ]
          addressOfMain = aLookup globals "main" (error "main is not defined")

buildInitialHeap :: [CoreScDefn] -> (TiHeap, TiGlobals)
buildInitialHeap scDefs = mapAccuml allocateSc hInitial scDefs

allocateSc :: TiHeap -> CoreScDefn -> (TiHeap, (Name, Addr))
allocateSc heap (name, args, body) = (heap', (name, addr))
    where (heap', addr) = hAlloc heap (NSupercomb name args body)

doAdmin :: TiState -> TiState
doAdmin state = applyToStats tiStatIncSteps state

tiFinal :: TiState -> Bool
tiFinal ([soleAddr], _, heap, _, _)
    = isDataNode (hLookup heap soleAddr)

tiFinal ([], _, _, _, _) = error "Empty stack!"
tiFinal _                = False -- Stack contains more than one item

isDataNode :: Node -> Bool
isDataNode (NNum _) = True
isDataNode _        = False

step :: TiState -> TiState
step state = dispatch (hLookup heap (head stack))
    where (stack, _, heap, _, _) = state

          dispatch (NNum n)    = numStep state n
          dispatch (NAp a1 a2) = apStep state a1 a2
          dispatch (NSupercomb sc args body) = scStep state sc args body

numStep :: TiState -> Int -> TiState
numStep _ _ = error "Number applied as a function!"

apStep :: TiState -> Addr -> Addr -> TiState
apStep (stack, dump, heap, globals, stats) a1 _a2 = (a1 : stack, dump, heap, globals, stats)

scStep :: TiState -> Name -> [Name] -> CoreExpr -> TiState
scStep (stack, dump, heap, globals, stats) _ argNames body
    | length stack < length argNames + 1 = error $ "Insufficient number of arguments"
    | otherwise                          = (newStack, dump, newHeap, globals, stats)

    where newStack = resultAddr : (drop (length argNames + 1) stack)
          (newHeap, resultAddr) = instantiate body heap env
          env = argBindings ++ globals
          argBindings = zip argNames (getargs heap stack)

getargs :: TiHeap -> TiStack -> [Addr]
getargs heap stack = map getarg (tail stack) -- skip the supercombinator
    where getarg addr = let (NAp _ arg) = hLookup heap addr
                         in arg

instantiate :: CoreExpr             -- Body of supercombinator
                -> TiHeap           -- Heap before instantiation
                -> ASSOC Name Addr  -- Association of names to addresses
                -> (TiHeap, Addr)   -- Heap after instantiation, and
                                    -- address of root of instance

instantiate (ENum n) heap _ = hAlloc heap (NNum n)

instantiate (EAp e1 e2) heap env = hAlloc heap2 (NAp a1 a2)
    where (heap1, a1) = instantiate e1 heap env
          (heap2, a2) = instantiate e2 heap1 env

instantiate (EVar v) heap env = (heap, aLookup env v err)
    where err = error ("Undefined name " ++ show v)

instantiate (ELet isRec defs body) heap env = instantiate body newHeap newEnv
    where allocDef (curHeap, curEnv) (name, expr) = let env' | isRec     = newEnv -- bind to final env
                                                             | otherwise = curEnv -- bind to current env
                                                        (heap', addr) = instantiate expr curHeap env'
                                                     in (heap', (name, addr) : curEnv)
          (newHeap, newEnv) = foldl allocDef (heap, env) defs

instantiate (EConstr _tag _arity) _heap _env = error "Can't instantiate constructors yet"

instantiate (ECase _ _) _ _ = error "Can't instantiate case exprs"
instantiate (ELam _args _body) _heap _env
    = error "Can't instantiate lambda (should be converted to supercombinator)"
