{-# OPTIONS_GHC -Wall #-}

module TeamplateInst where

import AST
import Heap
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
          | NInd Addr                        -- Indirection

data ShowStateOptions = ShowStateOptions { ssHeap :: Bool
                                         , ssEnv  :: Bool
                                         }

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

showResults :: ShowStateOptions -> [TiState] -> String
showResults opts states = iDisplay $ iConcat [ iLayn (map (showState opts) states),
                                               showStats (last states) ]

showState :: ShowStateOptions -> TiState -> Iseq
showState opts (stack, _, heap, env, _)
    = iConcat [ showStack heap stack, iNewline, extra ]
    where heapLines | ssHeap opts = showHeap heap
                    | otherwise   = []

          envLines  | ssEnv opts  = showEnv env
                    | otherwise   = []

          extra | null views = iNil
                | otherwise  = iSplitView views `iAppend` iNewline
                where views = filter (not . null) [ heapLines, envLines ]

showHeap :: TiHeap -> [Iseq]
showHeap heap = map formatter tuples
    where formatter (addr, node) = iConcat [ showFWAddr addr, iStr " -> ", showNode node ]
          tuples =  [ (addr, hLookup heap addr) | addr <- hAddresses heap ]

showEnv :: TiGlobals -> [Iseq]
showEnv env = map formatter env
    where formatter (name, addr) = iConcat [ iStr name, iStr " -> ", showFWAddr addr ]

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
showNode (NInd a) = iStr "NInd " `iAppend` showAddr a

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
runProg = showResults (ShowStateOptions False False) . eval . compile . parse

runDebugProg :: ShowStateOptions -> String -> String
runDebugProg opts = showResults opts . eval . compile . parse

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
          dispatch (NInd addr) = indStep state addr
          dispatch (NAp a1 a2) = apStep state a1 a2
          dispatch (NSupercomb sc args body) = scStep state sc args body

numStep :: TiState -> Int -> TiState
numStep _ _ = error "Number applied as a function!"

indStep :: TiState -> Addr -> TiState
indStep (_:stack, dump, heap, globals, stats) addr = (addr:stack, dump, heap, globals, stats)
indStep _ _ = error "Spine stack should have indirection address on top."

apStep :: TiState -> Addr -> Addr -> TiState
apStep (stack, dump, heap, globals, stats) a1 _a2 = (a1 : stack, dump, heap, globals, stats)

scStep :: TiState -> Name -> [Name] -> CoreExpr -> TiState
scStep (stack, dump, heap, globals, stats) _ argNames body
    | length stack < length argNames + 1 = error $ "Insufficient number of arguments"
    | otherwise                          = (newStack, dump, newHeap, globals, stats)

    where newStack@(rdxRoot:_) = drop (length argNames) stack
          newHeap = instantiateAndUpdate body rdxRoot heap env
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

instantiateAndUpdate :: CoreExpr            -- Body of supercombinator
                        -> Addr
                        -> TiHeap           -- Heap before instantiation
                        -> ASSOC Name Addr  -- Association of names to addresses
                        -> TiHeap           -- Heap after instantiation

instantiateAndUpdate (ENum n) updAddr heap _ = hUpdate heap updAddr (NNum n)

instantiateAndUpdate (EAp e1 e2) updAddr heap env = hUpdate heap2 updAddr (NAp a1 a2)
    where (heap1, a1) = instantiate e1 heap env
          (heap2, a2) = instantiate e2 heap1 env

instantiateAndUpdate (EVar v) updAddr heap env = hUpdate heap updAddr (NInd $ aLookup env v err)
    where err = error ("Undefined name " ++ show v)

instantiateAndUpdate (ELet isRec defs body) updAddr heap env = instantiateAndUpdate body updAddr newHeap newEnv
    where allocDef (curHeap, curEnv) (name, expr) = let env' | isRec     = newEnv -- bind to final env
                                                             | otherwise = curEnv -- bind to current env
                                                        (heap', addr) = instantiate expr curHeap env'
                                                     in (heap', (name, addr) : curEnv)
          (newHeap, newEnv) = foldl allocDef (heap, env) defs

instantiateAndUpdate (EConstr _tag _arity) _updAddr _heap _env = error "Can't instantiate constructors yet"

instantiateAndUpdate (ECase _ _) _ _ _ = error "Can't instantiate case exprs"
instantiateAndUpdate (ELam _ _) _ _ _
    = error "Can't instantiate lambda (should be converted to supercombinator)"
