{-# OPTIONS_GHC -Wall #-}

module TeamplateInst where

import AST
import Heap
import Iseq
import Utils
import Parser (parse)
import Main (preludeDefs, extraPreludeDefs)

type TiStack = [Addr]
type TiHeap = Heap Node
type TiGlobals = ASSOC Name Addr

type TiState = (TiStack, TiDump, TiHeap, TiGlobals, TiStats)

data Primitive = Neg | Add | Sub | Mul | Div
               | Greater | GreaterEq | Less | LessEq | Eq | NotEq
               | If
               | PrimConstr Int Int


data Node = NAp Addr Addr                    -- Application
          | NSupercomb Name [Name] CoreExpr  -- Supercombinator
          | NNum Int                         -- A number
          | NInd Addr                        -- Indirection
          | NPrim Name Primitive             -- Primitive
          | NData Int [Addr]                 -- Tag, list of components

data ShowStateOptions = ShowStateOptions { ssHeap :: Bool
                                         , ssEnv  :: Bool
                                         , ssDump :: Bool
                                         }

dbgOpts :: ShowStateOptions
dbgOpts = ShowStateOptions True True True

compactOpts :: ShowStateOptions
compactOpts = ShowStateOptions False False False

type TiDump = [TiStack]

primitives :: ASSOC Name Primitive
primitives = [ ("negate", Neg),

               ("+", Add), ("-", Sub),
               ("*", Mul), ("/", Div),

               (">", Greater), (">=", GreaterEq),
               ("<", Less),    ("<=", LessEq),
               ("==", Eq),     ("/=", NotEq),

               ("if", If) ]

initialTiDump :: TiDump
initialTiDump = []

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
showState opts (stack, dump, heap, env, _)
    = iConcat [ showStack heap stack, iNewline, extra ]
    where heapLines | ssHeap opts = showHeap heap
                    | otherwise   = iNil

          envLines  | ssEnv opts  = showEnv env
                    | otherwise   = iNil

          dumpLines | ssDump opts = showDump heap dump
                    | otherwise   = iNil

          extra | null views = iNil
                | otherwise  = iSplitView views `iAppend` iNewline
                where views = filter (not . isNil) [ heapLines, envLines, dumpLines ]

                      isNil INil = True
                      isNil _    = False

showHeap :: TiHeap -> Iseq
showHeap heap = iInterleave iNewline (map formatter tuples)
    where formatter (addr, node) = iConcat [ showFWAddr addr, iStr " -> ", showNode node ]
          tuples =  [ (addr, hLookup heap addr) | addr <- hAddresses heap ]

showDump :: TiHeap -> TiDump -> Iseq
showDump heap = iInterleave iNewline . map (showStack heap)

showEnv :: TiGlobals -> Iseq
showEnv = iInterleave iNewline . map formatter
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

showNode (NData tag addrs)     = iConcat [ iStr "NData ", iNum tag, iStr " [",
                                           iInterleave (iStr ", ") $ map showAddr addrs,
                                           iStr "]" ]

showNode (NPrim name _)        = iStr ("NPrim " ++ name)
showNode (NSupercomb name _ _) = iStr ("NSupercomb " ++ name)

showNode (NNum n)       = iStr "NNum "  `iAppend` iNum n
showNode (NInd a)       = iStr "NInd "  `iAppend` showAddr a

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
runProg = showResults compactOpts . eval . compile . parse

runDebugProg :: String -> String
runDebugProg = showResults dbgOpts . eval . compile . parse

compile :: CoreProgram -> TiState
compile program = (initialStack, initialTiDump, initialHeap, globals, tiStatInitial)
    where scDefs = program ++ preludeDefs ++ extraPreludeDefs

          (initialHeap, globals) = buildInitialHeap scDefs

          initialStack = [ addressOfMain ]
          addressOfMain = aLookup globals "main" (error "main is not defined")

buildInitialHeap :: [CoreScDefn] -> (TiHeap, TiGlobals)
buildInitialHeap scDefs = (heap2, scAddrs ++ primAddrs)
    where (heap1, scAddrs)   = mapAccuml allocateSc hInitial scDefs
          (heap2, primAddrs) = mapAccuml allocatePrim heap1 primitives

allocateSc :: TiHeap -> CoreScDefn -> (TiHeap, (Name, Addr))
allocateSc heap (name, args, body) = (heap', (name, addr))
    where (heap', addr) = hAlloc heap (NSupercomb name args body)

allocatePrim :: TiHeap -> (Name, Primitive) -> (TiHeap, (Name, Addr))
allocatePrim heap (name, prim) = (heap', (name, addr))
    where (heap', addr) = hAlloc heap (NPrim name prim)

doAdmin :: TiState -> TiState
doAdmin state = applyToStats tiStatIncSteps state

-- Debug version
--doAdmin state = abortIfSteps 100 . wprint $ applyToStats tiStatIncSteps state
--    where wprint st@(_, _, _, _, steps) = trace info st
--              where info = iDisplay $ iConcat [ iNum steps, iStr ") ",
--                                                iIndent $ showState dbgOpts st ]

--          abortIfSteps n st@(_, dump, heap, globals, v)
--              | n == v    = ([], dump, heap, globals, v)
--              | otherwise = st

tiFinal :: TiState -> Bool
tiFinal ([soleAddr], [], heap, _, _)
    = isDataNode (hLookup heap soleAddr)

tiFinal ([], _, _, _, _) = error "Empty stack!"
tiFinal _                = False -- Stack contains more than one item

isDataNode :: Node -> Bool
isDataNode (NNum _)    = True
isDataNode (NData _ _) = True
isDataNode _           = False

step :: TiState -> TiState
step state = dispatch (hLookup heap (head stack))
    where (stack, _, heap, _, _) = state

          dispatch d@(NData _ _) = dataStep state d

          dispatch (NNum n)      = numStep state n
          dispatch (NInd addr)   = indStep state addr
          dispatch (NAp a1 a2)   = apStep state a1 a2

          dispatch (NPrim _ prim) = primStep state prim
          dispatch (NSupercomb sc args body) = scStep state sc args body

-- Number:
--    a:[]   s:d   h[ a: NNum n ]   f
-- ->    s     d   h                f

numStep :: TiState -> Int -> TiState
numStep ([_], prevStack:dump', heap, globals, stats) _
    = (prevStack, dump', heap, globals, stats)

numStep _ _ = error "Number applied as a function!"

dataStep :: TiState -> Node -> TiState
dataStep ([_], prevStack:dump', heap, globals, stats) _
    = (prevStack, dump', heap, globals, stats)

dataStep _ _ = error "Data applied as a function!"

-- Indirection:
--     a:s   d   h[ a: NInd a1 ]   f
-- -> a1:s   d   h                 f

indStep :: TiState -> Addr -> TiState
indStep (_:stack, dump, heap, globals, stats) addr = (addr:stack, dump, heap, globals, stats)
indStep _ _ = error "Spine stack should have indirection address on top."

-- Application:
--    a:s   d   h┌ a:  NAp a1 a2 ┐   f
--               └ a2: NInd a3   ┘
-- -> a:s   d   h[ a:  NAp a1 a3 ]   f

--       a:s   d   h[ a:  NAp a1 a2 ]   f
-- -> a1:a:s   d   h                    f

apStep :: TiState -> Addr -> Addr -> TiState
apStep (stack, dump, heap, globals, stats) a1 a2
    | (NInd a3) <- hLookup heap a2 = let a = head stack;
                                         heap' = hUpdate heap a (NAp a1 a3)
                                      in (a1:stack, dump, heap', globals, stats)

    | otherwise                    = (a1:stack, dump, heap, globals, stats)


primStep :: TiState -> Primitive -> TiState

primStep stack Neg = negStep stack

primStep stack Add = primArith stack (+)
primStep stack Sub = primArith stack (-)
primStep stack Mul = primArith stack (*)
primStep stack Div = primArith stack div

primStep stack Greater   = primComp stack (>)
primStep stack GreaterEq = primComp stack (>=)
primStep stack Less      = primComp stack (<)
primStep stack LessEq    = primComp stack (<=)
primStep stack Eq        = primComp stack (==)
primStep stack NotEq     = primComp stack (/=)

primStep stack If          = primIf stack
primStep stack (PrimConstr tag arity) = primConstr stack tag arity

-- Negate:
--    a:a1:[]   d   h┌ a:  NPrim Neg ┐   f
--                   │ a1: NAp a b   │
--                   └ b:  Num n     ┘
-- ->   a1:[]   d   h[ a1: Neg n     ]   f

--    a:a1:[]           d   h┌ a:  NPrim _  ┐   f
--                           └ a1: NAp a b  ┘
-- ->    b:[]   (a1:[]):d   h                   f

negStep :: TiState -> TiState
negStep ([_, a1], dump, heap, globals, stats)
    | (NNum n) <- bNode = let heap' = hUpdate heap a1 (NNum (negate n))
                           in ([a1], dump, heap', globals, stats)

    | not (isDataNode bNode) = ([b], [a1]:dump, heap, globals, stats)
    | otherwise              = error "Negate called with non-number argument"

    where (NAp _ b) = hLookup heap a1
          bNode     = hLookup heap b

negStep _ = error "Negate: invalid arguments count"

primDyadic :: TiState -> (Node -> Node -> Node) -> TiState
primDyadic ([_, a1, a2], dump, heap, globals, stats) op
    | not (isDataNode b1Node) = ([b1], [a1, a2]:dump, heap, globals, stats)
    | not (isDataNode b2Node) = ([b2],     [a2]:dump, heap, globals, stats)

    | otherwise               = let heap' = hUpdate heap a2 (b1Node `op` b2Node)
                                 in ([a2], dump, heap', globals, stats)

    where (NAp _ b1) = hLookup heap a1
          b1Node     = hLookup heap b1

          (NAp _ b2) = hLookup heap a2
          b2Node     = hLookup heap b2

primDyadic _ _ = error "Dyadic func: invalid arguments count"

primArith :: TiState -> (Int -> Int -> Int) -> TiState
primArith state op = primDyadic state liftedOp
    where liftedOp (NNum n1) (NNum n2) = NNum (n1 `op` n2)
          liftedOp _ _  = error "Dyadic arith called with non-number argument"

primComp :: TiState -> (Int -> Int -> Bool) -> TiState
primComp state@(_, _, _, globals, _) op = primDyadic state liftedOp
    where cmp x y
              | x `op` y  = findPrimDef "True"
              | otherwise = findPrimDef "False"

          findPrimDef prim = NInd (aLookup globals prim err)
              where err = error $ "Primitive definition `" ++ prim ++ "` not found!"

          -- todo: compare NData..
          liftedOp (NNum x) (NNum y) = x `cmp` y
          liftedOp _ _  = error "Compare called with non-data argument"

coreIsTrue :: Node -> Bool
coreIsTrue (NData 2 []) = True
coreIsTrue (NData 1 []) = False
coreIsTrue _            = error "Not a boolean"

primIf :: TiState -> TiState
primIf (stack, dump, heap, globals, stats)
    | length stack < 4       = error "Primitive If: invalid arguments count"

    | not (isDataNode nCond) = let stack' = tail stack; -- reevaluate cond (takes care for NInd)
                                in ([aCond], stack':dump, heap, globals, stats)

    | otherwise              = let stack' = drop 3 stack;
                                   root   = head stack';

                                   aRes | coreIsTrue nCond = args !! 1
                                        | otherwise        = args !! 2

                                   heap' = hUpdate heap root $ NInd aRes

                                in (stack', dump, heap', globals, stats)

    where args  = getargs heap stack
          aCond = head args
          nCond = hLookup heap aCond

primConstr :: TiState -> Int -> Int -> TiState
primConstr (stack, dump, heap, globals, stats) tag arity
    | length stack /= arity + 1= error "Primitive Constr: invalid arguments count"
    | otherwise  = ([root], dump, heap', globals, stats)

    where root = last stack
          heap' = hUpdate heap root $ NData tag (getargs heap stack)

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

instantiate (EConstr tag arity) heap _ = hAlloc heap $ NPrim "Constr" (PrimConstr tag arity)

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

instantiateAndUpdate (EConstr tag arity) updAddr heap _
    = hUpdate heap updAddr $ NPrim "Constr" (PrimConstr tag arity)

instantiateAndUpdate (ECase _ _) _ _ _ = error "Can't instantiate case exprs"
instantiateAndUpdate (ELam _ _) _ _ _
    = error "Can't instantiate lambda (should be converted to supercombinator)"
