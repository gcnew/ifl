{-# OPTIONS_GHC -Wall #-}

module TeamplateInst where

import AST
import Heap
import Iseq
import Utils
import Parser (parse)
import Main (preludeDefs, extraPreludeDefs)

type TiOut = [Int]
type TiDump = [Int]
type TiStack = [Addr]
type TiHeap = Heap Node
type TiStats = (Int, Int)
type TiGlobals = ASSOC Name Addr

type TiState = (TiStack, TiDump, TiHeap, TiGlobals, TiOut, TiStats)

type Primitive = TiState -> TiState

data Node = NAp Addr Addr                    -- Application
          | NSupercomb Name [Name] CoreExpr  -- Supercombinator
          | NNum Int                         -- A number
          | NInd Addr                        -- Indirection
          | NPrim Name Primitive             -- Primitive
          | NData Int [Addr]                 -- Tag, list of components
          | NMarked MarkState Node           -- Marked node

data MarkState = Done       -- Mark node as finised
               | Visit Int  -- Node visited n times so far

data ShowStateOptions = ShowStateOptions { ssHeap     :: Bool
                                         , ssEnv      :: Bool
                                         , ssDump     :: Bool
                                         , ssLastOnly :: Bool
                                         }

dbgOpts :: ShowStateOptions
dbgOpts = ShowStateOptions True True True False

compactOpts :: ShowStateOptions
compactOpts = ShowStateOptions False False False True

primitives :: ASSOC Name Primitive

primitives = [ ("negate", negStep),

               ("+", primArith (+)), ("-", primArith (-)),
               ("*", primArith (*)), ("/", primArith div),

               (">", primComp (>)),   (">=", primComp (>=)),
               ("<", primComp (<)),   ("<=", primComp (<=)),
               ("==", primComp (==)), ("/=", primComp (/=)),

               ("if", primIf),     ("abort", primAbort),
               ("print", primPrint),

               ("casePair", primCasePair),
               ("caseList", primCaseList) ]

initialTiDump :: TiDump
initialTiDump = []

tiStatInitial :: TiStats
tiStatInitial = (0, 0)

tiStatIncSteps :: TiStats -> TiStats
tiStatIncSteps (s, gcs) = (s + 1, gcs)

tiStatGetSteps :: TiStats -> Int
tiStatGetSteps (s, _) = s

tiStatIncGC :: TiStats -> TiStats
tiStatIncGC (s, gcs) = (s, gcs + 1)

tiStatGetGC :: TiStats -> Int
tiStatGetGC (_, gcs) = gcs

applyToStats :: (TiStats -> TiStats) -> TiState -> TiState
applyToStats statsFun (stack, dump, heap, scDefs, out, stats)
    = (stack, dump, heap, scDefs, out, statsFun stats)

showResults :: ShowStateOptions -> [TiState] -> String
showResults opts states = iDisplay $ iConcat [ stateOutp,
                                               showOutput lastState,
                                               showStats lastState ]
    where lastState = last states
          stateOutp | ssLastOnly opts = showState dbgOpts lastState `iAppend` iNewline
                    | otherwise       = iLayn (map (showState opts) states)

showState :: ShowStateOptions -> TiState -> Iseq
showState opts (stack, dump, heap, env, _, _)
    = iConcat [ showHeapSize heap, iNewline,
                showStack heap stack, iNewline, extra ]

    where heapLines | ssHeap opts = showHeap heap
                    | otherwise   = iNil

          envLines  | ssEnv opts  = showEnv env
                    | otherwise   = iNil

          dumpLines | ssDump opts = showDump heap stack dump
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

showHeapSize :: TiHeap -> Iseq
showHeapSize heap = iStr "Heap size: " `iAppend` iNum (hSize heap)

showDump :: TiHeap -> TiStack -> TiDump -> Iseq
showDump heap stack = iInterleave iNewline . map (showStack heap) . getStacks stack

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

showNode (NNum n)       = iStr "NNum " `iAppend` iNum n
showNode (NInd a)       = iStr "NInd " `iAppend` showAddr a

showNode (NMarked Done n)      = iStr "NMarked Done " `iAppend` showNode n
showNode (NMarked (Visit x) n) = iConcat [ iStr "NMarked (Visit ", iNum x, iStr ") ", showNode n ]

showAddr :: Addr -> Iseq
showAddr addr = iStr (showaddr addr)

showFWAddr :: Addr -> Iseq -- Show address in field of width 4
showFWAddr addr = iStr (space (4 - length str) ++ str)
    where str = showaddr addr

showOutput :: TiState -> Iseq
showOutput (_, _, _, _, out, _) = iConcat [ iStr "Output: ",
                                            iInterleave (iStr ", ") (reverse $ map iNum out) ]

showStats :: TiState -> Iseq
showStats (_, _, _, _, _, stats)
    = iConcat [ iNewline, iNewline,
                iStr "Steps: ", iNum (tiStatGetSteps stats),
                iStr ", GC Count: ", iNum (tiStatGetGC stats) ]

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
compile program = (initialStack, initialTiDump, initialHeap, globals, [], tiStatInitial)
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
doAdmin state = runGC . applyToStats tiStatIncSteps $ state

runGC :: TiState -> TiState
runGC state@(_, _, heap, _, _, _)
    | hSize heap > 100  = applyToStats tiStatIncGC $ gc state
    | otherwise         = state

-- Debug version
--doAdmin state = abortIfSteps 100 . wprint $ applyToStats tiStatIncSteps state
--    where wprint st@(_, _, _, _, steps) = trace info st
--              where info = iDisplay $ iConcat [ iNum steps, iStr ") ",
--                                                iIndent $ showState dbgOpts st ]

--          abortIfSteps n st@(_, dump, heap, globals, v)
--              | n == v    = ([], dump, heap, globals, v)
--              | otherwise = st

tiFinal :: TiState -> Bool
tiFinal ([soleAddr], [], heap, _, _, _)
    = isDataNode (hLookup heap soleAddr)

tiFinal ([], _, _, _, _, _) = error "Empty stack!"
tiFinal _                   = False -- Stack contains more than one item

isDataNode :: Node -> Bool
isDataNode (NNum _)    = True
isDataNode (NData _ _) = True
isDataNode _           = False

step :: TiState -> TiState
step state = dispatch (hLookup heap (head stack))
    where (stack, _, heap, _, _, _) = state

          dispatch (NMarked _ _) = error "Assert: Unexpected NMarked in step"

          dispatch n@(NNum _)    = dataStep state n
          dispatch d@(NData _ _) = dataStep state d

          dispatch (NInd addr)   = indStep state addr
          dispatch (NAp a1 a2)   = apStep state a1 a2

          dispatch (NPrim _ prim) = prim state
          dispatch (NSupercomb sc args body) = scStep state sc args body

-- Number|Data:
--    a:[]   s:d   h[ a: NNum n ]   f
-- ->    s     d   h                f

dataStep :: TiState -> Node -> TiState
dataStep (stack, offset:dump', heap, globals, out, stats) _
    | length stack - offset /= 1  = error "Assert: unexpected stack offset"
    | otherwise                   = (tail stack, dump', heap, globals, out, stats)

dataStep _ _ = error "Data applied as a function!"

-- Indirection:
--     a:s   d   h[ a: NInd a1 ]   f
-- -> a1:s   d   h                 f

indStep :: TiState -> Addr -> TiState
indStep (_:stack, dump, heap, globals, out, stats) addr
    = (addr:stack, dump, heap, globals, out, stats)

indStep _ _ = error "Spine stack should have indirection address on top."

-- Application:
--    a:s   d   h┌ a:  NAp a1 a2 ┐   f
--               └ a2: NInd a3   ┘
-- -> a:s   d   h[ a:  NAp a1 a3 ]   f

--       a:s   d   h[ a:  NAp a1 a2 ]   f
-- -> a1:a:s   d   h                    f

apStep :: TiState -> Addr -> Addr -> TiState
apStep (stack, dump, heap, globals, out, stats) a1 a2
    | (NInd a3) <- hLookup heap a2 = let a = head stack;
                                         heap' = hUpdate heap a (NAp a1 a3)
                                      in (a1:stack, dump, heap', globals, out, stats)

    | otherwise                    = (a1:stack, dump, heap, globals, out, stats)

-- Negate:
--    a:a1:[]   d   h┌ a:  NPrim Neg ┐   f
--                   │ a1: NAp a b   │
--                   └ b:  Num n     ┘
-- ->   a1:[]   d   h[ a1: Neg n     ]   f

--    a:a1:[]           d   h┌ a:  NPrim _  ┐   f
--                           └ a1: NAp a b  ┘
-- ->    b:[]   (a1:[]):d   h                   f

negStep :: TiState -> TiState
negStep (stack, dump, heap, globals, out, stats)
    | length args /= 1       = error "Primitive Negate: invalid arguments count"

    | not (isDataNode bNode) = let (stack', dump') = newStack stack dump 1 [b]
                                in (stack', dump', heap, globals, out, stats)

    | (NNum n) <- bNode      = let (stack', heap') = pruneStack stack heap 1 (NNum (negate n))
                                in (stack', dump, heap', globals, out, stats)

    | otherwise              = error "Primitive Negate: non-number argument"

    where args  = getargs heap stack dump
          (b:_) = args
          bNode = hLookup heap b

primAbort :: TiState -> TiState
primAbort _ = error "Core: abort"

primDyadic :: TiState -> (Node -> Node -> Node) -> TiState
primDyadic (stack, dump, heap, globals, out, stats) op
    | length args < 2      = error "Primitive Dyadic: invalid arguments count"

    | not (isDataNode nA1) = let (stack', dump') = newStack stack dump 1 [aA1]
                              in (stack', dump', heap, globals, out, stats)

    | not (isDataNode nA2) = let (stack', dump') = newStack stack dump 2 [aA2]
                              in (stack', dump', heap, globals, out, stats)

    | otherwise            = let (stack', heap') = pruneStack stack heap 2 (nA1 `op` nA2)
                              in (stack', dump, heap', globals, out, stats)

    where args        = getargs heap stack dump
          (aA1:aA2:_) = args
          (nA1:nA2:_) = map (hLookup heap) args

primArith :: (Int -> Int -> Int) -> TiState -> TiState
primArith op state = primDyadic state liftedOp
    where liftedOp (NNum n1) (NNum n2) = NNum (n1 `op` n2)
          liftedOp _ _  = error "Dyadic arith called with non-number argument"

primComp :: (Int -> Int -> Bool) -> TiState -> TiState
primComp op state@(_, _, _, globals, _, _) = primDyadic state liftedOp
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
primIf (stack, dump, heap, globals, out, stats)
    | length args < 3        = error "Primitive If: invalid arguments count"

    | not (isDataNode nCond) = let (stack', dump') = newStack stack dump 1 [aCond]
                                in (stack', dump', heap, globals, out, stats)

    | otherwise              = let aRes | coreIsTrue nCond = aT
                                        | otherwise        = aF

                                   (stack', heap') = pruneStack stack heap 3 (NInd aRes)
                                in (stack', dump, heap', globals, out, stats)

    where args            = getargs heap stack dump
          (aCond:aT:aF:_) = args
          nCond           = hLookup heap aCond

primPrint :: TiState -> TiState
primPrint (stack, dump, heap, globals, out, stats)
    | length args < 2       = error "Primitive Print: invalid arguments count"

    | not (isDataNode nVal) = let (stack', dump') = newStack stack dump 1 [aVal]
                               in (stack', dump', heap, globals, out, stats)

    | otherwise             = let (NNum val)      = nVal
                                  (stack', heap') = pruneStack stack heap 2 (NInd aRes)
                               in (stack', dump, heap', globals, val:out, stats)

    where args          = getargs heap stack dump
          (aVal:aRes:_) = args
          nVal          = hLookup heap aVal

primCasePair :: TiState -> TiState
primCasePair (stack, dump, heap, globals, out, stats)
    | length args < 2        = error "Primitive CasePair: invalid arguments count"

    | not (isDataNode nPair) = let (stack', dump') = newStack stack dump 1 [aPair]
                                in (stack', dump', heap, globals, out, stats)

    | otherwise              = let NData 1 [left, right] = nPair
                                   (heap', leftAp)  = hAlloc heap (NAp aF left)
                                   (stack', heap'') = pruneStack stack heap' 2 (NAp leftAp right)
                                in (stack', dump, heap'', globals, out, stats)

    where args         = getargs heap stack dump
          (aPair:aF:_) = args
          nPair        = hLookup heap aPair

primCaseList :: TiState -> TiState
primCaseList (stack, dump, heap, globals, out, stats)
    | length args < 3        = error "Primitive CaseList: invalid arguments count"

    | not (isDataNode nList) = let (stack', dump') = newStack stack dump 1 [aList]
                                in (stack', dump', heap, globals, out, stats)

    | otherwise              = let NData tag dta = nList;
                                   (heap', node)
                                        | tag == 1  = (heap, NInd aCn)
                                        | tag == 2, [hd, tl] <- dta
                                            = let (hp, hdAp) = hAlloc heap (NAp aCc hd)
                                               in (hp, NAp hdAp tl)
                                        | otherwise = error "Error matching list: not a list"

                                   (stack', heap'') = pruneStack stack heap' 3 node
                                in (stack', dump, heap'', globals, out, stats)

    where args              = getargs heap stack dump
          (aList:aCn:aCc:_) = args
          nList             = hLookup heap aList


primConstr :: Int -> Int -> TiState -> TiState
primConstr tag arity (stack, dump, heap, globals, out, stats)
    | length args /= arity = error "Primitive Constr: invalid arguments count"
    | otherwise            = (stack', dump, heap', globals, out, stats)

    where args = getargs heap stack dump
          stack' = drop arity stack
          root = head stack'
          heap' = hUpdate heap root $ NData tag args

scStep :: TiState -> Name -> [Name] -> CoreExpr -> TiState
scStep (stack, dump, heap, globals, out, stats) _ argNames body
    | length args < length argNames = error "Insufficient number of arguments"
    | otherwise                     = (stack', dump, heap', globals, out, stats)

    where stack' = drop (length argNames) stack
          root = head stack'
          heap' = instantiateAndUpdate body root heap env
          env = argBindings ++ globals
          args = getargs heap stack dump
          argBindings = zip argNames args

getargs :: TiHeap -> TiStack -> TiDump -> [Addr]
getargs heap stack dump = map getarg (tail topStack) -- skip the supercombinator
    where topStack = head (getStacks stack dump)

          getarg addr = let (NAp _ arg) = hLookup heap addr
                         in arg

getStacks :: TiStack -> TiDump -> [TiStack]
getStacks stack dump = splitStacks stack (length stack:dump)
    where splitStacks s [_]       = [s]
          splitStacks s (x:y:rst) = (take (x - y) s) : (splitStacks (drop (x - y) s) (y:rst))
          splitStacks _ _         = error "Assert: never"

newStack :: TiStack -> TiDump -> Int -> [Addr] -> (TiStack, TiDump)
newStack stack dump pruneCount toBeStack = (toBeStack ++ pruned, (length pruned):dump)
    where pruned = drop pruneCount stack

pruneStack :: TiStack -> TiHeap -> Int -> Node -> (TiStack, TiHeap)
pruneStack stack heap dropCount node = (pruned, hUpdate heap root node)
    where pruned@(root:_) = drop dropCount stack

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

instantiate (EConstr tag arity) heap _ = hAlloc heap $ NPrim "Constr" (primConstr tag arity)

instantiate (ECase _ _) _ _ = error "Can't instantiate case exprs"
instantiate (ELam _args _body) _heap _env
    = error "Can't instantiate lambda (should be converted to supercombinator)"

instantiateAndUpdate :: CoreExpr            -- Body of supercombinator
                        -> Addr             -- Address of root
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
    = hUpdate heap updAddr $ NPrim "Constr" (primConstr tag arity)

instantiateAndUpdate (ECase _ _) _ _ _ = error "Can't instantiate case exprs"
instantiateAndUpdate (ELam _ _) _ _ _
    = error "Can't instantiate lambda (should be converted to supercombinator)"

gc :: TiState -> TiState
gc (stack, dump, heap, globals, out, stats) = (stack', dump, heap''', globals', out, stats)
    where (heap', stack')    = markStackRoots heap stack
          (heap'', globals') = markGlobalRoots heap' globals
          heap'''            = scanHeap heap''

markStackRoots :: TiHeap -> TiStack -> (TiHeap, TiStack)
markStackRoots = mapAccuml markFrom

markGlobalRoots :: TiHeap -> TiGlobals -> (TiHeap, TiGlobals)
markGlobalRoots = mapAccuml mapf
    where mapf heap (name, addr) = let (heap', addr') = markFrom heap addr
                                    in (heap', (name, addr'))

markFrom :: TiHeap -> Addr -> (TiHeap, Addr)
markFrom heap addr = markNode addr hNull heap

markNode :: Addr -> Addr -> TiHeap -> (TiHeap, Addr)
markNode addr back heap = case node of
        (NMarked Done _)
            | hIsNull back
                -> (heap, addr)

        (NMarked _ _)
            | (NMarked (Visit 1) (NAp b' addr2)) <- hLookup heap back
                -> markNode addr2 back $ hUpdate heap back (NMarked (Visit 2) (NAp addr b'))

            | (NMarked (Visit 2) (NAp addr1 b')) <- hLookup heap back
                -> markNode back b' $ hUpdate heap back (NMarked Done (NAp addr1 addr))

            | (NMarked (Visit n) (NData tag addrs)) <- hLookup heap back, n < length addrs
                -> markNode (addrs !! n) back $ hUpdate heap back (NMarked (Visit $ n + 1) (NData tag $ replaceAll addrs [(n - 1, addr), (n, addrs !! (n - 1))]))

            | (NMarked (Visit n) (NData tag addrs)) <- hLookup heap back, n == length addrs
                -> markNode back (last addrs) $ hUpdate heap back (NMarked Done (NData tag $ replace addrs (n - 1, addr)))

            | otherwise -> error $ "GC: unexpected node type: " ++ (iDisplay $ showNode node)

        (NAp addr1 addr2)  -> markNode addr1 addr $ hUpdate heap addr (NMarked (Visit 1) (NAp back addr2))

        (NData tag addrs)
            | null addrs   -> markNode addr back heapDone -- treat as if atom
            | otherwise    -> markNode (head addrs) addr $ hUpdate heap addr (NMarked (Visit 1) (NData tag $ replace addrs (0, back)))

        -- indirections
        (NInd addr1) -> markNode addr1 back heap

        -- make Done nodes
        (NSupercomb _ _ _) -> markNode addr back heapDone
        (NNum _)           -> markNode addr back heapDone
        (NPrim _ _)        -> markNode addr back heapDone

    where node = hLookup heap addr
          heapDone  = hUpdate heap addr (NMarked Done node)

scanHeap :: TiHeap -> TiHeap
scanHeap heap = foldr prune heap (hAddresses heap)
    where prune addr h
            | (NMarked _ boxed) <- node = hUpdate h addr boxed
            | otherwise                 = hFree h addr
            where node = hLookup heap addr
