{-# OPTIONS_GHC -Wall #-}

module GM where

import Data.List (find, foldl')

import AST
import Heap
import Iseq
import Utils
import Parser (parse)
import Main (preludeDefs)

type GmStats = Int
type GmStack = [Addr]
type GmHeap = Heap Node
type GmDump = [GmDumpItem]
type GmCode = [Instruction]
type GmGlobals = ASSOC Name Addr

type GmDumpItem = (GmCode, GmStack)

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
                 | Eval
                 | Abort
                 | Add | Sub | Mul | Div | Neg
                 | Eq | Ne | Lt | Le | Gt | Ge
                 | Cond [Instruction] [Instruction]
                 deriving (Eq, Show)

data GmState = GmState { gmCode    :: GmCode,     -- Current instruction stream
                         gmStack   :: GmStack,    -- Current stack
                         gmDump    :: GmDump,
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

          dispatch (Cond ifTrue ifFalse) = primCond ifTrue ifFalse

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
isDataNode (NNum _) = True
isDataNode _        = False

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

unwind :: GmState -> GmState
unwind state = newState (hLookup heap addr)
    where heap  = gmHeap state
          stack = gmStack state
          dump  = gmDump state

          (addr:rest) = stack

          newState (NNum _)
            | ((code, stack') : dump') <- dump
                = state { gmCode = code, gmStack = addr : stack', gmDump = dump' }
            | otherwise = state

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
compile program = GmState initialCode [] [] heap globals statInitial
    where scDefs = program ++ preludeDefs
          (heap, globals) = buildInitialHeap scDefs

initialCode :: GmCode
initialCode = [ PushGlobal "main", Unwind ] -- no idea why we need Eval,
                                            -- Unwind works just fine..

buildInitialHeap :: CoreProgram -> (GmHeap, GmGlobals)
buildInitialHeap prog = mapAccuml allocateSc hInitial compiled
    where compiled = map compileSc prog ++ compiledPrimitives

allocateSc :: GmHeap -> GmCompiledSC -> (GmHeap, (Name, Addr))
allocateSc heap (name, nargs, instns) = (heap', (name, addr))
    where (heap', addr) = hAlloc heap (NGlobal nargs instns)

compileSc :: (Name, [Name], CoreExpr) -> GmCompiledSC
compileSc (name, env, body) = (name, length env, compileR body (zip env [0..]))

compileR :: GmCompiler
compileR e env = compileE e env ++ [ Update n, Pop n, Unwind ]
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
compileC (ELet rec defs expr) env = compileLet compileC rec defs expr env

compileC (EConstr _ _) _ = error "compileC: EConstr: not yet implemented"
compileC (ECase _ _) _   = error "compileC: ECase: not yet implemented"
compileC (ELam _ _) _    = error "compileC: ELam: not yet implemented"

compileE :: GmCompiler
compileE (ENum n) _               = [PushInt n]
compileE (ELet rec defs expr) env = compileLet compileE rec defs expr env

-- Lambda If is broken now.. will be fixed when Data constructors are
-- implemented and primitive Cond removed
compileE node env
    | (EVar "if" : ifCond : ifTrue : ifFalse : aps) <- unfolded,
      False                  <- elem "if" (aDomain env)  -- and not a local variable
        = let nAps   = length aps
              env'   = argOffset nAps env
              ifCode = compileE ifCond env'
                        ++ [ Cond (compileE ifTrue  env')
                                  (compileE ifFalse env') ]
              (_, code) = foldl' (comp compileC) (nAps - 1, ifCode) aps
           in code ++ replicate nAps MkAp

    | (EVar op : aps)        <- unfold node [],
      Just (_, arity, instr) <- findBuiltIn op,        -- it is a built-in
      False                  <- elem op (aDomain env)  -- and not a local variable
                                                       -- can't check for prelude :(
        = let strictAps = take arity aps
              lazyAps   = drop arity aps
              strictRes = foldl' (comp compileE) (length aps - 1, instr) strictAps
              (_, code) = foldl' (comp compileC) strictRes lazyAps
           in code ++ replicate (length lazyAps) MkAp -- operator MkAp nodes are needed only in
                                                      -- lambda prelude
                                                      -- e.g.: (1 > 0) 5 6

    | otherwise = compileC node env ++ [ Eval ]

    where unfold (EAp e1 e2) acc = unfold e1 (e2 : acc)
          unfold n acc           = n : acc

          unfolded = unfold node []

          findBuiltIn op = find (\(name, _, _) -> name == op) buildIns

          comp cc (offset, code) expr = let env' = argOffset offset env
                                         in (offset - 1, cc expr env' ++ code)

compileLet :: GmCompiler -> Bool -> [(Name, CoreExpr)] -> GmCompiler
compileLet compiler rec defs expr env
    | rec       = [ Alloc n ]
                    ++ compileDefs True defs env'
                    ++ replicate n (Update $ n - 1)
                    ++ compiler expr env'
                    ++ [ Slide n ]

    | otherwise = compileDefs False defs env
                    ++ compiler expr env'
                    ++ [ Slide n ]

    where n    = length defs
          env' = zip (map fst defs) [n-1, n-2 .. 0] ++ argOffset n env

compileDefs :: Bool -> [(Name, CoreExpr)] -> GmEnvironment -> GmCode
compileDefs _ [] _ = []

compileDefs rec ((name, expr):defs) env = compileC expr env ++ compileDefs rec defs env'
    where env' | rec       = env
               | otherwise = (name, 0) : argOffset 1 env

primCond :: GmCode -> GmCode -> GmState -> GmState
primCond ifTrue ifFalse state = state { gmCode = code' ++ gmCode state, gmStack = stack' }
    where (addr:stack') = gmStack state
          code' | unboxBoolean addr state = ifTrue
                | otherwise               = ifFalse

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
        ("True", 0, [ PushInt 1, Update 0, Pop 0, Unwind ]),
        ("False", 0, [ PushInt 0, Update 0, Pop 0, Unwind ]),

        ("abort", 0, [ Abort ]),

        ("if", 3, [ Push 0, Eval,
                    Cond [Push 1] [Push 2],
                    Update 3, Pop 3, Unwind ])
    ]

builtInCC :: (Name, Int, GmCode) -> GmCompiledSC
builtInCC (name, arity, ins) = (name, arity, force ++ ins ++ clean)
    where force = concat $ replicate arity [ Push (arity - 1), Eval ]
          clean = [ Update arity, Pop arity, Unwind ]

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

showInstruction Eval = iStr "Eval"
showInstruction (Cond _ _) = iStr "Cond"

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

showStats :: GmState -> Iseq
showStats s = iConcat [ iStr "Steps taken = ", iNum (statGetSteps (gmStats s)) ]
