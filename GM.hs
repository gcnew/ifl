{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE MultiWayIf #-}

module GM where

import Control.Monad (guard, foldM)
import Control.Monad.Identity (runIdentity)
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
type GmVStack = [Int]
type GmOutput = [Int]
type GmHeap = Heap Node
type GmDump = [GmDumpItem]
type GmCode = [Instruction]
type GmGlobals = ASSOC Name Addr

type GmDumpItem = (GmCode, GmStack, GmVStack)

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
                 | PushBasic Int
                 | MkInt
                 | MkBool
                 | Get
                 | Cond GmCode GmCode
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
                         gmVStack  :: GmVStack,
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

          dispatch (PushBasic n) = pushBasic n
          dispatch MkInt = mkInt
          dispatch MkBool = mkBool
          dispatch Get = primGet
          dispatch (Cond ifTrue ifFalse) = primCond ifTrue ifFalse

          dispatch Neg = primitive1 negate

          dispatch Add = primitive2 (+)
          dispatch Sub = primitive2 (-)
          dispatch Mul = primitive2 (*)
          dispatch Div = primitive2 div

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
    | otherwise       = state { gmCode   = [ Unwind ],
                                gmStack  = [ addr ],
                                gmVStack = [],
                                gmDump   = (code, rest, vStack) : dump }
    where stack  = gmStack state
          vStack = gmVStack state
          code   = gmCode state
          dump   = gmDump state

          (addr:rest) = stack
          node        = hLookup (gmHeap state) addr

primPrint :: GmState -> GmState
primPrint state = state { gmStack = rest, gmOutput = out : gmOutput state }
    where (addr:rest) = gmStack state
          node = hLookup (gmHeap state) addr

          out | (NNum n) <- node = n
              | otherwise        = error "Print: number expected"

pushBasic :: Int -> GmState -> GmState
pushBasic n state = state { gmVStack = n : (gmVStack state) }

mkInt :: GmState -> GmState
mkInt state = state { gmStack = addr : gmStack state, gmVStack = vStack', gmHeap = heap' }
    where (n:vStack')   = gmVStack state
          (heap', addr) = hAlloc (gmHeap state) (NNum n)

mkBool :: GmState -> GmState
mkBool state = state { gmStack = addr : gmStack state, gmVStack = vStack', gmHeap = heap' }
    where (n:vStack')   = gmVStack state

          node | n == 1    = NInd $ findGlobal "False"  -- NConstr 1 []
               | n == 2    = NInd $ findGlobal "True"   -- NConstr 2 []
               | otherwise = error "mkBool: not a boolean"

          findGlobal key = aLookup (gmGlobals state) key err
              where err = error $ "Assert: Global not found: " ++ key

          (heap', addr) = hAlloc (gmHeap state) node

primGet :: GmState -> GmState
primGet state = state { gmStack = stack', gmVStack = n : (gmVStack state) }
    where (addr:stack') = gmStack state
          node = hLookup (gmHeap state) addr
          n | (NNum x)       <- node = x
            | (NConstr 1 []) <- node = 1 -- False
            | (NConstr 2 []) <- node = 2 -- True
            | otherwise              = error "primGet: invalid node"

primCond :: GmCode -> GmCode -> GmState -> GmState
primCond ifTrue ifFalse state = state { gmCode = code' ++ gmCode state, gmVStack = vStack' }
    where (n:vStack') = gmVStack state
          code' | n == 1    = ifFalse
                | n == 2    = ifTrue
                | otherwise = error "primCond: not a boolean"

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
            | ((code, stack', vStack') : dump') <- dump
                = state { gmCode = code,
                          gmStack = addr : stack',
                          gmVStack = vStack',
                          gmDump = dump' }
            | otherwise = state

          newState (NNum _)      = unwindData
          newState (NConstr _ _) = unwindData

          newState (NInd a1)  = state { gmCode = [ Unwind ], gmStack = a1:rest }
          newState (NAp a1 _) = state { gmCode = [ Unwind ], gmStack = a1:stack }

          newState (NGlobal n code)
            | nArgs < n = case dump of
                ((code', stack', vStack') : dump') -> state { gmCode = code',
                                                              gmStack = last stack : stack',
                                                              gmVStack = vStack',
                                                              gmDump = dump' }

                _                         -> error "Unwinding with too few arguments"

            | otherwise = state { gmCode = code, gmStack = rearrange n heap stack }
            where nArgs = length rest

rearrange :: Int -> GmHeap -> GmStack -> GmStack
rearrange n heap stack = take n (map getArg (tail stack)) ++ drop n stack
    where getArg addr | (NAp _ arg) <- hLookup heap addr = arg
                      | otherwise = error "Broken spine: non NAp node encountered"

boolIntrinsics :: [String]
boolIntrinsics = [ "True", "False", "if" ]

constrPrelude :: CoreProgram
constrPrelude = foldr removeDefinition prelude0 boolIntrinsics
    where prelude0 = preludeDefs ++ extraPreludeDefs ++ casePreludeDefs

compile :: CoreProgram -> GmState
compile program = GmState initialCode [] [] [] heap globals [] statInitial
    where scDefs = program ++ constrPrelude
          (heap, globals) = buildInitialHeap scDefs

initialCode :: GmCode
initialCode = [ PushGlobal "main", Unwind ] -- no idea why we need Eval,
                                            -- Unwind works just fine..

buildInitialHeap :: CoreProgram -> (GmHeap, GmGlobals)
buildInitialHeap prog = mapAccuml allocateSc hInitial compiled
    where globalsMap = foldr (\(name, _, _) acc -> (name, hNull) : acc) [] prog
          (cSc, globalsMap') = runState (mapM compileSc prog) globalsMap
          (cExtra, []) = runState (mapM compileSc builtInSc) []
          synth = filter (isPrefixOf "$") (map fst globalsMap')
          cSynth = map compileS synth
          compiled = cSc ++ cExtra ++ cSynth ++ compiledPrimitives

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
        = do (_, code) <- foldM (ccLazy env) (n - 2, []) aps
             return $ code ++ [Pack tag arity]

    -- not-saturated ctor
    | (EConstr tag arity : aps) <- spine,
      n - 1 /= arity
        = do ctorName <- getCtorName tag arity
             (_, code) <- foldM (ccLazy env) (n - 2, []) aps
             return $ code ++ (PushGlobal ctorName : replicate (n - 1) MkAp)

    | otherwise
        = do (_, code) <- foldM (ccLazy env) (n - 1, []) spine
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
         let mRes = runStateT (compileIfOrOp boxResult expr env) globals

         if | Just res <- mRes -> StateT $ const (return res)
            | otherwise        -> do cExpr <- compileC expr env
                                     return (cExpr ++ [ Eval ])

compileIfOrOp :: (String -> GmCode)                -- epilogue provider
                 -> CoreExpr                       -- the root expression
                 -> GmEnvironment                  -- the environment
                 -> StateT GmGlobals Maybe GmCode  -- the result
compileIfOrOp getEpilogue expr env
    = do globals <- get

         let spine = unfoldAp expr
         (EVar op:aps) <- return $ spine

         guard $ not (aHasKey op env)      -- not a local variable
         guard $ not (aHasKey op globals)  -- not a global variable

         -- don't optimese `if` when booleans are redefined
         guard $ op /= "if" || all (not . (`aHasKey` globals)) [ "True", "False" ]

         (opCc, arity) <- if | op == "if"
                                -> return (compileIf, 3)

                             | (Just (_, arity, instr)) <- findBuiltIn op
                                -> return (compileOp instr, arity)

                             | otherwise
                                -> fail "Neither if nor OP."

         let opArgs       = take arity aps
             lazyAps      = drop arity aps
             lazyApsCount = length lazyAps

         opCode <- hoistMaybeT $ opCc opArgs env

         let strictCode = opCode ++ getEpilogue op
         (_, code)  <- hoistMaybeT $ foldM (ccLazy env) (lazyApsCount, strictCode) lazyAps

         return $ code ++ replicate lazyApsCount MkAp

    where hoistMaybeT = mapStateT (return . runIdentity)


compileOp :: GmCode -> [CoreExpr] -> GmEnvironment -> State GmGlobals GmCode
compileOp instr args env = foldM (ccStrict env) instr args

compileIf :: [CoreExpr] -> GmEnvironment -> State GmGlobals GmCode
compileIf args env
    = do let [cond, ifTrue, ifFalse] = args

         cCond    <- compileB cond env
         cIfTrue  <- compileE ifTrue env
         cIfFalse <- compileE ifFalse env

         return $ cCond ++ [ Cond cIfTrue cIfFalse ]

ccStrict :: GmEnvironment -> GmCode -> CoreExpr -> State GmGlobals GmCode
ccStrict env code expr = do cExpr <- compileB expr env
                            return $ cExpr ++ code

ccLazy :: GmEnvironment -> (Int, GmCode) -> CoreExpr -> State GmGlobals (Int, GmCode)
ccLazy env (offset, code) expr = do cExpr <- compileC expr env'
                                    return (offset - 1, cExpr ++ code)
    where env' = argOffset offset env

compileB :: GmCompiler
compileB (ENum n) _ = return [PushBasic n]
compileB (ELet rec defs expr) env = compileLet compileB rec defs expr env

compileB expr env
    = do globals <- get
         case () of
          _ | (Just res) <- runStateT (compileIfOrOp (const []) expr env) globals
                -> StateT $ const (return res)

            | otherwise
                -> do cExpr <- compileE expr env
                      return (cExpr ++ [ Get ])


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
    where env' | rec       = argOffset 1 env
               | otherwise = (name, 0) : argOffset 1 env

primitive1 :: (Int -> Int)           -- operator
              -> GmState -> GmState  -- in state & retval
primitive1 op state =  state { gmVStack = op val : vStack' }
    where (val:vStack') = gmVStack state

primitive2 :: (Int -> Int -> Int)    -- operator
              -> GmState -> GmState  -- in state & retval
primitive2 op state = state { gmVStack = v1 `op` v2 : vStack' }
    where (v1:v2:vStack') = gmVStack state

comparison :: (Int -> Int -> Bool)   -- operator
              -> GmState -> GmState  -- in state & retval
comparison op = primitive2 liftedOp
    where liftedOp x y | x `op` y  = 2 -- True
                       | otherwise = 1 -- False

arithIns :: [(Name, Int, GmCode)]  -- (name, arity, instruction)
arithIns = [ ("negate", 1, [Neg]),

             ("+", 2, [Add]), ("-", 2, [Sub]),
             ("*", 2, [Mul]), ("/", 2, [Div]) ]

relationIns :: [(Name, Int, GmCode)]  -- (name, arity, instruction)
relationIns = [ ( ">", 2, [Gt]), (">=", 2, [Ge]),
                ( "<", 2, [Lt]), ("<=", 2, [Le]),
                ("==", 2, [Eq]), ("/=", 2, [Ne]) ]


builtIns :: [(Name, Int, GmCode)]
builtIns = arithIns ++ relationIns

builtInSc :: CoreProgram
builtInSc = map cc builtIns
    where cc (name, arity, _) = let args = map genArg [1..arity]
                                 in (name, args, foldl1 EAp (map EVar (name:args)))
          genArg n = "a" ++ show n

compiledPrimitives :: [GmCompiledSC]
compiledPrimitives = [
        ("abort", 0, [ Abort ]),
        ("print", 2, [ Eval, Print, Update 0, Unwind ]),

        ("False", 0, [ Pop 1, Pack 1 0, Unwind ]),
        ("True",  0, [ Pop 1, Pack 2 0, Unwind ]),
        ("if",    3, [ Eval, Get, Cond [Eval, Update 1, Pop 1] [Pop 1, Eval, Update 0], Unwind ])
        -- naive:
        -- ("print", 2, [ Push 0, Eval, Print, Push 1, Update 2, Pop 2, Unwind ])
    ]

pluckName :: (Name, Int, GmCode) -> Name
pluckName (name, _, _) = name

findBuiltIn :: String -> Maybe (Name, Int, GmCode)
findBuiltIn = \op -> find ((== op) . pluckName) builtIns

isRelation :: String -> Bool
isRelation op = op `elem` map pluckName relationIns

isArith :: String -> Bool
isArith op = op `elem` map pluckName arithIns

boxResult :: String -> GmCode
boxResult op | isRelation op = [MkBool]
             | isArith    op = [MkInt]
             | "if" == op    = []
             | otherwise     = error $ "boxResult: Unexpected operator: " ++ op

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

showInstruction Get           = iStr "Get"
showInstruction (Cond _ _)    = iStr "Cond"
showInstruction MkInt         = iStr "MkInt"
showInstruction MkBool        = iStr "MkBool"
showInstruction (PushBasic n) = iStr "PushBasic " `iAppend` iNum n

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

          vStackLines = showVStack s

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
                                          vStackLines,
                                          dumpLines ]

showStack :: GmState -> Iseq
showStack s = iInterleave iNewline stackItems
    where stackItems = map (showStackItem s) (reverse (gmStack s))

showVStack :: GmState -> Iseq
showVStack s = iInterleave iNewline stackItems
    where stackItems = map iNum (reverse (gmVStack s))

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
showDumpItem (code, stack, vStack) = iInterleave iNewline [
        iStr "<",
        shortShowInstructions 3 code,
        shortShowStack stack,
        shortShowVStack vStack,
        iStr ">" ]

shortShowInstructions :: Int -> GmCode -> Iseq
shortShowInstructions n code = iConcat [ iStr "{",
                                         iInterleave (iStr "; ") dotcodes,
                                         iStr "}" ]
    where codes = map showInstruction (take n code)
          dotcodes | length code > n = codes ++ [ iStr "..." ]
                   | otherwise = codes

shortShowStack :: GmStack -> Iseq
shortShowStack stack = iConcat [ iStr "[",
                                 iInterleave (iStr ", ") (map showFWAddr stack),
                                 iStr "]" ]

shortShowVStack :: GmVStack -> Iseq
shortShowVStack = iInterleave (iStr ", ") . map iNum . take 5 . reverse

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

showOutput :: GmState -> Iseq
showOutput s = iConcat [ iStr "Output: ",
                          iInterleave (iStr ", ") (reverse $ map iNum (gmOutput s)) ]

showStats :: GmState -> Iseq
showStats s = iConcat [ iStr "Steps taken = ", iNum (statGetSteps (gmStats s)) ]
