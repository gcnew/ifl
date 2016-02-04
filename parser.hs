{-# OPTIONS_GHC -Wall #-}

module Language where

type Name = String

type IsRec = Bool
recursive, nonRecursive :: IsRec
recursive    = True
nonRecursive = False

data Expr a
    = EVar Name             -- Variables
    | ENum Int              -- Numbers
    | EConstr Int Int       -- Constructor tag arity
    | EAp (Expr a) (Expr a) -- Applications
    | ELet                  -- Let(rec) expressions
        IsRec               -- boolean with True = recursive,
        [(a, Expr a)]       -- Definitions
        (Expr a)            -- Body of let(rec)
    | ECase                 -- Case expression
       (Expr a)             -- Expression to scrutinise
       [Alter a]            -- Alternatives
    | ELam [a] (Expr a)     -- Lambda abstractions
    deriving (Show)

type CoreExpr = Expr Name
type Alter a = (Int, [a], Expr a)
type CoreAlt = Alter Name

type ScDefn a = (Name, [a], Expr a)
type CoreScDefn = ScDefn Name

type Program a = [ScDefn a]
type CoreProgram = Program Name


bindersOf :: [(a,b)] -> [a]
bindersOf defns = [name | (name, _) <- defns]

rhssOf :: [(a,b)] -> [b]
rhssOf defns = [rhs | (_, rhs) <- defns]

isAtomicExpr :: Expr a -> Bool
isAtomicExpr (EVar _) = True
isAtomicExpr (ENum _) = True
isAtomicExpr _        = False

preludeDefs :: CoreProgram
preludeDefs = [
    -- I x = x
    ("I", ["x"], EVar "x"),

    -- K x y = x
    ("K", ["x","y"], EVar "x"),

    -- K1 x y = y
    ("K1",["x","y"], EVar "y"),

    -- S f g x = f x (g x)
    ("S", ["f","g","x"],
        EAp (EAp (EVar "f") (EVar "x")) (EAp (EVar "g") (EVar "x"))),

    -- compose f g x = f (g x)
    ("compose", ["f","g","x"],
        EAp (EVar "f") (EAp (EVar "g") (EVar "x"))),

    -- twice f = compose f f
    ("twice", ["f"], EAp (EAp (EVar "compose") (EVar "f")) (EVar "f")) ]

data Iseq = INil
    | IStr String
    | IAppend Iseq Iseq
    | IIndent Iseq
    | INewline
    deriving (Show)

iNil :: Iseq                     -- The empty iseq
iNil = INil

iStr :: String -> Iseq           -- Turn a string into an iseq
iStr = (iInterleave iNewline) . (map IStr) . (split '\n')

iAppend :: Iseq -> Iseq -> Iseq  -- Append two iseqs
iAppend INil s2   = s2
iAppend s1   INil = s1
iAppend s1   s2   = IAppend s1 s2

iNewline :: Iseq                 -- New line with indentation
iNewline = INewline

iIndent :: Iseq -> Iseq          -- Indent an iseq
iIndent s = IIndent s

iDisplay :: Iseq -> String       -- Turn an iseq into a string
iDisplay s = flatten 0 [(s, 0)]

iConcat :: [Iseq] -> Iseq
iConcat xs = foldr iAppend iNil xs

iInterleave :: Iseq -> [Iseq] -> Iseq
iInterleave _ []       = iNil
iInterleave _ [x]      = x
iInterleave sep (x:xs) = x `iAppend` sep `iAppend` iInterleave sep xs

flatten :: Int -> [(Iseq, Int)] -> String
flatten _ []                    = ""
flatten col ((INil, _): seqs)   = flatten col seqs
flatten col ((IStr s, _): seqs) = s ++ flatten (col + length s) seqs

flatten col (((IAppend s1 s2), indent): seqs)
    = flatten col ((s1, indent) : (s2, indent) : seqs)

flatten col ((IIndent s, _) : seqs)
    = flatten col ((s, col) : seqs)

flatten _ ((INewline, indent) : seqs)
    = '\n' : (space indent) ++ (flatten indent seqs)

space :: Int -> String
space n = replicate n ' '

split :: Eq a => a -> [a] -> [[a]]
split sep arr = foldr splitter [[]] arr
    where splitter _ [] = undefined -- should never happen, silence warnings
          splitter c acc@(x:xs) | c /= sep  = ((c:x):xs)
                                | otherwise = [] : acc

operators :: [String]
operators = map (:[]) "+-*/"

pprExpr :: CoreExpr -> Iseq
pprExpr (EVar v)    = iStr v
pprExpr (ENum num)  = iStr (show num)

pprExpr (EAp (EAp (EVar op) e1) e2)
    | op `elem` operators = iConcat [ pprAExpr e1, iStr " ", iStr op, iStr " ", pprAExpr e2 ]
pprExpr (EAp e1 e2) = (pprExpr e1) `iAppend` (iStr " ") `iAppend` (pprAExpr e2)

pprExpr (EConstr tag arity)
    = iConcat [ iStr "Pack{",
                iStr (show tag), iStr ", ",
                iStr (show arity), iStr "}" ]

pprExpr (ELet isrec defns expr)
    = iConcat [ iStr keyword,
                iStr " ", iIndent (pprDefns defns), iNewline,
                iStr "in ", pprExpr expr ]
    where keyword | isrec     = "letrec"
                  | otherwise = "let"

pprExpr (ELam vars expr) = iConcat [ iStr "\\ ", (pprVarNames vars), iStr ". ", pprExpr expr ]

pprExpr (ECase expr alts)
    = iConcat [ iStr "case ", pprExpr expr, iStr " of ",
                iIndent (iNewline `iAppend` pprAlts alts) ]

pprAlts :: [CoreAlt] -> Iseq
pprAlts alts = iInterleave iNewline (map pprAlt alts)

pprAlt :: CoreAlt -> Iseq
pprAlt (tag, vars, expr)
    = iConcat [ iStr "<", iStr (show tag), iStr "> ",
                pprVarNames vars, iStr " -> ", pprExpr expr ]

pprAExpr :: CoreExpr -> Iseq
pprAExpr e
    | isAtomicExpr e = pprExpr e
    | otherwise      = (iStr "(") `iAppend` pprExpr e `iAppend` (iStr ")")

pprDefns :: [(Name,CoreExpr)] -> Iseq
pprDefns defns = iInterleave sep (map pprDefn defns)
    where sep = iConcat [ iStr ";", iNewline ]

pprDefn :: (Name, CoreExpr) -> Iseq
pprDefn (name, expr) = iConcat [ iStr name, iStr " = ", iIndent (pprExpr expr) ]

pprProgram :: CoreProgram -> Iseq
pprProgram prog = iInterleave (iStr "\n\n") (map pprScDefn prog)

pprScDefn :: CoreScDefn -> Iseq
pprScDefn (name, vars, expr) = iConcat [ iStr name, iStr " ", pprVarNames vars,
                                         iStr " = " , iIndent (pprExpr expr) ]

pprVarNames :: [String] -> Iseq
pprVarNames names = iInterleave (iStr " ") (map iStr names)

pprint :: CoreProgram -> String
pprint prog = iDisplay (pprProgram prog)


mkMultiAp :: Int -> CoreExpr -> CoreExpr -> CoreExpr
mkMultiAp n e1 e2 = foldl EAp e1 (take n e2s)
    where e2s = e2 : e2s

--main :: IO ()
--main = putStrLn $ pprint preludeDefs

main :: IO ()
main = putStrLn $ pprint [ ("letSample", [], testLet), ("caseSample", [], testCase) ]

testCase :: CoreExpr
testCase = ECase (EVar "x") [
    -- <0> v -> iStr v
    (0, [ "v" ], (EAp (EVar "iStr") (EVar "v"))),

    -- <1> num -> iStr (show num)
    (1, [ "num" ], (EAp (EVar "iStr") (EAp (EVar "show") (EVar "num")))),

    -- <2> x y z -> x + y * z
    (2, [ "x", "y", "z" ], (EAp (EAp (EVar "+") (EVar "x")) (EAp (EAp (EVar "*") (EVar "y")) (EVar "z"))))
    ]

testLet :: CoreExpr
testLet = (ELet False [
    ("a", (ENum 3)),
    ("b", (ENum 4))
    ]
    (EAp (EAp (EVar "+") (EVar "a")) (EVar "b")))
