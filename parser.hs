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
    ("I", ["x"], EVar "x"),
    ("K", ["x","y"], EVar "x"),
    ("K1",["x","y"], EVar "y"),
    ("S", ["f","g","x"],
        EAp (EAp (EVar "f") (EVar "x")) (EAp (EVar "g") (EVar "x"))),
    ("compose", ["f","g","x"],
        EAp (EVar "f") (EAp (EVar "g") (EVar "x"))),
    ("twice", ["f"], EAp (EAp (EVar "compose") (EVar "f")) (EVar "f")) ]

data Iseq = INil
    | IStr String
    | IAppend Iseq Iseq

iNil :: Iseq                     -- The empty iseq
iNil = INil

iStr :: String -> Iseq           -- Turn a string into an iseq
iStr str = IStr str

iAppend :: Iseq -> Iseq -> Iseq  -- Append two iseqs
iAppend s1 s2 = IAppend s1 s2

iNewline :: Iseq                 -- New line with indentation
iNewline = IStr "\n"

iIndent :: Iseq -> Iseq          -- Indent an iseq
iIndent s = s

iDisplay :: Iseq -> String       -- Turn an iseq into a string
iDisplay s = flatten [s]

iConcat :: [Iseq] -> Iseq
iConcat xs = foldl iAppend iNil xs

iInterleave :: Iseq -> [Iseq] -> Iseq
iInterleave sep seqs = iConcat list
    where list :: [Iseq]
          list = join sep seqs

          join :: Iseq -> [Iseq] -> [Iseq]
          join _ []     = []
          join _ (x:[]) = [x]
          join s (x:xs) = (x : s : (join s xs))

flatten :: [Iseq] -> String
flatten []                     = ""
flatten (INil : seqs)          = flatten seqs
flatten (IStr s : seqs)        = s ++ flatten seqs
flatten (IAppend s1 s2 : seqs) = flatten (s1 : s2 : seqs)

pprExpr :: CoreExpr -> Iseq
pprExpr (EVar v)    = iStr v
pprExpr (ENum num)  = iStr (show num)
pprExpr (EAp e1 e2) = (pprExpr e1) `iAppend` (iStr " ") `iAppend` (pprAExpr e2)

pprExpr (EConstr tag arity)
    = iConcat [ iStr "Pack{",
                iStr (show tag), iStr ", ",
                iStr (show arity), iStr "}" ]

pprExpr (ELet isrec defns expr)
    = iConcat [ iStr keyword, iNewline,
                iStr "  ", iIndent (pprDefns defns), iNewline,
                iStr "in ", pprExpr expr ]
    where keyword | isrec     = "letrec"
                  | otherwise = "let"

pprExpr (ELam vars expr) = iConcat [ iStr "\\ ", (pprVarNames vars), iStr ". ", pprExpr expr ]

pprExpr (ECase expr alts)
    = iConcat [ iStr "case ", pprExpr expr ]

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
pprScDefn (name, vars, expr) = iConcat [ iStr name, iStr " ", pprVarNames vars, iStr " = ", pprExpr expr ]

pprVarNames :: [String] -> Iseq
pprVarNames names = iInterleave (iStr " ") (map iStr names)

pprint :: CoreProgram -> String
pprint prog = iDisplay (pprProgram prog)


mkMultiAp :: Int -> CoreExpr -> CoreExpr -> CoreExpr
mkMultiAp n e1 e2 = foldl EAp e1 (take n e2s)
    where e2s = e2 : e2s

main :: IO ()
main = putStrLn $ pprint preludeDefs



