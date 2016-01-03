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

iNil     :: Iseq                  -- The empty iseq
iStr     :: String -> Iseq        -- Turn a string into an iseq
iAppend  :: Iseq -> Iseq -> Iseq  -- Append two iseqs
iNewline :: Iseq                  -- New line with indentation
iIndent  :: Iseq -> Iseq          -- Indent an iseq
iDisplay :: Iseq -> String        -- Turn an iseq into a string

pprExpr :: CoreExpr -> Iseq
pprExpr (EVar v)    = iStr v
pprExpr (EAp e1 e2) = (pprExpr e1) `iAppend` (iStr " ") `iAppend` (pprAExpr e2)

pprExpr (ELet isrec defns expr)
    = iConcat [ iStr keyword, iNewline,
                iStr "  ", iIndent (pprDefns defns), iNewline,
                iStr "in ", pprExpr expr ]
    where keyword | not isrec = "let"
                  | isrec = "letrec"

pprDefns :: [(Name,CoreExpr)] -> Iseq
pprDefns defns = iInterleave sep (map pprDefn defns)
    where sep = iConcat [ iStr ";", iNewline ]

pprDefn :: (Name, CoreExpr) -> Iseq
pprDefn (name, expr) = iConcat [ iStr name, iStr " = ", iIndent (pprExpr expr) ]

iConcat :: [Iseq] -> Iseq
iConcat xs = foldl iAppend iNil xs

iInterleave :: Iseq -> [Iseq] -> Iseq
iInterleave sep xs = iConcat list
    where list = join sep xs
          join s []     = []
          join s (x:xs) = (x : s : (join s xs))

main = show preludeDefs



