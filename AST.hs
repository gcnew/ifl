module AST where

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
