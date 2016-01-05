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

iNil :: Iseq                     -- The empty iseq
iNil = INil

iStr :: String -> Iseq           -- Turn a string into an iseq
iStr str = IStr str

iAppend :: Iseq -> Iseq -> Iseq  -- Append two iseqs
iAppend s1 s2 = IAppend s1 s2

iNewline :: Iseq                 -- New line with indentation
iNewline = IStr "\n"

iIndent :: Iseq -> Iseq          -- Indent an iseq
iIndent s = IIndent s

iDisplay :: Iseq -> String       -- Turn an iseq into a string
iDisplay s = flatten 0 [(0, s)]

iConcat :: [Iseq] -> Iseq
iConcat xs = foldr iAppend iNil xs

iInterleave :: Iseq -> [Iseq] -> Iseq
iInterleave _ []       = iNil
iInterleave _ [x]      = x
iInterleave sep (x:xs) = x `iAppend` sep `iAppend` iInterleave sep xs 

flatten :: Int -> [(Int, Iseq)] -> String
flatten _ []                                 = ""
flatten col ((indent, INil) : seqs)          = flatten col seqs
flatten col ((indent, IStr s) : seqs)        = (space indent) ++ s ++ flatten indent seqs
flatten col ((indent, IAppend s1 s2) : seqs)
    = flatten col ((indent, s1) : (indent, s2) : seqs)

flatten col ((indent, INewline) : ss)
    = '\n' : (space indent) ++ (flatten indent ss)

flatten col ((indent, IIndent s) : ss)
    = flatten col ((col, s) : ss)

space :: Int -> String
space n = replicate n ' '

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
    = iConcat [ iStr "case ", pprExpr expr, iStr " of", iNewline,
                iIndent (pprAlts alts) ]

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



