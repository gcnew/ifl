{-# OPTIONS_GHC -Wall #-}

module Language where

import Iseq ()
import AST
import PrettyPrint

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
