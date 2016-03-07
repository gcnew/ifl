{-# OPTIONS_GHC -Wall #-}

module Main where

import Data.List (intercalate)

import AST
import Parser (parse)
import PrettyPrint

parseDefs :: [String] -> CoreProgram
parseDefs = parse . intercalate ";\n"

preludeDefs :: CoreProgram
preludeDefs = parseDefs [
        "I x = x",
        "K x y = x",
        "K1 x y = y",
        "S f g x = f x (g x)",
        "compose f g x = f (g x)",
        "twice f = compose f f"
    ]

extraPreludeDefs :: CoreProgram
extraPreludeDefs = parseDefs [
        "MkPair = Pack{1,2}",
        "fst p = casePair p K",
        "snd p = casePair p K1",

        "Nil = Pack{1,0}",
        "Cons = Pack{2,2}",
        "head l = caseList l abort K",
        "tail l = caseList l abort K1",

        "Unit = Pack{1,0}",
        "printList xs  = caseList xs Unit printCons",
        "printCons h t = print h (printList t)",

        "False = Pack{1,0}",
        "True = Pack{2,0}",

        "and x y = if x y False",
        "or x y = if x True y",
        "xor x y = and (or x y) (or (not x) (not y))",
        "not x = if x False True"
    ]

main :: IO ()
main = putStrLn . pprint $ preludeDefs ++ extraPreludeDefs
