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

casePreludeDefs :: CoreProgram
casePreludeDefs = parseDefs [
        "if cond t f = case cond of\n\
        \                   <1> -> f;\n\
        \                   <2> -> t",

        "caseList l cn cc = case l of\n\
        \                        <1>       -> cn;\n\
        \                        <2> hd tl -> cc hd tl",

        "casePair p fn = case p of\n\
        \                     <1> fst snd -> fn fst snd"
    ]

lambdaPreludeDefs :: CoreProgram
lambdaPreludeDefs = parseDefs [
        "caseList = I",
        "casePair = I",
        "if = I",

        "MkPair a b f = f a b",
        "fst p = p K",
        "snd p = p K1",

        "Nil cn cc=cn",
        "Cons a b cn cc = cc a b",
        "head l = caseList l abort K",
        "tail l = caseList l abort K1",

        "Unit = negate 1",
        "printList xs = caseList xs Unit printCons",
        "printCons h t = print h (printList t)",

        "True t f = t",
        "False t f = f",

        "and b1 b2 t f = b1 (b2 t f) f",
        "or b1 b2 t f = b1 t (b2 t f)",
        "not b t f = b f t"
    ]

main :: IO ()
main = putStrLn . pprint $ preludeDefs ++ extraPreludeDefs
