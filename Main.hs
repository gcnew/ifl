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

main :: IO ()
main = putStrLn . pprint $ preludeDefs ++ extraPreludeDefs
