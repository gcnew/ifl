module Lexer where

import Data.Char (isDigit, isAlpha)

type Token = (Int, String) -- Atoken is never empty

twoCharOps :: [String]
twoCharOps = ["==", "?=", ">=", "<=", "->"]

clex :: Int -> String -> [Token]
clex _ [] = []

clex ln (c1 : c2 : cs)
    | op == "--"           = clex (ln + 1) (drop 1 (dropWhile (/= '\n') cs))
    | op `elem` twoCharOps = (ln, op) : clex ln cs
    where op = [c1, c2]

clex ln (c:cs)
    | c == '\n'      = clex (ln + 1) cs
    | isWhiteSpace c = clex ln cs

clex ln (c:cs) | isDigit c = (ln, numToken) : clex ln rest
    where numToken = c : (takeWhile isDigit cs)
          rest = dropWhile isDigit cs

clex ln (c:cs) | isAlpha c = (ln, varTok) : clex ln rest
    where varTok = c : (takeWhile isIdChar cs)
          rest = dropWhile isIdChar cs

clex ln (c:cs) = (ln, [c]) : clex ln cs

isIdChar :: Char -> Bool
isIdChar c = isAlpha c || isDigit c || (c == '_') 

isWhiteSpace :: Char -> Bool
isWhiteSpace = (`elem` " \t\n")
