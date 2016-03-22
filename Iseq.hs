{-# OPTIONS_GHC -Wall #-}

module Iseq where

import Utils

data Iseq = INil
    | IStr String
    | IAppend Iseq Iseq
    | IIndent Iseq
    | INewline
    deriving (Show)

iNil :: Iseq                     -- The empty iseq
iNil = INil

iIsNil :: Iseq -> Bool
iIsNil INil = True
iIsNil _    = False

iStr :: String -> Iseq           -- Turn a string into an iseq
iStr = iInterleave iNewline . map mkIStr . split '\n'
    where mkIStr ""  = iNil
          mkIStr str = IStr str

iAppend :: Iseq -> Iseq -> Iseq  -- Append two iseqs
iAppend = IAppend

iNewline :: Iseq                 -- New line with indentation
iNewline = INewline

iIndent :: Iseq -> Iseq          -- Indent an iseq
iIndent s = IIndent s

iDisplay :: Iseq -> String       -- Turn an iseq into a string
iDisplay s = flatten 0 [(s, 0)]

iConcat :: [Iseq] -> Iseq
iConcat xs = foldr iAppend iNil xs

iNum :: Int -> Iseq
iNum n = iStr (show n)

iFWNum :: Int -> Int -> Iseq
iFWNum width n = iStr (space (width - length digits) ++ digits)
    where digits = (show n)

iLayn :: [Iseq] -> Iseq
iLayn xs = iConcat (map layItem (zip [1..] xs))
    where layItem (n, s) = iConcat [ iFWNum 4 n, iStr ") ", iIndent s, iNewline ]

iInterleave :: Iseq -> [Iseq] -> Iseq
iInterleave _ []       = iNil
iInterleave _ [x]      = x
iInterleave sep (x:xs) = x `iAppend` sep `iAppend` iInterleave sep xs

iSplitView :: [Iseq] -> Iseq
iSplitView = iInterleave iNewline . map cf . eqlzLineSz . eqlzLineCount . toStringLines
    where cf = iInterleave (iStr "  |  ") . map iStr  -- concat function

          toStringLines  = map (split '\n' . iDisplay)
          padWith x n xs = xs ++ replicate (n - length xs) x

          maxLines       = maximum . map length
          maxLinesLength = map (maximum . map length)

          eqlzLineCount views = map (padWith "" (maxLines views)) views
          eqlzLineSz    views = zipNWith (zipWith (padWith ' ') (maxLinesLength views)) views

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
