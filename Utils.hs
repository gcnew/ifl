{-# OPTIONS_GHC -Wall #-}

module Utils where

space :: Int -> String
space n = replicate n ' '

split :: Eq a => a -> [a] -> [[a]]
split sep arr = foldr splitter [[]] arr
    where splitter _ [] = undefined -- should never happen, silence warnings
          splitter c acc@(x:xs) | c /= sep  = ((c:x):xs)
                                | otherwise = [] : acc
