{-# OPTIONS_GHC -Wall #-}

module Utils where

space :: Int -> String
space n = replicate n ' '

split :: Eq a => a -> [a] -> [[a]]
split sep arr = foldr splitter [[]] arr
    where splitter _ [] = undefined -- should never happen, silence warnings
          splitter c acc@(x:xs) | c /= sep  = ((c:x):xs)
                                | otherwise = [] : acc

zipNWith :: ([a] -> b) -> [[a]] -> [b]
zipNWith f xss | any null xss = []
               | otherwise    = f (map head xss) : zipNWith f (map tail xss)

type ASSOC a b = [(a,b)]

aLookup :: (Eq a) => ASSOC a b -> a -> b -> b
aLookup [] _ def = def  
aLookup ((k', v) : rest) k def | k' == k   = v
                               | otherwise = aLookup rest k def

aDomain :: ASSOC a b -> [a]
aDomain alist = [key | (key, _) <- alist]

aRange :: ASSOC a b -> [b]
aRange alist = [val | (_, val) <- alist]

aEmpty :: ASSOC a b
aEmpty = []

mapAccuml :: (a -> b -> (a, c)) -> a -> [b] -> (a, [c])
mapAccuml _ acc [] = (acc, [])
mapAccuml f acc (x:xs) = (acc2, x':xs')
    where (acc1, x')  = f acc x
          (acc2, xs') = mapAccuml f acc1 xs
