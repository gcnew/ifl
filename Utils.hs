{-# OPTIONS_GHC -Wall #-}

module Utils where

space :: Int -> String
space n = replicate n ' '

split :: Eq a => a -> [a] -> [[a]]
split sep arr = foldr splitter [[]] arr
    where splitter c acc | c /= sep  = ((c:head acc) : tail acc)
                         | otherwise = [] : acc

zipNWith :: ([a] -> b) -> [[a]] -> [b]
zipNWith _ [] = []
zipNWith f xss | any null xss = []
               | otherwise    = f (map head xss) : zipNWith f (map tail xss)

replaceAll :: [a] -> [(Int, a)] -> [a]
replaceAll = foldr (flip replace)

replace :: [a] -> (Int, a) -> [a]
replace xs (idx, val)
    | idx < 0   = error "invalid index: negative"
    | otherwise = replace' xs idx val

    where replace' [] _ _     = error "invalid index: greater than list length"
          replace' (_:ys) 0 v = v : ys
          replace' (y:ys) n v = y : replace' ys (n - 1) v

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
