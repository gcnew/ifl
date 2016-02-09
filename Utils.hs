{-# OPTIONS_GHC -Wall #-}

module Utils where

space :: Int -> String
space n = replicate n ' '

split :: Eq a => a -> [a] -> [[a]]
split sep arr = foldr splitter [[]] arr
    where splitter _ [] = undefined -- should never happen, silence warnings
          splitter c acc@(x:xs) | c /= sep  = ((c:x):xs)
                                | otherwise = [] : acc

type Addr = Int
type Heap a = (Int, [Addr], [(Addr, a)])

hInitial :: Heap a
hInitial = (0, [1..], [])

hAlloc :: Heap a -> a -> (Heap a, Addr)
hAlloc (size, (next : free), cts) n = ((size+1, free, (next, n) : cts), next)
hAlloc _ _ = error "Heap addresses exhausted"

hUpdate :: Heap a -> Addr -> a -> Heap a
hUpdate (size, free, cts) a n = (size, free, (a, n) : remove cts a)

hFree :: Heap a -> Addr -> Heap a
hFree (size, free, cts) a = (size-1, a:free, remove cts a)

hLookup :: Heap a -> Addr -> a
hLookup (_, _, cts) a = aLookup cts a (error ("Can't find node " ++ showaddr a ++ " in heap"))

hAddresses :: Heap a -> [Addr]
hAddresses (_, _, cts) = [addr | (addr, _) <- cts]

hSize :: Heap a -> Int
hSize (size, _, _) = size

hNull :: Addr
hNull = 0

hIsnull :: Addr -> Bool
hIsnull = (== hNull)

showaddr :: Addr -> [Char]
showaddr a = '#' : show a

remove :: [(Int,a)] -> Int -> [(Int,a)]
remove [] a = error ("Attempt to update or free nonexistent address " ++ showaddr a)
remove ((a', n) : cts) a | a == a'   = cts
                         | otherwise = (a',n) : remove cts a

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
