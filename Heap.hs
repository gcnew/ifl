{-# OPTIONS_GHC -Wall #-}

module Heap where

import Utils (aLookup)

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
