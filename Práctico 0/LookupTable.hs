{-# OPTIONS_GHC -fno-warn-tabs #-}

module LookupTable where

create :: Table a b

upd :: Eq a => (a,b) -> Table a b -> Table a b

lkup :: Eq a => a -> Table a b -> Maybe b

del :: Eq a => a -> Table a b -> Table a b

type Table a b = [(a,b)]

create = []

upd p [] = [p]
upd p@(k,d) (p'@(k',_) : ps) 
   | k == k' = p : ps
   | k /= k' = p' : upd p ps

lkup k [] = Nothing
lkup k (p'@(k',v') : ps) 
   | k == k' = Just v'
   | k /= k' = lkup k ps

del k [] = []
del k (p'@(k',_) : ps) 
   | k == k' = ps
   | k /= k' = p' : del k ps

