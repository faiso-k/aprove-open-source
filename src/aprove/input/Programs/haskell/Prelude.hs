module Prelude (zipWith,negate) where

data Int = Int 

zipWith                  :: (a->b->c) -> [a]->[b]->[c]
zipWith z (a:as) (b:bs)   = z a b : zipWith z as bs
--zipWith _ _      _        = []

negate :: Num a => a -> a
negate x = x

class Ord a where 
  (>=) :: a -> a -> Bool
  
class Eq a where 
  (==) :: a -> a -> Bool
  (/=) :: a -> a -> Bool

class Num a where 
 (-) :: a -> a -> a

(&&) :: Bool -> Bool -> Bool
(&&) x y = x
 
default(Int)