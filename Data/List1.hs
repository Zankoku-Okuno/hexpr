{-# LANGUAGE DeriveFunctor #-}
module Data.List1 where

data List1 a = Nil1 a | Cons1 a (List1 a)
	deriving (Eq, Functor)

toList1 :: [a] -> List1 a
toList1 [] = error "Attempt to create List1 value without elements."
toList1 [x] = Nil1 x
toList1 (x : xs) = Cons1 x $ toList1 xs

fromList1 :: List1 a -> [a]
fromList1 (Nil1 x) = [x]
fromList1 (Cons1 x xs) = x : fromList1 xs

instance Show a => Show (List1 a) where
	show xs = "1[" ++ impl xs ++ "]"
		where
		impl (Nil1 x) = show x
		impl (Cons1 x xs) = show x ++ ", " ++ show xs
