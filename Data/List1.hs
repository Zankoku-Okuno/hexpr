{-# LANGUAGE DeriveFunctor #-}
module Data.List1 where

newtype List1 a = List1 (a, [a])
	deriving (Eq, Functor)

fromList1 :: List1 a -> [a]
fromList1 (List1 (x, xs)) = x:xs

toList1 :: a -> [a] -> List1 a
toList1 x xs = List1 (x, xs)

instance Show a => Show (List1 a) where
    show xs = "1" ++ show (fromList1 xs)


newtype List2 a = List2 (a, a, [a])
	deriving (Eq, Functor)

fromList2 :: List2 a -> [a]
fromList2 (List2 (x1, x2, xs)) = x1:x2:xs

toList2 :: a -> a -> [a] -> List2 a
toList2 x1 x2 xs = List2 (x1, x2, xs)

instance Show a => Show (List2 a) where
    show xs = "2" ++ show (fromList2 xs)
