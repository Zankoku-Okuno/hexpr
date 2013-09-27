module Data.List1 where

newtype List1 a = List1 (a, [a])

fromList1 :: List1 a -> [a]
fromList1 (List1 (x, xs)) = x:xs

toList1 :: a -> [a] -> List1 a
toList1 x xs = List1 (x, xs)


instance Show a => Show (List1 a) where
    show xs = "1" ++ show (fromList1 xs)
