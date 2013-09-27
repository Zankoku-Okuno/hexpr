module Data.List1 where

newtype List1 a = List1 (a, [a])

fromList1 :: List1 a -> [a]
fromList1 (x, [xs]) = x:xs

toList1 :: [a] -> List1 a
toList1 xs = (head xs, tail xs)


instance Show a => Show (List1 a) where
	show xs = "1[" ++ impl xs ++ "]"
		where
		impl (Nil1 x) = show x
		impl (Cons1 x xs) = show x ++ ", " ++ show xs
