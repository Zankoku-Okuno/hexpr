import Data.Spine


instance DeQuasiQuote Int where
	quoteForm = 0
	listForm = (-1)

main = print . deQuasiQuote $ QNest [[QLeaf 1], [QLeaf 2]]