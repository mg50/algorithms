module Test
import BTree as B
import Types

testTree : BTree 1 Int Int
testTree = foldl (\tree, x => B.insert x (2*x) tree) (B.newEmptyBTree 1) [1..100]

result : Maybe Int
result = B.find 17 testTree
