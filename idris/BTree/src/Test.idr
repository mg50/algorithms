module Test
import BTree as B
import Types

testTree : BTree 1 Int Int
testTree = foldl (\tree, x => B.insert x x tree) (B.newEmptyBTree 1) [1..100]
