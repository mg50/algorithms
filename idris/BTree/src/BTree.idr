module BTree
import Data.Vect
import Node as N
import Lemmas as L
import Types

%default total
%access public export

newEmptyBTree : (order : Nat) -> {auto pf: LTE 1 order} -> BTree order k v
newEmptyBTree {pf} n = MkBTree pf (RootLeaf node)
  where
    node : Node 0 0 order 0 k v
    node = MkLeaf LTEZero (MkBoundedVect [] LTEZero LTEZero)

find : Ord k => k -> BTree order k v -> Maybe v
find k (MkBTree _ (RootLeaf node)) = N.find k node
find k (MkBTree _ (RootInternal node)) = N.find k node

handleSplit : Ord k =>
              LTE min order ->
              LTE 1 order ->
              Node order min order height k v ->
              Entry k v ->
              Node order min order height k v ->
              BTree order k v
handleSplit {order} minLteOrder oneLteOrder left mid right =
  let entries = MkBoundedVect [mid] lteRefl (L.lemma6 order oneLteOrder)
      left' = N.adjustMin minLteOrder left
      right' = N.adjustMin minLteOrder right
      node = MkNode oneLteOrder entries $
        MkBoundedVect [(order ** left'), (order ** right')]
                      lteRefl
                      (L.lemma7 order oneLteOrder)
  in MkBTree oneLteOrder (RootInternal node)

insert : Ord k => k -> v -> BTree order k v -> BTree order k v
insert {order} k v (MkBTree oneLteOrder (RootLeaf node)) =
  case N.insert (MkEntry k v) node of
    (_ ** Success node') => MkBTree oneLteOrder (RootLeaf node')
    (order ** Split left mid right) =>
      handleSplit LTEZero oneLteOrder left mid right

insert {order} k v (MkBTree oneLteOrder (RootInternal node)) =
  case N.insert (MkEntry k v) node of
  (_ ** Success node') => MkBTree oneLteOrder (RootInternal node')
  (order ** Split left mid right) =>
    handleSplit oneLteOrder oneLteOrder left mid right
