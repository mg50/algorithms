module Node
import Data.Vect
import Types
import BoundedVect
import Util as U
import Lemmas as L

%default total
%access public export

findInEntries : Ord k => k -> Vect n (Entry k v) -> Maybe v
findInEntries k [] = Nothing
findInEntries k ((MkEntry k' v)::xs) =
  if k == k' then
    Just v
  else if k > k' then
    findInEntries k xs
  else
    Nothing

mutual
  findHelper : Ord k =>
               k ->
               InterleavedList (Entry k v) (m : Nat ** Node m order order height k v) ->
               Maybe v
  findHelper k (NoMore (_ ** node)) = find k node
  findHelper k (More (MkEntry k' v) (_ ** node) rest) =
    if k == k' then
      Just v
    else if k < k' then
      find k node
    else
      findHelper k rest

  find : Ord k => k -> Node n min order height k v -> Maybe v
  find k (MkLeaf _ (MkBoundedVect xs _ _)) = findInEntries k xs
  find k (MkNode _ (MkBoundedVect entries _ _) (MkBoundedVect children _ _)) =
    findHelper k (U.interleave entries children)

insertIntoLeaf : Ord k =>
                 Entry k v ->
                 Node n min order 0 k v ->
                 (n' : Nat ** InsertionResult n' min order 0 k v)
insertIntoLeaf {min} {order} (MkEntry k v) (MkLeaf minLteOrder entries) =
  case ordInsert (MkEntry k v) entries of
    Right (newLength ** bv) => (newLength ** Success (MkLeaf minLteOrder bv))
    Left entries' => let (left, mid, right) = U.trisect entries'
                         leftChild = toLeaf left minLteOrder
                         rightChild = toLeaf right minLteOrder
                     in (order ** Split leftChild mid rightChild)
  where
    -- why do I need to specify the k/v implicits here?
    toLeaf : {k, v : Type} -> Vect order (Entry k v) -> LTE min order -> Node order min order 0 k v
    toLeaf xs minLteOrder = MkLeaf minLteOrder $ MkBoundedVect xs minLteOrder (lteAddRight order)

mutual
  -- this is crazy! how can we simplify it?
  insertIntoChild : Ord k =>
                    Entry k v ->
                    LTE idx n ->
                    Node n min order (S height) k v ->
                    (n' : Nat ** InsertionResult n' min order (S height) k v)
  insertIntoChild {n} {idx} entry idxLteN (MkNode minLteOrder entries children) =
    let MkBoundedVect entriesVect epf1 epf2 = entries
        MkBoundedVect childrenVect cpf1 cpf2 = children
        (complement ** lemma) = L.lemma8 idxLteN
        (left, (childLength ** child)::right) = U.vsplit (U.retypeVect lemma childrenVect)
    in case insert entry child of
      -- entry inserted into child without split
      (newLength ** Success child') =>
        let newChildren = U.retypeVect (sym lemma) (left ++ (newLength ** child')::right)
        in (n ** Success $ MkNode minLteOrder entries (MkBoundedVect newChildren cpf1 cpf2))

      -- insertion into the child caused overflow
      (_ ** Split l mid r) =>
        let newEntryVect = U.vectInsertOrd mid entriesVect
            newLeftChild = (order ** l)
            newRightChild = (order ** r)
            newChildrenVect = left ++ newLeftChild :: newRightChild :: right
            newChildrenVect' = U.retypeVect (L.lemma1 lemma) newChildrenVect
        in case decEq n (2*order) of
          -- we have room for the new entry/children here
          No contra =>
            let lteMaxProof1 = L.lemma2 n (2*order) epf2 contra
                newEntries = MkBoundedVect newEntryVect (lteSuccRight epf1) lteMaxProof1

                lteMaxProof2 = L.lemma2 (S n) (2*order + 1) cpf2 (L.lemma3 contra)
                newChildren = MkBoundedVect newChildrenVect' (lteSuccRight cpf1) lteMaxProof2
            in (S n ** Success $ MkNode minLteOrder newEntries newChildren)

          -- we're out of room and need to split this node as well
          Yes nEq2Order =>
            let (leftEntries, midEntry, rightEntries) =
                  U.trisect $ U.retypeVect (cong nEq2Order) newEntryVect
                vect' = U.retypeVect (L.lemma4 order) $
                        U.retypeVect (cong nEq2Order) newChildrenVect'
                (leftChildren, rightChildren) = U.vsplit vect'

                SminLteSorder = LTESucc minLteOrder
                leftEntries' = MkBoundedVect leftEntries minLteOrder (lteAddRight order)
                leftChildren' = MkBoundedVect leftChildren SminLteSorder (L.lemma5 order)
                leftNode = MkNode minLteOrder leftEntries' leftChildren'

                rightEntries' = MkBoundedVect rightEntries minLteOrder (lteAddRight order)
                rightChildren' = MkBoundedVect rightChildren SminLteSorder (L.lemma5 order)
                rightNode = MkNode minLteOrder rightEntries' rightChildren'
            in (order ** Split leftNode midEntry rightNode)


  insertIntoNode : Ord k =>
                   Entry k v ->
                   Node n min order (S height) k v ->
                   (n' : Nat ** InsertionResult n' min order (S height) k v)
  insertIntoNode {n} {min} entry node@(MkNode minLteOrder (MkBoundedVect entries p1 p2) children) =
    case U.findInsertionLoc entry entries of
      -- key is already present in current node's entries, so just update values
      Left xs => (n ** Success $ MkNode minLteOrder (MkBoundedVect xs p1 p2) children)
      -- key is absent, try insertion in child at this index
      Right (_ ** idxLteN) => insertIntoChild entry idxLteN node


  insert : Ord k =>
           Entry k v ->
           Node n min order height k v ->
           (n' : Nat ** InsertionResult n' min order height k v)
  insert entry leaf@(MkLeaf _ _) = insertIntoLeaf entry leaf
  insert entry node@(MkNode _ _ _) = insertIntoNode entry node

adjustMin : LTE min order -> Node order min order height k v -> Node order order order height k v
adjustMin {order} minLteOrder (MkLeaf _ (MkBoundedVect entries zLteN nLteMax)) =
  MkLeaf lteRefl (MkBoundedVect entries lteRefl (lteAddRight order))
adjustMin {order} lteMinOrder (MkNode _ entries children) =
  let MkBoundedVect entriesVect _ _ = entries
      MkBoundedVect childrenVect _ _ = children

      entries' = MkBoundedVect entriesVect lteRefl (lteAddRight order)
      children' = MkBoundedVect childrenVect lteRefl (L.lemma5 order)
  in MkNode lteRefl entries' children'
