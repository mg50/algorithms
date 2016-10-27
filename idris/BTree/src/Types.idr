module Types
import Data.Vect

%default total
%access public export

data BoundedVect : Nat -> Nat -> Nat -> Type -> Type where
  MkBoundedVect : Vect n a ->
                  LTE min n ->
                  LTE n max ->
                  BoundedVect n min max a

data Entry : Type -> Type -> Type where
  MkEntry : k -> v -> Entry k v

Eq k => Eq (Entry k v) where
  (MkEntry k _) == (MkEntry k' _) = k == k'

Ord k => Ord (Entry k v) where
  compare (MkEntry k _) (MkEntry k' _) = compare k k'

Entries : Nat -> Nat -> Nat -> Type -> Type -> Type
Entries n min order k v = BoundedVect n min (2*order) (Entry k v)

mutual
  Children : Nat -> Nat -> Nat -> Nat -> Type -> Type -> Type
  Children n min order height k v =
    BoundedVect (S n) (S min) (2*order + 1) (m : Nat ** Node m order order height k v)

  data Node : Nat -> Nat -> Nat -> Nat -> Type -> Type -> Type where
    MkLeaf : LTE min order ->
             Entries n min order k v ->
             Node n min order 0 k v
    MkNode : LTE min order ->
             Entries n min order k v ->
             Children n min order height k v ->
             Node n min order (S height) k v

data InsertionResult : Nat -> Nat -> Nat -> Nat -> Type -> Type -> Type where
  Success : Node n min order height k v -> InsertionResult n min order height k v
  Split : Node order min order height k v ->
          Entry k v ->
          Node order min order height k v ->
          InsertionResult order min order height k v

data Root : Nat -> Type -> Type -> Type where
  RootLeaf : Node n 0 order 0 k v -> Root order k v
  RootInternal : Node n 1 order (S height) k v -> Root order k v

data BTree : Nat -> Type -> Type -> Type where
  MkBTree : LTE 1 order -> Root order k v -> BTree order k v


--------------------------------------------------------------------------------
-- DISPLAY
--------------------------------------------------------------------------------

(Show k, Show v) => Show (Entry k v) where
  show (MkEntry k v) = "(" ++ show k ++ "," ++ show v ++ ")"

showEntries : (Show k, Show v) => Entries n min order k v -> String
showEntries {n} (MkBoundedVect xs _ _) = "[" ++ go n xs ++ "]"
  where
    go : (Show k, Show v) => (n : Nat) -> Vect n (Entry k v) -> String
    go Z [] = ""
    go (S Z) (e::[]) = show e
    go (S (S k)) (e::e'::es) = show e ++ "," ++ go (S k) (e'::es)

spaces : Nat -> String
spaces Z = ""
spaces (S n) = "  " ++ spaces n

mutual
  -- why do I need to define it using a helper function?
  showNodeHelper : (Show k, Show v) => (n : Nat) -> (m : Nat ** Node m min order height k v) -> String
  showNodeHelper n (m ** node) = showNode n node

  showNode : (Show k, Show v) => (n : Nat) -> Node m min order height k v -> String
  showNode n (MkLeaf _ entries) = spaces n ++ showEntries entries
  showNode n (MkNode _ entries (MkBoundedVect children _ _)) =
    let firstLine = spaces n ++ showEntries entries
        otherLines = map (showNodeHelper (2+n)) children
    in Strings.unlines (firstLine :: toList otherLines)

(Show k, Show v) => Show (Node n min order height k v) where
  show = showNode 0

(Show k, Show v) => Show (Root order k v) where
  show (RootLeaf node) = show node
  show (RootInternal node) = show node

(Show k, Show v) => Show (BTree order k v) where
  show (MkBTree _ root) = show root
