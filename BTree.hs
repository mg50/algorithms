module BTree where

data BTree k = BTree { order :: Int
                     , n :: Int
                     , keys :: [k]
                     , children :: Maybe [BTree k]
                     }

data InsertionResult k = Success (BTree k) | Split (BTree k) k (BTree k) deriving (Show)

instance (Show k) => Show (BTree k) where
  show = go 0
    where go n btree = spaces n ++ "btree " ++ show (keys btree) ++ "\n" ++ showChildren n btree
          showChildren n btree = case children btree of
                                   Nothing -> ""
                                   Just children' -> concatMap (go (n+1)) children'
          spaces n = replicate (2*n) ' '

newEmptyBTree :: Ord k => Int -> BTree k
newEmptyBTree order = BTree order 0 [] Nothing

insert :: (Ord k) => k -> BTree k -> BTree k
insert k btree = case insert' k btree of
                   Success tree -> tree
                   Split left n right -> btree{ keys = [n]
                                              , children = Just [left, right]
                                              , n = 1
                                              }

insert' :: (Ord k) => k -> BTree k -> InsertionResult k
insert' k btree =
  case children btree of
    Nothing -> let (ks, _, len) = unsafeInsert k (n btree) (keys btree)
                   btree' = btree { keys = ks, n = len }
               in normalize btree'

    Just children ->
      case findInsertIndex k btree of
        Nothing -> Success btree
        Just idx ->
          let child = children !! idx
          in case insert' k child of
              Success child' -> Success btree{children = Just (listInsert idx child' children)}
              Split left mid right ->
                let (leftKeys, rightKeys) = splitAt idx (keys btree)
                    (leftChildren, _, rightChildren) = tripart idx children
                    btree' = btree{ children = Just (leftChildren ++ [left, right] ++ rightChildren)
                                  , keys = leftKeys ++ [mid] ++ rightKeys
                                  , n = n btree + 1
                                  }
                in normalize btree'

normalize :: BTree k -> InsertionResult k
normalize btree = if n btree <= 2 * order btree
                  then Success btree
                  else uncurry3 Split (splitOverflowingNode btree)


listInsert :: Int -> a -> [a] -> [a]
listInsert _ x [] = error "could not insert"
listInsert 0 x (y:ys) = x:ys
listInsert n x (y:ys) = n `seq` y : listInsert (n-1) x ys

findInsertIndex :: Ord k => k -> BTree k -> Maybe Int
findInsertIndex k btree =
  let result = dropWhile (\(key, i) -> key < k) $ keys btree `zip` [0..]
  in case result of
       [] -> Just (n btree)
       (k',idx):_ | k == k' -> Nothing
                  | otherwise -> Just idx

unsafeInsert :: Ord k => k -> Int -> [k] -> ([k], Int, Int)
unsafeInsert k len ks =
  let (lesser, rest) = span (\(key, i) -> key < k) $ ks `zip` [0..]
  in case rest of
       [] -> (ks ++ [k], len, len + 1)
       (k', idx):_ | k == k' -> (ks, idx, len)
                   | otherwise -> (map fst lesser ++ k:(map fst rest), idx, len + 1)

tripart :: Int -> [a] -> ([a], a, [a])
tripart n xs =
  let (first, middle:last) = splitAt n xs
  in (first, middle, last)

splitOverflowingNode :: BTree k -> (BTree k, k, BTree k)
splitOverflowingNode btree =
  let ord = order btree
      (fk, mk, lk) = tripart ord (keys btree)
      bijust (x, y) = (Just x, Just y)
      (fc, lc) = maybe (Nothing, Nothing) (bijust . splitAt (ord+1)) (children btree)
  in ( btree{n = ord, keys = fk, children = fc}
     , mk
     , btree{n = ord, keys = lk, children = lc}
     )

uncurry3 f = \(x, y, z) -> f x y z
