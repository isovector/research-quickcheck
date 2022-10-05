{-# LANGUAGE RankNTypes         #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DataKinds #-}

module Lib where

import Test.QuickCheck.Checkers
import Control.Lens hiding (Empty, elements, reversed)
import Test.QuickCheck
import GHC.IO (unsafePerformIO)
import Data.List (partition)
import Data.Int (Int8)
import System.IO.Silently
import Unsafe.Coerce (unsafeCoerce)
import GHC.Exts (Any)
import Data.Function (on)
import Data.Foldable (toList)
import GHC.TypeLits
import Data.Proxy (Proxy(Proxy))

isSorted :: (a -> a -> Bool) -> [a] -> Bool
isSorted f as = and $ zipWith f as $ tail as

suchThatP :: forall a. Gen a -> (a -> Property) -> Gen a
suchThatP g p = unsafePerformIO $! silence $! go 1000
  where
    go :: Int -> IO (Gen a)
    go 0 = pure discard
    go n = do
      !a <- generate g
      !r <- quickCheckResult (p a)
      case r of
        Success{} -> pure $! pure a
        _ -> go (n - 1)
{-# NOINLINE suchThatP #-}

genTrans :: ( Show a, Arbitrary a, CoArbitrary a) => Gen (a -> a -> Bool)
genTrans = suchThatP arbitrary isTrans


isTrans :: ( Show a, Arbitrary a) => (a -> a -> Bool) -> Property
isTrans f = property $ \a b c -> (f a b && f b c) ==> f a c


sort :: (a -> a -> Bool) -> [a] -> [a]
sort _ [] = []
sort f (a : as) =
  let (rs, ls) = partition (f a) as
   in sort f ls ++ (a : sort f rs)

fiddle :: Traversable t => (forall x. [x] -> [x]) -> t a -> t a
fiddle f = partsOf traversed %~ f


rotateL :: Int -> [a] -> [a]
rotateL n as
  | n >= length as = as
  | otherwise = reversed (take n) as ++ take (length as - n) as

rotateR :: Int -> [a] -> [a]
rotateR n as
  | n >= length as = as
  | otherwise = drop n as ++ reversed (take n) as

swapHead :: [a] -> [a]
swapHead (a : b : as) = b : a : as
swapHead as = as

duplicateHead :: [a] -> [a]
duplicateHead (a : _ : as) = a : a : as
duplicateHead as = as


reversed :: ([a] -> [a]) -> [a] -> [a]
reversed f = reverse . f . reverse


makeBug :: Traversable t => (a -> t b) -> Gen (a -> t b)
makeBug f = fmap (. f) $ oneof
  [ pure $ fiddle swapHead
  , pure $ fiddle $ reversed swapHead
  , pure $ fiddle duplicateHead
  , pure $ fiddle $ reversed duplicateHead
  , do
      n <- elements [1..5]
      pure $ fiddle $ rotateL n
  , do
      n <- elements [1..5]
      pure $ fiddle $ rotateR n
  , do
      n <- elements [1..5]
      pure $ fiddle $ rotateR n . swapHead . rotateL n
  ]


checkSort :: (Show a, Arbitrary a, EqProp a) => (a -> a -> Bool) -> ((a -> a -> Bool) -> [a] -> [a]) -> Property
checkSort f sort' = sort f =-= sort' f

checkInsert :: (Show a, Arbitrary a, EqProp a) => (a -> a -> Bool) -> ((a -> a -> Bool) -> [a] -> BST a -> BST a) -> Property
checkInsert f insertMany' = property $ do
  as <- genBST f arbitrary
  pure $ (\z -> insertMany f z as) =-= (\z -> insertMany' f z as)

isInsert :: (a -> a -> Bool) -> ((a -> a -> Bool) -> [a] -> BST a -> BST a) -> [a] -> Bool
isInsert f ins as = isSorted f $ toList $ ins f as Empty

instance EqProp Int8 where
  (=-=) = (===)


main :: IO ()
main = do
  bad_sort' <- fmap curry $ generate $ makeBug $ uncurry $ sort @Any
  let bad_sort :: forall x. (x -> x -> Bool) -> [x] -> [x]
      bad_sort = unsafeCoerce bad_sort'
  f <- generate genTrans
  quickCheck $ checkSort @Bool f bad_sort
  quickCheck $ checkSort @Int8 (<=) bad_sort
  quickCheck $ checkSort @Int divmod bad_sort

  bad_insert' <- fmap curry3 $ generate $ makeBug $ uncurry3 $ insertMany @Any
  let bad_insert :: forall x. (x -> x -> Bool) -> [x] -> BST x -> BST x
      bad_insert = unsafeCoerce bad_insert'

  quickCheck $ validBSTGen @Int (<=)
  quickCheck $ validBSTGen @Int divmod


  putStrLn "--------------------------------------------------------------------------------"
  putStrLn "check insert"
  putStrLn "--------------------------------------------------------------------------------"
  -- quickCheck $ isInsert @Bool f insertMany
  quickCheck $ isInsert @Bool (<=) insertMany
  quickCheck $ isInsert @Int8 (<=) insertMany
  quickCheck $ isInsert @Int (<=) insertMany
  quickCheck $ isInsert @(Fin 8) (<=) insertMany
  quickCheck $ isInsert @(Fin 32) (<=) insertMany


  putStrLn "--------------------------------------------------------------------------------"
  -- quickCheck $ checkInsert @Bool f bad_insert
  quickCheck $ checkInsert @Bool (<=) bad_insert
  quickCheck $ checkInsert @Int8 (<=) bad_insert
  quickCheck $ checkInsert @Int (<=) bad_insert
  quickCheck $ checkInsert @(Fin 8) (<=) bad_insert
  quickCheck $ checkInsert @(Fin 32) (<=) bad_insert

-- notes:
--  - we can even find bugs instantiating sort at bool
--  - the smaller the type, the longer it takes for QC to find bugs. makes
--    sense; generators are less likely to overlap

-- questions at this point:
--  - does parametricity let us come up with interesting transitive functions? i think no
--  - can we use the trans function's type to synthesize an appropriate type to monomorphize at?


divmod :: Int -> Int -> Bool
divmod _ 0 = False
divmod 0 _ = True
divmod a b = mod b a == 0



data BST a where
  Empty :: BST a
  Node :: BST a -> a -> BST a -> BST a
  deriving (Eq, Ord, Show, Foldable, Traversable, Functor)


insert :: (a -> a -> Bool) -> a -> BST a -> BST a
insert _ a Empty = Node Empty a Empty
insert f a (Node l a' r)
  | f a a' = Node (insert f a l) a' r
  | otherwise = Node l a' (insert f a r)

insertMany :: (a -> a -> Bool) -> [a] -> BST a -> BST a
insertMany f as b = foldr (insert f) b as

genBST :: (a -> a -> Bool) -> Gen a -> Gen (BST a)
genBST f g = do
  as <- listOf g
  pure $ insertMany f as Empty

validBSTGen :: Arbitrary a => (a -> a -> Bool) -> Property
validBSTGen f = property $ do
  bst <- genBST f arbitrary
  pure $ isSorted f $ toList bst

instance EqProp a => EqProp (BST a) where
  (=-=) = (=-=) `on` toList

uncurry3 :: (a -> b -> c -> d) -> (a, b, c) -> d
uncurry3 fabcd (a, b, c) = fabcd a b c

curry3 :: ((a, b, c) -> d) -> a -> b -> c -> d
curry3 f a b c = f (a, b, c)


newtype Fin (n :: Nat) = Fin { getFin8 :: Int }
  deriving Show

instance Arbitrary (Fin n) where
  arbitrary = Fin <$> arbitrary

instance KnownNat n => Eq (Fin n) where
  (==) = (==) `on` flip mod (natVal $ Proxy @n) . fromIntegral . getFin8

instance KnownNat n => Ord (Fin n) where
  compare = compare `on` flip mod (natVal $ Proxy @n) . fromIntegral . getFin8


instance KnownNat n => EqProp (Fin n) where
  (=-=) = (===)

