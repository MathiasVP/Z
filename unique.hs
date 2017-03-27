{-# LANGUAGE DeriveGeneric #-}

module Unique(unique, UniqueInt(UniqueInt)) where
import Data.Unique
import Data.Hashable
import qualified Debug.Hoed.Pure as Hoed

newtype UniqueInt = UniqueInt Int
  deriving (Eq, Ord, Hoed.Generic)

instance Hoed.Observable UniqueInt

instance Show UniqueInt where
  show (UniqueInt n) = show n

instance Hashable UniqueInt where
  hashWithSalt n (UniqueInt uint) =
    hashWithSalt n uint

unique :: IO UniqueInt
unique = do
  u <- newUnique
  return $ UniqueInt $ hashUnique u
