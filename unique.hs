module Unique(unique, UniqueInt(UniqueInt)) where
import Data.Unique
import Data.Hashable

newtype UniqueInt = UniqueInt Int
  deriving (Eq, Ord)

instance Show UniqueInt where
  show (UniqueInt n) = show n

instance Hashable UniqueInt where
  hashWithSalt n (UniqueInt uint) =
    hashWithSalt n uint

unique :: IO UniqueInt
unique = do
  u <- newUnique
  return $ UniqueInt $ hashUnique u
