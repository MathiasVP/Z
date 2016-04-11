module Unique(unique, UniqueInt(UniqueInt)) where
import Data.Unique

newtype UniqueInt = UniqueInt Int
  deriving (Eq, Ord)

instance Show UniqueInt where
  show (UniqueInt n) = show n

unique :: IO UniqueInt
unique = do
  u <- newUnique
  return $ UniqueInt $ hashUnique u
