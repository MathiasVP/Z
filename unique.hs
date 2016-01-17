{-# LANGUAGE DeriveDataTypeable #-}

module Unique(unique, UniqueInt) where
import Data.IORef
import Data.Global
import Data.Typeable

newtype UniqueInt = UniqueInt Int
  deriving (Typeable, Eq, Ord)

instance Show UniqueInt where
  show (UniqueInt n) = show n
  
counter :: IORef UniqueInt
counter = declareIORef "unique-counter" (UniqueInt 0)

unique :: IO UniqueInt
unique = do
  counter' <- readIORef counter
  modifyIORef counter (\(UniqueInt n) -> UniqueInt (n+1))
  return counter'