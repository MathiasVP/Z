module Unique(unique) where
import Data.IORef
import Data.Global

counter :: IORef Int
counter = declareIORef "unique-counter" 0

unique :: IO Int
unique = do
  counter' <- readIORef counter
  modifyIORef counter (+1)
  return counter'