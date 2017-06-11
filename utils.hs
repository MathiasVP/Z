module Utils where
import Control.Monad
import qualified Data.Map as Map
import qualified Data.List as List
import Data.Map(Map)
import Control.Monad.Trans.Maybe

concatMapM :: (Monad m) => (a -> m [b]) -> [a] -> m [b]
concatMapM f xs = fmap List.concat (mapM f xs)

foldlWithKeyM :: Monad m => (a -> k -> b -> m a) -> a -> Map k b -> m a
foldlWithKeyM f acc = Map.foldlWithKey f' (return acc)
    where
        f' ma k b = ma >>= \a -> f a k b

mapWithKeyM :: (Monad m, Ord k) => (k -> a -> m b) -> Map k a -> m (Map k b)
mapWithKeyM f = foldlWithKeyM g Map.empty
  where g m k v = f k v >>= \v' -> return (Map.insert k v' m)

findM :: (Monad m) => (a -> m (Maybe b)) -> [a] -> m (Maybe b)
findM f = runMaybeT . msum . map (MaybeT . f)

ifM :: Monad m => m Bool -> m a -> m a -> m a
ifM mb mThen mElse = do
  b <- mb
  if b then mThen else mElse
