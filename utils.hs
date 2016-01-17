module Utils where
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.State.Lazy
import qualified Data.Map as Map
import qualified Data.List as List
import Data.Map(Map)

concatMapM :: (Monad m) => (a -> m [b]) -> [a] -> m [b]
concatMapM f xs = liftM List.concat (mapM f xs)

foldlWithKeyM :: Monad m => (a -> k -> b -> m a) -> a -> Map k b -> m a
foldlWithKeyM f acc = Map.foldlWithKey f' (return acc)
    where
        f' ma k b = ma >>= \a -> f a k b
        
io :: IO a -> StateT b IO a
io = liftIO