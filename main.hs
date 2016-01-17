import Parser as P
import qualified TypeInfer as T
import qualified IRGen as IR
import Control.Monad.Trans.Writer.Lazy
import qualified Data.List as List

main :: IO ()
main = let path = "../test.z"
       in do content <- readFile path
             case P.parse content of
               Left err -> print err
               Right ast -> do
                 (typed, env, subst) <- T.infer ast
                 ir <- IR.irGen env typed
                 print ir