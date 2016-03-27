import Parser as P
import qualified TypeInfer as T
import qualified IRGen as IR
import qualified InferFieldOffsets as IFO
import qualified Data.List as List
import Text.Groom

main :: IO ()
main = let path = "../test.z"
       in do content <- readFile path
             case P.parse content of
               Left err -> print err
               Right ast -> do
                 (typed, env, subst) <- T.infer ast
                 let fieldMap = IFO.construct env typed
                 putStrLn (groom typed)
                 putStrLn (groom env)
                 putStrLn (groom subst)
                 --ir <- IR.irGen env typed
                 --print ir