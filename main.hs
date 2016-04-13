import Parser as P
import qualified TypeInfer as T
--import qualified IRGen as IR
import qualified InferFieldOffsets as IFO
import qualified Data.List as List
import qualified Data.Map as Map
import Data.Map(Map, (!))
import qualified CallGraph as CG
import Data.Graph.Inductive.Dot
import Text.Groom

main :: IO ()
main = let path = "../test.z"
       in do content <- readFile path
             case P.parse content of
               Left err -> print err
               Right ast -> do
                 (typed, env) <- T.infer ast
                 let cg = CG.construct env typed
                 putStrLn (groom cg)
                 --let fieldMap = IFO.construct env typed
                 --putStrLn (groom typed)
                 --putStrLn (groom fieldMap)
                 --ir <- IR.irGen env typed
                 --print ir
