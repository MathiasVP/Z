import Parser as P
import qualified TypeInfer as T
--import qualified LLTranslate as LL
--import qualified InferFieldOffsets as IFO
--import qualified CallGraph as CG
import Text.Groom

main :: IO ()
main = let path = "test.z"
       in do content <- readFile path
             case P.parse content of
               Left err -> print err
               Right ast -> do
                 putStrLn (groom ast)
                 putStrLn ""
                 (typed, env, _) <- T.infer ast
                 putStrLn (groom typed)
                 --ll <- LL.translate env typed
                 --putStrLn (groom ll)
                 --let cg = CG.construct env funcs typed
                 --putStrLn (groom cg)
                 --let fieldMap = IFO.construct env typed
                 --putStrLn (groom typed)
                 --putStrLn (groom fieldMap)
                 --ir <- IR.irGen env typed
                 --print ir
