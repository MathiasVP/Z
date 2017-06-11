{-
  TODO:
  Explicit type variables should not be identified with other variables during
  type inference. i.e. it should not be possible to write a function with the
  type (not counting a possible looping term):

  forall A B.
    fun f (x : A) -> B =
      ...
-}

import Parser as P
import qualified TypeInfer as T
import qualified PPTypedAst as PP
import qualified PPLLAst as PPLL
import qualified LLTranslate as LL
--import qualified InferFieldOffsets as IFO
--import qualified CallGraph as CG

main :: IO ()
main = let path = "test.z"
       in do content <- readFile path
             case P.parse content of
               Left err -> print err
               Right ast -> do
                 (typed, env) <- T.infer ast
                 putStrLn $ PP.ppAst typed
                 --ll <- LL.translate env typed
                 --putStrLn (PPLL.ppLLAst ll)
                 --let cg = CG.construct env funcs typed
                 --putStrLn (groom cg)
                 --let fieldMap = IFO.construct env typed
                 --putStrLn (groom typed)
                 --putStrLn (groom fieldMap)
                 --ir <- IR.irGen env typed
                 --print ir
