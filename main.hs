import Parser as P
import TypeInfer as T
import MatchCheck as MC
import Control.Monad.Trans.Writer.Lazy
import qualified Data.List as List

main :: IO ()
main = let path = "../test.z"
       in do content <- readFile path
             case P.parse content of
               Left err -> print err
               Right ast -> do
                 (typed, env, subst) <- T.infer ast
                 let (b, badMatches) = runWriter (MC.matchCheck typed)
                 mapM putStrLn (List.map MC.formatMatchWarning badMatches)
                 case b of
                  True -> return () --Continue compilation
                  False -> return () --Abort compilation