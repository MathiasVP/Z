module CallGraph where

import Types
import TypedAst
import TypeUtils
import qualified Data.Graph.Inductive.Graph as Gr
import Data.Graph.Inductive.PatriciaTree(Gr)

newtype CallGraph = CallGraph (Gr Identifier ())

construct :: Env -> [TypedDecl] -> CallGraph
construct env decl = CallGraph $ Gr.empty