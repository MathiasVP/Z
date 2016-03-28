module CubicSolver where

import Prelude hiding ((++))
import qualified Data.Vector as Vector
import Data.Vector((!?), (//), (++), Vector)
import qualified Data.List as List
import qualified Data.Map as Map
import Data.Map(Map, (!))
import qualified Data.Set as Set
import Data.Set(Set)
import qualified Data.Graph.Inductive.Graph as Gr
import Data.Graph.Inductive.Graph((&))
import Data.Graph.Inductive.PatriciaTree(Gr)

newtype Token a = Token a
  deriving (Ord, Eq, Show)
newtype Variable a = Variable a
  deriving (Ord, Eq, Show)

newtype Node a b = Node (Variable b, BitVector b)
  deriving Show

type BitVector b = Vector (Bool, [(Variable b, Variable b)])
type Pos = Int

data Instance a b = Instance (Gr (Node a b) ())
                             (Map (Token a) Pos)
                             (Map Pos (Token a))
                             (Map (Variable b) Gr.Node)
  deriving Show
  
empty :: Instance a b
empty = Instance Gr.empty Map.empty Map.empty Map.empty
  
zeroBitsOfLength :: Int -> BitVector b
zeroBitsOfLength k = Vector.replicate k (False, [])

zeroBits :: Instance a b -> BitVector b
zeroBits inst = zeroBitsOfLength (bitlength inst)

insertNode :: Ord b => Variable b -> Instance a b -> (Gr.Node, Instance a b)
insertNode v inst@(Instance gr tokmap invtokmap varmap) =
  (n, Instance (Gr.insNode (n, node) gr) tokmap invtokmap varmap')
  where n = Gr.noNodes gr
        node = Node (v, zeroBits inst)
        varmap' = Map.insert v n varmap

nodeOf :: Ord b => Variable b -> Instance a b -> (Gr.Node, Instance a b)
nodeOf v inst@(Instance _ _ _ m) =
  case Map.lookup v m of
    Just node -> (node, inst)
    Nothing -> insertNode v inst

posOf :: Ord a => Token a -> Instance a b -> (Pos, Instance a b)
posOf t inst@(Instance gr tokmap invtokmap varmap) =
  case Map.lookup t tokmap of
    Just p -> (p, inst)
    Nothing -> (p, inst')
      where p = Map.size tokmap
            inst' = Instance gr (Map.insert t p tokmap)
                                (Map.insert p t invtokmap)
                                varmap

bitvectorOf :: Ord b => Variable b -> Instance a b ->
                 (BitVector b, Instance a b)
bitvectorOf v inst = (bits, inst')
  where (node, inst'@(Instance gr _ _ _)) = nodeOf v inst
        (Just (_, _, Node (_, bits), _), _) = Gr.match node gr
  
bitlength :: Instance a b -> Int
bitlength (Instance _ tokmap _ _) = Map.size tokmap

isSet :: (Ord a, Ord b) => Variable b -> Token a ->
           Instance a b -> (Bool, Instance a b)
isSet v t inst =
  case bits !? p of
    Just (b, _) -> (b, inst'')
    Nothing -> (False, inst'')
  where (p, inst') = posOf t inst
        (bits, inst'') = bitvectorOf v inst'
        
pairs :: (Ord a, Ord b) => Variable b -> Token a -> Instance a b ->
           ([(Variable b, Variable b)], Instance a b)
pairs v t inst = (snd $ entry bits p, inst'')
  where (p, inst') = posOf t inst
        (bits, inst'') = bitvectorOf v inst'
        
insertPair :: (Ord a, Ord b) => (Variable b, Variable b) -> Variable b ->
                Token a -> Instance a b -> Instance a b
insertPair pair v t inst =
  let (Just (to, _, _, from), gr') = Gr.match node gr
  in Instance ((to, node, Node (v, bits'), from) & gr') tokmap invtokmap varmap
    where (node, inst') = nodeOf v inst
          (p, inst'') = posOf t inst'
          (bits, inst'''@(Instance gr tokmap invtokmap varmap)) =
            bitvectorOf v inst''
          bits' = case bits !? p of
                    Just (b, pairs) -> bits // [(p, (b, pair : pairs))]
                    Nothing         ->
                      let n = Vector.length bits
                          diff = bitlength inst''' - n
                          bits' = bits ++ zeroBitsOfLength diff
                      in bits' // [(p, (False, [pair]))]
          
entry :: BitVector b -> Pos -> (Bool, [(Variable b, Variable b)])
entry bits p =
  case bits !? p of
    Just e  -> e
    Nothing -> (False, [])

set :: (Ord a, Ord b) => Variable b -> Token a -> Instance a b -> Instance a b
set v t inst =
  let (Just (to, _, _, from), gr') = Gr.match node gr
  in Instance ((to, node, Node (v, bits'), from) & gr') tokmap invtokmap varmap
  where (node, inst') = nodeOf v inst
        (p, inst'') = posOf t inst'
        n = Vector.length bits
        (bits, inst'''@(Instance gr tokmap invtokmap varmap)) =
          bitvectorOf v inst''
        bits' = if n > p then
                  bits // [(p, (True, []))]
                else let diff = (bitlength inst''' - n)
                         bits' = bits ++ zeroBitsOfLength diff
                     in bits' // [(p, (True, []))]
         
insertEdge :: Ord b => (Variable b, Variable b) -> Instance a b -> Instance a b
insertEdge (src, dst) inst =
  Instance (Gr.insEdge (from, to, ()) gr) tokmap invtokmap varmap
  where (from, inst') = nodeOf src inst
        (to, inst''@(Instance gr tokmap invtokmap varmap)) = nodeOf dst inst'

data Constraint a b
  = Membership (Token a) (Variable b)
  | Inclusion (Variable b) (Variable b)
  | CondInclusion (Token a) (Variable b) (Variable b) (Variable b)
  
newtype Solution a b = Solution (Map (Variable b) (Set (Token a)))
  deriving Show

constraint :: (Ord a, Ord b) => Constraint a b ->
                   Instance a b -> Instance a b
constraint (Membership t v) inst = List.foldr insertEdge inst'' ps
  where inst' = set v t inst
        (ps, inst'') = pairs v t inst'
constraint (Inclusion x y) inst =
  insertEdge (x, y) inst
constraint (CondInclusion t v x y) inst =
  case isSet v t inst of
    (True, inst') -> insertEdge (x, y) inst'
    (False, inst') -> insertPair (x, y) v t inst'

solution :: (Ord b, Ord a) => Instance a b -> Solution a b
solution (Instance gr tokmap invtokmap varmap) =
  Solution $ Map.foldrWithKey extract Map.empty varmap
  where
    extract var node =
      let (Just (_, _, Node (_, bits), _), _) = Gr.match node gr
      in Map.insert var (Set.unions . Vector.toList $ Vector.imap tokens bits)
      
    tokens p (True, _) = Set.singleton $ invtokmap ! p
    tokens _ (False, _) = Set.empty