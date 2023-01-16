{-# HLINT ignore "Use lambda-case" #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Backend.SingleShotAffogato where

import Backend.Milkremover
import Data.List (intersect, union)
import qualified Data.Map as Map
import Data.Maybe (fromJust, fromMaybe)
import qualified Data.Set as Set

data CoffeFlowGraph = CFG
  { blocks :: Map.Map Label EspressoBlock,
    preds :: Map.Map Label [Label],
    succs :: Map.Map Label [Label]
  }

instance Show CoffeFlowGraph where
  show (CFG b p s) = "Blocks: " ++ show b ++ "\nPredecessors: " ++ show p ++ "\nSuccessors: " ++ show s ++ "\n"

makeCFG :: Method -> CoffeFlowGraph
makeCFG m =
  CFG
    { blocks = Map.insert lname (reverse bc) blocks,
      preds = preds,
      succs = succs
    }
  where
    labels = map (\(LAB l) -> l) $ filter (\case LAB _ -> True; _ -> False) $ body m
    sm = Map.fromList $ map (,[]) labels
    (blocks, preds, succs, bc, lname) = foldl f (Map.empty, sm, sm, [], "Entry") (tail $ body m)
    f (blocks, preds, succs, bc, name) code = case code of
      (LAB l) -> (Map.insert name (reverse bc) blocks, preds, succs, [], l)
      (BR l) -> (blocks, adjust preds l name, adjust succs name l, code : bc, name)
      (CBR _ l1 l2) ->
        ( blocks,
          adjust (adjust preds l1 name) l2 name,
          adjust (adjust succs name l1) name l2,
          code : bc,
          name
        )
      _ -> (blocks, preds, succs, code : bc, name)

computeDominators :: CoffeFlowGraph -> Map.Map Label [Label]
computeDominators (CFG b p s) = fst $ until snd loop (doms, False)
  where
    keys = Map.keys b
    doms = Map.adjust (const ["Entry"]) "Entry" $ Map.map (const keys) b
    loop (doms, ok) =
      let newDom l _ = case p Map.! l of
            [] -> [l]
            ps -> union [l] $ foldl1 intersect $ map (doms Map.!) ps
          doms' = Map.mapWithKey newDom doms
       in (doms', doms == doms')

computeImmediateDominators :: CoffeFlowGraph -> Map.Map Label [Label] -> Map.Map Label (Maybe Label)
computeImmediateDominators (CFG b p s) = Map.mapWithKey f
  where
    f l ds = dfs l (Set.singleton l) $ filter (/= l) ds
    dfs l v ds =
      if l `elem` ds
        then Just l
        else case p Map.! l of
          [] -> Nothing
          ps -> case filter (`Set.notMember` v) ps of
            [] -> Nothing
            preds ->
              foldr
                ( \pa a -> case a of
                    Nothing -> dfs pa (Set.insert pa v) ds
                    _ -> a
                )
                Nothing
                preds

computeDominanceFrontier :: CoffeFlowGraph -> Map.Map Label (Maybe Label) -> Map.Map Label [Label]
computeDominanceFrontier (CFG b p s) idom = foldr f df keys
  where
    keys = Map.keys b
    df = Map.map (const []) b
    f l df = foldr (g l) df $ Just <$> p Map.! l
    g l p df =
      fst $
        until
          (\(_, r) -> r == (idom Map.! l))
          ( \(df, r) -> case r of
              Nothing -> undefined
              Just r -> (adjust df r l, idom Map.! r)
          )
          (df, p)

placePhiNodes :: CoffeFlowGraph -> Map.Map Label [Label] -> CoffeFlowGraph
placePhiNodes (CFG b p s) dF = CFG b' p s
  where
    orig = Map.map getVariables b
    defsites = Map.foldrWithKey (\n v d -> foldr (\a d' -> adjust d' a n) d v) Map.empty orig
    allvars = Set.unions $ Map.elems orig
    b' = fst $ foldr f (b, Map.empty) allvars
    f a (b, phis) = let w = defsites Map.! a in fs3 $ until (\(_, _, w) -> null w) (g a) (b, phis, w)
    g a (b, phis, w) = let n = head w in foldr (h a n) (b, phis, tail w) $ dF Map.! n
    h a n y (b, phis, w) = if y `elem` (phis `lu` a) then (b, phis, w) else (b', phis', w')
      where
        lu a b = fromMaybe Set.empty (Map.lookup b a)
        b' = Map.adjust (PHI a (map (a,) $ p Map.! y) :) y b
        phis' = adjset phis a y
        w' = if a `elem` (orig Map.! y) then w else y : w

getVariables :: EspressoBlock -> Set.Set String
getVariables = foldr f Set.empty
  where
    f :: Instruction -> Set.Set String -> Set.Set String
    f instr s = case instr of
      ADD str _ _ -> Set.insert str s
      SUB str _ _ -> Set.insert str s
      MUL str _ _ -> Set.insert str s
      DIV str _ _ -> Set.insert str s
      MOD str _ _ -> Set.insert str s
      NEG str _ -> Set.insert str s
      AND str _ _ -> Set.insert str s
      OR str _ _ -> Set.insert str s
      NOT str _ -> Set.insert str s
      EQS str _ _ -> Set.insert str s
      NEQ str _ _ -> Set.insert str s
      GRT str _ _ -> Set.insert str s
      GRE str _ _ -> Set.insert str s
      LRT str _ _ -> Set.insert str s
      LRE str _ _ -> Set.insert str s
      CPY str _ -> Set.insert str s
      CALL str _ _ -> Set.insert str s
      _ -> s

renameVariables :: CoffeFlowGraph -> CoffeFlowGraph
renameVariables (CFG b p s) = undefined

-- reverse makeCFG
-- starting from node "Entry":
--  -- prepend LAB name to block
--  -- add block to accumulator
--  -- repeat for successors
--  -- if no successors, return accumulator, concatenating accordlingly
linearizeCFG :: CoffeFlowGraph -> [Instruction]
linearizeCFG (CFG b p s) = undefined

fs3 :: (a, b, c) -> (a, b)
fs3 (a, b, _) = (a, b)

adjust :: Ord k => Map.Map k [a] -> k -> a -> Map.Map k [a]
adjust m k v = if Map.member k m then Map.adjust (v :) k m else Map.insert k [v] m

adjset :: (Ord k, Ord a) => Map.Map k (Set.Set a) -> k -> a -> Map.Map k (Set.Set a)
adjset m k v = if Map.member k m then Map.adjust (Set.insert v) k m else Map.insert k (Set.singleton v) m