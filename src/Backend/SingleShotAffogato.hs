{-# HLINT ignore "Use lambda-case" #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Backend.SingleShotAffogato where

import Backend.Milkremover
import Data.Bifunctor (first, second)
import Data.List (intersect, mapAccumL, sort, sortBy, union, find)
import qualified Data.Map as Map
import Data.Maybe (catMaybes, fromJust, fromMaybe, isJust, mapMaybe)
import qualified Data.Set as Set
import qualified Frontend.Typechecker as Typechecker
import Latte.Abs (Ident(Ident), Type' (..))

lookupik2 m k = case Map.lookup k m of
  Just v -> v
  Nothing -> error $ "lookupik2: " ++ show k ++ " not found in " ++ show m

data CoffeFlowGraph = CFG
  { blocks :: Map.Map Label EspressoBlock,
    preds :: Map.Map Label [Label],
    succs :: Map.Map Label [Label]
  }

instance Show CoffeFlowGraph where
  show (CFG b p s) = "Blocks: " ++ show b ++ "\nPredecessors: " ++ show p ++ "\nSuccessors: " ++ show s ++ "\n"

makeAffogato :: Espresso -> Espresso
makeAffogato esp = esp {functions = Map.mapWithKey (makeAffogatoMethod cls rets) (functions esp)}
  where
    rets = Map.map retType (functions esp) `Map.union` builtinMthET
    cls = classes esp

makeAffogatoMethod :: ClMap -> Map.Map Label EspressoType -> Label -> Method -> Method
makeAffogatoMethod cls rets name m = m {body = body', types = types'}
  where
    cfg = makeCFG m
    df = computeDominanceFrontier cfg $ computeImmediateDominators cfg (computeDominators cfg)
    phi = renameVariables $ placePhiNodes cfg df
    body' = linearizeCFG $ coffeTamping phi
    ts = types m
    argtypes = Map.fromList $ mapMaybe (\n -> case  ts Map.!? n of { Nothing -> Nothing; Just t -> Just (n, t)}) (args m)
    types' = fst $ until (\(m', s) -> s == Map.size m') aux (argtypes, -1)
    aux (m', _) = (foldl gatherTypes m' body', Map.size m')
    gatherTypes m' (ADD s (L str) _) = case m' Map.!? str of
      Nothing -> m'
      Just et -> Map.insert s et m'
    gatherTypes m' (ADD s (V va) _) = case va of
      VInt _ -> Map.insert s EI32 m'
      VString _ -> Map.insert s EStr m'
      _ -> error $ "Addition of " ++ show va ++ " not supported"
    gatherTypes m' (SUB s _ _) = Map.insert s EI32 m'
    gatherTypes m' (MUL s _ _) = Map.insert s EI32 m'
    gatherTypes m' (DIV s _ _) = Map.insert s EI32 m'
    gatherTypes m' (MOD s _ _) = Map.insert s EI32 m'
    gatherTypes m' (NEG s _) = Map.insert s EI32 m'
    gatherTypes m' (AND s _ _) = Map.insert s EI1 m'
    gatherTypes m' (OR s _ _) = Map.insert s EI1 m'
    gatherTypes m' (NOT s _) = Map.insert s EI1 m'
    gatherTypes m' (EQS s _ _) = Map.insert s EI1 m'
    gatherTypes m' (NEQ s _ _) = Map.insert s EI1 m'
    gatherTypes m' (LRT s _ _) = Map.insert s EI1 m'
    gatherTypes m' (LRE s _ _) = Map.insert s EI1 m'
    gatherTypes m' (GRT s _ _) = Map.insert s EI1 m'
    gatherTypes m' (GRE s _ _) = Map.insert s EI1 m'
    gatherTypes m' (PHI s x0) =
      let ts =
            map
              ( \(v, _) -> case v of
                  L str -> m' Map.!? str
                  V (VBool _) -> Just EI1
                  V (VInt _) -> Just EI32
                  V (VString _) -> Just EStr
                  V (VClass x) -> Just (EClass x)
                  V (VNull x) -> Just (EClass x)
              )
              x0
       in case catMaybes ts of
            [] -> m'
            h : _ -> Map.insert s h m'
    gatherTypes m' (CALL s f _) = case rets Map.!? f of 
      Nothing -> let (cl, _) = break (== '.') name in case methodOwner cls f cl of
        Nothing -> error $ "Function " ++ f ++ " not found"
        Just x -> Map.insert s (rets `lookupik2` (x ++ "." ++ f)) m'
      Just t -> Map.insert s t m'
    gatherTypes m' (GET s et f) = case et of
      L str -> case m' Map.!? str of
        Just (EClass x) -> Map.insert s (fields (cls `lookupik2` x) `lookupik2` f) m'
        _ -> m'
      V (VClass x) -> Map.insert s (fields (cls `lookupik2` x) `lookupik2` f) m'
      V (VNull x) -> error "Null pointer exception"
      _ -> m'
    gatherTypes m' (SET et f et') = case et' of
      L s -> case m' Map.!? s of
        Nothing -> case et of
          L str -> case m' Map.!? str of
            Just (EClass x) -> Map.insert s (fields (cls `lookupik2` x) `lookupik2` f) m'
            _ -> m'
          V (VClass x) -> Map.insert s (fields (cls `lookupik2` x) `lookupik2` f) m'
          V (VNull x) -> error "Null pointer exception"
          _ -> m'
        Just t -> m'
      _ -> m'
    gatherTypes m' (NEW s x) = Map.insert s (EClass x) m'
    gatherTypes m' (CAST s ty et) = Map.insert s (EClass ty) m'
    gatherTypes m' (RET et) = case et of
      L s -> case m' Map.!? s of
        Just _ -> m'
        Nothing -> Map.insert s (retType m) m'
      _ -> m'
    gatherTypes m' _ = m'

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

removeEmptyBlocks :: CoffeFlowGraph -> CoffeFlowGraph
removeEmptyBlocks (CFG b p s) = CFG b' p' s'
  where
    empites = Map.foldlWithKey (\s k bl -> if null bl then Set.insert k s else s) Set.empty b
    b1 = Map.filter (not . null) b
    b' = Map.map (filter remEmpty) b1
    p' = Map.map (filter (`Set.notMember` empites)) $ Map.filterWithKey (\k _ -> k `Set.notMember` empites) p
    s' = Map.map (filter (`Set.notMember` empites)) $ Map.filterWithKey (\k _ -> k `Set.notMember` empites) s
    remEmpty (BR str) = str `Set.notMember` empites
    remEmpty _ = True

-- DEAD BLOCK: block with no predecessors, removed by removeDeadBlocks
-- EMPTY BLOCK: block with no instructions, can be removed because it is unreachable
-- BLOCK WITH ONLY JUMP: block only with BR lab instruction, canbe removed and its occurences replaced with lab

removeTrampolines :: CoffeFlowGraph -> CoffeFlowGraph
removeTrampolines (CFG b p s) = removeDeadBlocks $ CFG b''' p s'''
  where
    t1 = Map.foldlWithKey (\m k bl -> if length bl == 1 && isTrampoline bl then Map.insert (target bl) k m else m) Map.empty b
    trampolines = collapsePaths $ Map.filter (/= "Entry") t1
    firsts = Set.fromList $ Map.elems trampolines
    mids = Set.filter (isTrampoline . (b Map.!)) $ Set.fromList $ Map.keys trampolines
    b' = Map.map (map rmTrmp) b
    b'' = Map.filterWithKey (\k _ -> k `Set.notMember` firsts && k `Set.notMember` mids) b'
    b''' = Map.mapKeys (\k -> fromMaybe k $ Map.lookup k trampolines) b''
    s' = Map.map (map (\x -> fromMaybe x $ Map.lookup x trampolines)) s
    s'' = Map.filterWithKey (\k _ -> k `Set.notMember` firsts && k `Set.notMember` mids) s'
    s''' = Map.mapKeys (\k -> fromMaybe k $ Map.lookup k trampolines) s''
    isTrampoline [BR l] = True
    isTrampoline _ = False
    target [BR l] = l
    target _ = error "isTrampoline failed"
    rmTrmp (BR l) = BR $ fromMaybe l $ Map.lookup l trampolines
    rmTrmp (CBR c l1 l2) = CBR c (fromMaybe l1 $ Map.lookup l1 trampolines) (fromMaybe l2 $ Map.lookup l2 trampolines)
    rmTrmp (PHI l vls) = PHI l $ map (\(v, l) -> (v, fromMaybe l $ Map.lookup l trampolines)) vls
    rmTrmp x = x

collapsePaths :: Map.Map Label Label -> Map.Map Label Label
collapsePaths m = Map.map collapse m
  where
    collapse l = maybe l collapse (Map.lookup l m)

computeDominators :: CoffeFlowGraph -> Map.Map Label [Label]
computeDominators (CFG b p s) = fst $ until snd loop (doms, False)
  where
    keys = Map.keys b
    doms = Map.adjust (const ["Entry"]) "Entry" $ Map.map (const keys) b
    loop (doms, ok) =
      let newDom l _ = case p `lookupik2` l of
            [] -> [l]
            ps -> union [l] $ foldl1 intersect $ map (doms Map.!) ps
          doms' = Map.mapWithKey newDom doms
       in (doms', doms == doms')

computeImmediateDominators :: CoffeFlowGraph -> Map.Map Label [Label] -> Map.Map Label (Maybe Label)
computeImmediateDominators (CFG b p s) = Map.mapWithKey f
  where
    f l ds = dft l (Set.singleton l) $ filter (/= l) ds
    dft l v ds =
      if l `elem` ds
        then Just l
        else case p `lookupik2` l of
          [] -> Nothing
          ps -> case filter (`Set.notMember` v) ps of
            [] -> Nothing
            preds ->
              foldr
                ( \pa a -> case a of
                    Nothing -> dft pa (Set.insert pa v) ds
                    _ -> a
                )
                Nothing
                preds

computeDominanceFrontier :: CoffeFlowGraph -> Map.Map Label (Maybe Label) -> Map.Map Label [Label]
computeDominanceFrontier (CFG b p s) idom = foldr f df keys
  where
    keys = Map.keys b
    df = Map.map (const []) b
    f l df = foldr (g l) df $ Just <$> p `lookupik2` l
    g l p df =
      fst $
        until
          (\(_, r) -> r == (idom `lookupik2` l))
          ( \(df, r) -> case r of
              Nothing -> undefined
              Just r -> (adjust df r l, idom `lookupik2` r)
          )
          (df, p)

placePhiNodes :: CoffeFlowGraph -> Map.Map Label [Label] -> CoffeFlowGraph
placePhiNodes (CFG b p s) dF = CFG b' p s
  where
    orig = Map.map getVariables b
    defsites = Map.foldrWithKey (\n v d -> foldr (\a d' -> adjust d' a n) d v) Map.empty orig
    allvars = Set.unions $ Map.elems orig
    b' = fst $ foldr f (b, Map.empty) allvars
    f a (b, phis) = let w = defsites `lookupik2` a in fs3 $ until (\(_, _, w) -> null w) (g a) (b, phis, w)
    g a (b, phis, w) = let n = head w in foldr (h a n) (b, phis, tail w) $ dF `lookupik2` n
    h a n y (b, phis, w) = if y `elem` (phis `lu` a) then (b, phis, w) else (b', phis', w')
      where
        lu a b = fromMaybe Set.empty (Map.lookup b a)
        b' = Map.adjust (PHI a (map (L a,) $ p `lookupik2` y) :) y b
        phis' = adjset phis a y
        w' = if a `elem` (orig `lookupik2` y) then w else y : w

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
      GET str _ _ -> Set.insert str s
      NEW str _ -> Set.insert str s
      _ -> s

renameVariables :: CoffeFlowGraph -> CoffeFlowGraph
renameVariables (CFG b p s) = CFG b' p s
  where
    b' = snd $ dft "Entry" "" Set.empty Map.empty (Map.empty, Map.empty)
    dft l pl v c (h, bls) =
      if Set.member l v
        then let bl = renamePhiLabs pl c (b `lookupik2` l) in (h, addBlock l bl bls)
        else
          let v' = Set.insert l v
              ((c', h'), bl) = mapAccumL (renameInstr pl) (c, h) $ b `lookupik2` l
           in foldr (\_l -> dft _l l v' c') (h', addBlock l bl bls) $ s `lookupik2` l
    addBlock l bl bls = case Map.lookup l bls of
      Nothing -> Map.insert l bl bls
      Just bl' -> Map.insert l (mergePhis bl' bl) bls
    mergePhis =
      zipWith
        ( \old new ->
            ( case (old, new) of
                (PHI s1 es1, PHI _ es2) -> PHI s1 (auxPhi es1 es2)
                _ -> old
            )
        )
    auxPhi = zipWith (\(s1, l1) (s2, l2) -> if isV s1 || '$' `elem` getLabelET s1 then (s1, l1) else (s2, l2))

renameInstr :: Label -> (Map.Map String Int, Map.Map String Int) -> Instruction -> ((Map.Map String Int, Map.Map String Int), Instruction)
renameInstr pl (c, h) instr = case instr of
  ADD s et1 et2 -> aux2 ADD s et1 et2
  SUB s et1 et2 -> aux2 SUB s et1 et2
  MUL s et1 et2 -> aux2 MUL s et1 et2
  DIV s et1 et2 -> aux2 DIV s et1 et2
  MOD s et1 et2 -> aux2 MOD s et1 et2
  AND s et1 et2 -> aux2 AND s et1 et2
  OR s et1 et2 -> aux2 OR s et1 et2
  EQS s et1 et2 -> aux2 EQS s et1 et2
  NEQ s et1 et2 -> aux2 NEQ s et1 et2
  GRT s et1 et2 -> aux2 GRT s et1 et2
  GRE s et1 et2 -> aux2 GRE s et1 et2
  LRT s et1 et2 -> aux2 LRT s et1 et2
  LRE s et1 et2 -> aux2 LRE s et1 et2
  NEG s et -> aux1 NEG s et
  NOT s et -> aux1 NOT s et
  CPY s et -> aux1 CPY s et
  PHI s x0 ->
    let (s', h', c') = next h c s
        x0' =
          map
            ( \(v, l) ->
                if isV v
                  then (v, l)
                  else if l == pl then (L $ curr c (getLabelET v), l) else (v, l)
            )
            x0
     in ((c', h'), PHI s' x0')
  CALL s str ets ->
    let (s', h', c') = next h c s
        ets' = map (modEt c) ets
    in ((c', h'), CALL s' str ets')
  CBR et s str -> let et' = modEt c et in ((c, h), CBR et' s str)
  RET et -> let et' = modEt c et in ((c, h), RET et')
  GET s et str ->
    let et' = modEt c et
        (s', h', c') = next h c s
    in ((c', h'), GET s' et' str)
  SET et s et' ->
    let et'' = modEt c et
        et''' = modEt c et'
    in ((c, h), SET et'' s et''')
  NEW s str -> let (s', h', c') = next h c s in ((c', h'), NEW s' str)
  CAST s ty et -> 
    let et' = modEt c et
        (s', h', c') = next h c s
    in ((c', h'), CAST s' ty et')
  _ -> ((c, h), instr)
  where
    next h c s = case Map.lookup s h of
      Nothing -> (s ++ "$1", Map.insert s 1 h, Map.insert s 1 c)
      Just i -> (s ++ "$" ++ show (i + 1), Map.insert s (i + 1) h, Map.insert s (i + 1) c)
    curr m s = case Map.lookup s m of
      Nothing -> s
      Just i -> s ++ "$" ++ show i
    modEt m (L s) = L $ curr m s
    modEt m v = v
    aux2 f s et1 et2 =
      let (s', h', c') = next h c s
          et1' = modEt c et1
          et2' = modEt c et2
       in ((c', h'), f s' et1' et2')
    aux1 f s et =
      let (s', h', c') = next h c s
          et' = modEt c et
       in ((c', h'), f s' et')

renamePhiLabs :: Label -> Map.Map Label Int -> [Instruction] -> [Instruction]
renamePhiLabs pl c = map renamePhiLab
  where
    renamePhiLab (PHI s x0) =
      let x0' =
            map
              ( \(v, l) ->
                  if isV v
                    then (v, l)
                    else if l == pl then (L $ curr c (getLabelET v), l) else (v, l)
              )
              x0
       in PHI s x0'
    renamePhiLab instr = instr
    curr m s = case Map.lookup s m of
      Nothing -> s
      Just i -> s ++ "$" ++ show i

caffeinePropagation :: CoffeFlowGraph -> CoffeFlowGraph
caffeinePropagation (CFG b p s) = CFG b' p s
  where
    ((b', _), cnt) = until (\((_, fix), cnt) -> fix && cnt > 0) cpStep ((b, True), 0)
    cpStep ((b, _), cnt) = (fs3 $ dft "Entry" Set.empty (b, True, Map.empty), cnt + 1)
    dft l v (b, fix, vals) =
      let v' = Set.insert l v
          ((fix', vals'), bl) = mapAccumL caffeinateInstr (fix, vals) $ b `lookupik2` l
          bl' = catMaybes bl
       in if Set.member l v
            then (Map.insert l bl' b, fix', vals')
            else foldr (`dft` v') (Map.insert l bl' b, fix', vals') $ s `lookupik2` l

caffeinateInstr :: (Bool, Map.Map Label ET) -> Instruction -> ((Bool, Map.Map Label ET), Maybe Instruction)
caffeinateInstr (fix, vals) instr = case instr of
  ADD s et et' -> aux2 ADD addV s et et'
  SUB s et et' -> aux2 SUB subV s et et'
  MUL s et et' -> aux2 MUL mulV s et et'
  DIV s et et' -> aux2 DIV divV s et et'
  MOD s et et' -> aux2 MOD modV s et et'
  AND s et et' -> aux2 AND andV s et et'
  OR s et et' -> aux2 OR orV s et et'
  EQS s et et' -> aux2 EQS eqV s et et'
  NEQ s et et' -> aux2 NEQ neqV s et et'
  GRT s et et' -> aux2 GRT grtV s et et'
  GRE s et et' -> aux2 GRE greV s et et'
  LRT s et et' -> aux2 LRT lrtV s et et'
  LRE s et et' -> aux2 LRE lreV s et et'
  NEG s et -> case et of
    L str -> case vals Map.!? str of
      Nothing -> ((fix, vals), Just instr)
      Just a -> caffeinateInstr (False, vals) $ NEG s a
    V (VInt i) -> ((False, Map.insert s (V $ VInt $ negate i) vals), Nothing)
    _ -> error $ "NEG on non-integer: " ++ show instr
  NOT s et -> case et of
    L str -> case vals Map.!? str of
      Nothing -> ((fix, vals), Just instr)
      Just a -> caffeinateInstr (False, vals) $ NOT s a
    V (VBool b) -> ((False, Map.insert s (V $ VBool $ not b) vals), Nothing)
    _ -> error $ "NOT on non-boolean: " ++ show instr
  CPY s et -> case et of
    L str -> case Map.lookup str vals of
      Nothing -> ((False, Map.insert s et vals), Nothing)
      Just et' -> ((False, Map.insert s et' vals), Nothing)
    V va -> ((False, Map.insert s et vals), Nothing)
  PHI s x0 -> case x0 of
    [] -> ((False, vals), Nothing)
    [(et, pl)] -> ((False, Map.insert s et vals), Nothing)
    xs ->
      let (fix', x0') =
            foldr
              ( \(et, pl) (fix, xs) -> case et of
                  L str -> case vals Map.!? str of
                    Nothing -> (fix, (et, pl) : xs)
                    Just et' -> (False, (et', pl) : xs)
                  V va -> (fix, (V va, pl) : xs)
              )
              (fix, [])
              xs
       in ((fix', vals), Just $ PHI s x0')
  CALL s str ets ->
    let (fix', ets') =
          foldr
            ( \et (fix, ets) -> case et of
                L str -> case vals Map.!? str of
                  Nothing -> (fix, et : ets)
                  Just et' -> (False, et' : ets)
                V va -> (fix, V va : ets)
            )
            (fix, [])
            ets
     in ((fix', vals), Just $ CALL s str ets')
  CBR et s str -> case et of
    L cs -> case vals Map.!? cs of
      Nothing -> ((fix, vals), Just instr)
      Just et' -> case et' of
        V (VBool True) -> ((False, vals), Just $ BR s)
        V (VBool False) -> ((False, vals), Just $ BR str)
        _ -> ((False, vals), Just $ CBR et' s str)
    V (VBool True) -> ((False, vals), Just $ BR s)
    V (VBool False) -> ((False, vals), Just $ BR str)
    _ -> error $ "Non-boolean condition in CBR: " ++ show instr
  RET et -> case et of
    L s -> case vals Map.!? s of
      Nothing -> ((fix, vals), Just instr)
      Just et' -> ((False, vals), Just $ RET et')
    V va -> ((fix, vals), Just instr)
  SET et field et' -> let
    (bet, fix') = case et of
      V va -> (et, fix)
      L s -> case vals Map.!? s of
        Nothing -> (et, fix)
        Just et'' -> (et'', False)
    (bet', fix'') = case et' of
      V va -> (et', fix')
      L s -> case vals Map.!? s of
        Nothing -> (et', fix')
        Just et'' -> (et'', False)
    in ((fix'', vals), Just $ SET bet field bet')
  GET s et field -> let
    (bet, fix') = case et of
      L s -> case vals Map.!? s of
        Nothing -> (et, fix)
        Just et' -> (et', False)
      V va ->  (et, fix) -- Shouldn't happen
    in ((fix', vals), Just $ GET s bet field)
  CAST s ty et -> let
    (bet, fix') = case et of
      L s -> case vals Map.!? s of
        Nothing -> (et, fix)
        Just et' -> (et', False)
      V va ->  (et, fix) -- Shouldn't happen
    in ((fix', vals), Just $ CAST s ty bet)
  _ -> ((fix, vals), Just instr)
  where
    aux2 f f' s et et' = case (et, et') of
      (V va1, V va2) -> ((False, Map.insert s (V $ f' va1 va2) vals), Nothing)
      (V _, L la2) -> case Map.lookup la2 vals of
        Nothing -> ((fix, vals), Just instr)
        Just a -> caffeinateInstr (False, vals) $ f s et a
      (L la1, V _) -> case Map.lookup la1 vals of
        Nothing -> ((fix, vals), Just instr)
        Just a -> caffeinateInstr (False, vals) $ f s a et'
      (L la1, L la2) -> case (Map.lookup la1 vals, Map.lookup la2 vals) of
        (Just a, Just b) -> caffeinateInstr (fix, vals) $ f s a b
        (Just a, Nothing) -> caffeinateInstr (fix, vals) $ f s a (L la2)
        (Nothing, Just b) -> caffeinateInstr (fix, vals) $ f s (L la1) b
        (Nothing, Nothing) -> ((fix, vals), Just instr)

-- Remove unused variables
collectDirtyCups :: CoffeFlowGraph -> CoffeFlowGraph
collectDirtyCups (CFG b p s) = CFG b' p s
  where
    used = Map.foldl addVars Set.empty b
    b' = Map.map removeUnused b
    removeUnused =
      filter
        ( \i -> case i of
            ADD str _ _ -> str `Set.member` used
            SUB str _ _ -> str `Set.member` used
            MUL str _ _ -> str `Set.member` used
            DIV str _ _ -> str `Set.member` used
            MOD str _ _ -> str `Set.member` used
            AND str _ _ -> str `Set.member` used
            OR str _ _ -> str `Set.member` used
            EQS str _ _ -> str `Set.member` used
            NEQ str _ _ -> str `Set.member` used
            GRT str _ _ -> str `Set.member` used
            GRE str _ _ -> str `Set.member` used
            LRT str _ _ -> str `Set.member` used
            LRE str _ _ -> str `Set.member` used
            NEG str _ -> str `Set.member` used
            NOT str _ -> str `Set.member` used
            CPY str _ -> str `Set.member` used
            PHI str _ -> str `Set.member` used
            GET str _ _ -> str `Set.member` used
            NEW str _ -> str `Set.member` used
            CAST str _ _ -> str `Set.member` used
            _ -> True
        )
    addVars =
      foldl
        ( \s i -> case i of
            ADD _ et et' -> addVar et $ addVar et' s
            SUB _ et et' -> addVar et $ addVar et' s
            MUL _ et et' -> addVar et $ addVar et' s
            DIV _ et et' -> addVar et $ addVar et' s
            MOD _ et et' -> addVar et $ addVar et' s
            AND _ et et' -> addVar et $ addVar et' s
            OR _ et et' -> addVar et $ addVar et' s
            EQS _ et et' -> addVar et $ addVar et' s
            NEQ _ et et' -> addVar et $ addVar et' s
            GRT _ et et' -> addVar et $ addVar et' s
            GRE _ et et' -> addVar et $ addVar et' s
            LRT _ et et' -> addVar et $ addVar et' s
            LRE _ et et' -> addVar et $ addVar et' s
            NEG _ et -> addVar et s
            NOT _ et -> addVar et s
            CPY _ et -> addVar et s
            PHI _ x0 -> foldr (\(v, _) -> addVar v) s x0
            CALL _ _ ets -> foldr addVar s ets
            CBR et _ _ -> addVar et s
            RET et -> addVar et s
            GET _ et _ -> addVar et s
            SET et _ et' -> addVar et $ addVar et' s
            CAST _ _ et -> addVar et s
            _ -> s
        )
    addVar et s = case et of L str -> Set.insert str s; V _ -> s

linearizeCFG :: CoffeFlowGraph -> [Instruction]
linearizeCFG (CFG b p s) = concat $ reverse blocksList
  where
    blocksList = fst $ lin "Entry" ([], Set.empty)
    lin lab (acc, v) =
      if Set.member lab v
        then (acc, v)
        else
          let block = LAB lab : (b `lookupik2` lab)
              v' = Set.insert lab v
           in case s `lookupik2` lab of
                [] -> (block : acc, v')
                ss -> foldr lin (block : acc, v') ss

removeDeadBlocks :: CoffeFlowGraph -> CoffeFlowGraph
removeDeadBlocks = aux . aux
  where
    aux cfg =
      makeCFG $
        Method
          { args = [],
            types = Map.empty,
            retType = EVoid,
            body = linearizeCFG cfg
          }

cleanUpAfterDead :: CoffeFlowGraph -> CoffeFlowGraph
cleanUpAfterDead (CFG b p s) = CFG b' p s
  where
    labels = Map.keysSet b
    b' =
      Map.map
        ( map
            ( \case
                PHI str x0 -> PHI str $ filter (\(_, l) -> l `elem` labels) x0
                instr -> instr
            )
        )
        b

killUnreachableStmts :: CoffeFlowGraph -> CoffeFlowGraph
killUnreachableStmts (CFG b p s) = CFG b' p s
  where
    b' = Map.map (\bl -> let (a, b) = break breaks bl in a ++ aux b) b
    breaks (BR _) = True
    breaks (CBR {}) = True
    breaks (RET {}) = True
    breaks VRET = True
    breaks _ = False
    aux (a : _) = [a]
    aux _ = []

globalComputerScientistsElimination :: CoffeFlowGraph -> CoffeFlowGraph
globalComputerScientistsElimination cfg@(CFG b p s) = CFG b' p s
  where
    idom = computeImmediateDominators cfg $ computeDominators cfg
    mdTree = Map.foldlWithKey (\m k v -> Map.insertWith (++) v [k] m) Map.empty idom
    dTree = Map.mapKeys fromJust $ Map.filterWithKey (\k _ -> isJust k) mdTree
    sortedBlocks = Map.map (sortInstr <$>) b
    b' = dft "Entry" (Map.empty, Map.empty) sortedBlocks
    dft lab (etv, vtv) b =
      let ((etv', vtv'), bl) = mapAccumL gcseInstr (etv, vtv) (b `lookupik2` lab)
          bl' = catMaybes bl
       in case dTree Map.!? lab of
            Nothing -> Map.insert lab bl' b
            Just kids -> foldr (\l b -> dft l (etv', vtv') b) (Map.insert lab bl' b) kids

gcseInstr :: (Map.Map Instruction Label, Map.Map Label Label) -> Instruction -> ((Map.Map Instruction Label, Map.Map Label Label), Maybe Instruction)
gcseInstr (etv, vtv) instr = case instr of
  ADD s et et' -> gcse2 ADD s et et'
  SUB s et et' -> gcse2 SUB s et et'
  MUL s et et' -> gcse2 MUL s et et'
  DIV s et et' -> gcse2 DIV s et et'
  MOD s et et' -> gcse2 MOD s et et'
  AND s et et' -> gcse2 AND s et et'
  OR s et et' -> gcse2 OR s et et'
  EQS s et et' -> gcse2 EQS s et et'
  NEQ s et et' -> gcse2 NEQ s et et'
  GRT s et et' -> gcse2 GRT s et et'
  GRE s et et' -> gcse2 GRE s et et'
  LRT s et et' -> gcse2 LRT s et et'
  LRE s et et' -> gcse2 LRE s et et'
  NEG s et -> gcse1 NEG s et
  NOT s et -> gcse1 NOT s et
  CPY s et -> gcse1 CPY s et
  PHI s x0 ->
    let x0' = map (first lookupET) x0
     in case etv Map.!? PHI s x0' of
          Nothing -> ((Map.insert (PHI s x0') s etv, vtv), Just $ PHI s x0')
          Just str -> ((etv, Map.insert s str vtv), Nothing)
  CALL s str ets -> ((etv, vtv), Just $ CALL s str (lookupET <$> ets))
  CBR et s str -> let bet = lookupET et in ((etv, vtv), Just $ CBR bet s str)
  RET et -> let bet = lookupET et in ((etv, vtv), Just $ RET bet)
  GET s et f -> ((etv, vtv), Just $ GET s (lookupET et) f)
  SET et str et' -> ((etv, vtv), Just $ SET (lookupET et) str (lookupET et'))
  CAST s ty et -> ((etv, vtv), Just $ CAST s ty (lookupET et))
  _ -> ((etv, vtv), Just instr)
  where
    gcse2 f s et et' =
      let bet = lookupET et; bet' = lookupET et'
       in case etv Map.!? f "" bet bet' of
            Nothing -> ((Map.insert (f "" bet bet') s etv, vtv), Just $ f s bet bet')
            Just str -> ((etv, Map.insert s str vtv), Nothing)
    gcse1 f s et =
      let bet = lookupET et
       in case etv Map.!? f "" bet of
            Nothing -> ((Map.insert (f "" bet) s etv, vtv), Just $ f s bet)
            Just str -> ((etv, Map.insert s str vtv), Nothing)
    lookupET et = case et of L str -> L $ fromMaybe str $ Map.lookup str vtv; V v -> et

sortInstr :: Instruction -> Instruction
sortInstr (PHI str x0) = PHI str $ sortBy (\(_, l) (_, l') -> compare l l') x0
sortInstr (ADD str et et') = let [et1, et2] = sort [et, et'] in ADD str et1 et2
sortInstr (MUL str et et') = let [et1, et2] = sort [et, et'] in MUL str et1 et2
sortInstr (AND str et et') = let [et1, et2] = sort [et, et'] in AND str et1 et2
sortInstr (OR str et et') = let [et1, et2] = sort [et, et'] in OR str et1 et2
sortInstr (EQS str et et') = let [et1, et2] = sort [et, et'] in EQS str et1 et2
sortInstr (NEQ str et et') = let [et1, et2] = sort [et, et'] in NEQ str et1 et2
sortInstr instr = instr

coffeTamping :: CoffeFlowGraph -> CoffeFlowGraph
coffeTamping cfg = cfg'
  where
    cfg' = snd $ fs3 $ until (\(CFG b _ _, CFG b' _ _, cnt) -> cnt > 0 && b == b') loop (cfg, cfg, 0)
    loop (_, new, cnt) = (new, f new, cnt + 1)
    f =
      globalComputerScientistsElimination
        . killUnreachableStmts
      --  . removeTrampolines
        . removeEmptyBlocks
        . cleanUpAfterDead
        . removeDeadBlocks
        . collectDirtyCups
        . caffeinePropagation

fs3 :: (a, b, c) -> (a, b)
fs3 (a, b, _) = (a, b)

adjust :: Ord k => Map.Map k [a] -> k -> a -> Map.Map k [a]
adjust m k v = if Map.member k m then Map.adjust (v :) k m else Map.insert k [v] m

adjset :: (Ord k, Ord a) => Map.Map k (Set.Set a) -> k -> a -> Map.Map k (Set.Set a)
adjset m k v = if Map.member k m then Map.adjust (Set.insert v) k m else Map.insert k (Set.singleton v) m

addV :: Value -> Value -> Value
addV (VInt i) (VInt j) = VInt $ i + j
addV (VString s) (VString t) = VString $ s ++ t
addV a b = error $ "Cannot add values of types: " ++ show a ++ " and " ++ show b

subV :: Value -> Value -> Value
subV (VInt i) (VInt j) = VInt $ i - j
subV a b = error $ "Cannot subtract values of types: " ++ show a ++ " and " ++ show b

mulV :: Value -> Value -> Value
mulV (VInt i) (VInt j) = VInt $ i * j
mulV a b = error $ "Cannot multiply values of types: " ++ show a ++ " and " ++ show b

divV :: Value -> Value -> Value
divV (VInt i) (VInt j) = VInt $ i `div` j
divV a b = error $ "Cannot divide values of types: " ++ show a ++ " and " ++ show b

modV :: Value -> Value -> Value
modV (VInt i) (VInt j) = VInt $ i `mod` j
modV a b = error $ "Cannot modulo values of types: " ++ show a ++ " and " ++ show b

andV :: Value -> Value -> Value
andV (VBool i) (VBool j) = VBool $ i && j
andV a b = error $ "Cannot AND values of types: " ++ show a ++ " and " ++ show b

orV :: Value -> Value -> Value
orV (VBool i) (VBool j) = VBool $ i || j
orV a b = error $ "Cannot OR values of types: " ++ show a ++ " and " ++ show b

eqV :: Value -> Value -> Value
eqV (VInt i) (VInt j) = VBool $ i == j
eqV (VString s) (VString t) = VBool $ s == t
eqV (VBool b) (VBool c) = VBool $ b == c
eqV a b = error $ "Cannot compare values of types: " ++ show a ++ " and " ++ show b

neqV :: Value -> Value -> Value
neqV (VInt i) (VInt j) = VBool $ i /= j
neqV (VString s) (VString t) = VBool $ s /= t
neqV (VBool b) (VBool c) = VBool $ b /= c
neqV a b = error $ "Cannot compare values of types: " ++ show a ++ " and " ++ show b

grtV :: Value -> Value -> Value
grtV (VInt i) (VInt j) = VBool $ i > j
grtV a b = error $ "Cannot compare values of types: " ++ show a ++ " and " ++ show b

greV :: Value -> Value -> Value
greV (VInt i) (VInt j) = VBool $ i >= j
greV a b = error $ "Cannot compare values of types: " ++ show a ++ " and " ++ show b

lrtV :: Value -> Value -> Value
lrtV (VInt i) (VInt j) = VBool $ i < j
lrtV a b = error $ "Cannot compare values of types: " ++ show a ++ " and " ++ show b

lreV :: Value -> Value -> Value
lreV (VInt i) (VInt j) = VBool $ i <= j
lreV a b = error $ "Cannot compare values of types: " ++ show a ++ " and " ++ show b

isV :: ET -> Bool
isV (V _) = True
isV _ = False

getLabelET :: ET -> Label
getLabelET (L l) = l
getLabelET _ = error "Expected label"

builtinMthET :: Map.Map String EspressoType
builtinMthET = Map.map aux $ Map.mapKeys (\(Ident x) -> x) Typechecker.builtinMethods
  where
    aux = mapType . Typechecker.methodRetType
    mapType (Void _) = EVoid
    mapType (Int _) = EI32
    mapType (Bool _) = EI1
    mapType (Str _) = EStr
    mapType _ = undefined