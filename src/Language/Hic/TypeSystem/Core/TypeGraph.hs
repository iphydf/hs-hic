{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE PatternSynonyms     #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections       #-}

{- |
Module      : Language.Hic.TypeSystem.Core.TypeGraph
Description : Graph representation of equi-recursive C types.

This module implements the "Rigorous, Total Type Solver" architectural vision.
It represents C types as finite directed graphs of "Rigid Nodes".
-}
module Language.Hic.TypeSystem.Core.TypeGraph
    ( -- * Core Types
      TypeGraph
    , pattern TypeGraph
    , NodeId
    , Node
    , Polarity (..)

      -- * Conversion
    , fromTypeInfo
    , toTypeInfo

      -- * Graph Operations
    , productConstruction
    , substitute
    , lfp
    , minimizeGraph
    , normalizeGraph
    , collectTemplateVarsFromGraph
    , tgNodes
    , tgRoot
    , getNode
    )
where

import           Control.Applicative                            ((<|>))
import           Control.Monad                                 (when)
import           Control.Monad.State.Strict                    (get, modify,
                                                                put, runState,
                                                                state)
import           Data.Fix                                      (Fix (..))
import           Data.IntMap.Strict                            (IntMap)
import qualified Data.IntMap.Strict                            as IntMap
import           Data.IntSet                                   (IntSet)
import qualified Data.IntSet                                   as IntSet
import           Data.List                                     (elemIndex)
import           Data.Map.Strict                               (Map)
import qualified Data.Map.Strict                               as Map
import           Data.Set                                      (Set)
import qualified Data.Set                                      as Set
import qualified Data.Text                                     as Text
import           GHC.Generics                                  (Generic)
import qualified Language.Cimple                               as C
import qualified Language.Hic.Core.GraphAlgebra                as GA
import           Language.Hic.Core.TypeSystem                  (Phase (..),
                                                                TemplateId (..),
                                                                TypeInfo)
import qualified Language.Hic.TypeSystem.Core.Base             as TS
import           Language.Hic.TypeSystem.Core.Qualification    (Constness (..),
                                                                Nullability (..),
                                                                Ownership (..),
                                                                QualState (..))
import           Language.Hic.TypeSystem.Core.Transition       (Polarity (..),
                                                                ProductState (..),
                                                                RigidNodeF (..),
                                                                SpecialNode (..),
                                                                ValueStructure (..),
                                                                fromRigid,
                                                                stepTransition,
                                                                toRigid)
import qualified Language.Hic.TypeSystem.Core.Transition.Atoms as Transition

--------------------------------------------------------------------------------
-- Core Types
--------------------------------------------------------------------------------

-- | Type for internal node identifiers in the graph.
type NodeId = GA.NodeId

-- | Internal representation of a type node where children are identified by ID.
type Node p = RigidNodeF (TemplateId p) NodeId

-- | A graph representation of an equi-recursive type.
type TypeGraph p = GA.Graph (RigidNodeF (TemplateId p))

-- | Pattern for deconstructing a TypeGraph into its node map and root ID.
pattern TypeGraph :: IntMap (Node p) -> NodeId -> TypeGraph p
pattern TypeGraph nodes root = GA.Graph nodes root
{-# COMPLETE TypeGraph #-}

tgNodes :: TypeGraph p -> IntMap (Node p)
tgNodes = GA.gNodes

tgRoot :: TypeGraph p -> NodeId
tgRoot = GA.gRoot

-- | Looks up a node in the graph, handling terminal NodeIds.
getNode :: NodeId -> TypeGraph p -> Node p
getNode i (TypeGraph nodes _)
    | i == -1 = RSpecial SUnconstrained
    | i == -2 = RSpecial SConflict
    | otherwise = IntMap.findWithDefault (RSpecial SConflict) i nodes

-- | Identifies nodes that are structurally neutral for the given polarity.
-- A node is neutral if it only leads to identity terminals.
identifyNeutralNodes :: Polarity -> IntMap (Node p) -> IntSet
identifyNeutralNodes pol nodes =
    let initial = IntMap.keysSet $ IntMap.filter (Transition.isIdentityFor pol) nodes
        step seen =
            let new = IntMap.keysSet $ IntMap.filterWithKey (\i n -> i `IntSet.member` seen || isNeutral seen n) nodes
            in if new == seen then seen else step new
        isNeutral seen = \case
            RValue (VPointer r _ _) _ _ -> r `IntSet.member` seen
            RValue (VArray m ds) _ _ -> maybe True (`IntSet.member` seen) m && all (`IntSet.member` seen) ds
            RFunction r ps _ _ -> r `IntSet.member` seen && all (`IntSet.member` seen) ps
            RSpecial s -> Transition.isIdentityFor pol (RSpecial s)
            _ -> False
    in step initial

--------------------------------------------------------------------------------
-- Conversion: Tree <-> Graph
--------------------------------------------------------------------------------

-- | Converts a 'TypeInfo' tree into a 'TypeGraph'.
fromTypeInfo :: (Ord (TemplateId p)) => TypeInfo p -> TypeGraph p
fromTypeInfo t =
    let (rootId, (_, _, m)) = runState (go [] (TS.normalizeType t)) (0, Map.empty, IntMap.empty)
    in TypeGraph m rootId
  where
    go stack ty = do
        (nextId, treeToId, idToNode) <- get
        case Map.lookup ty treeToId of
            Just i -> return i
            Nothing ->
                let rigid = toRigid ty
                in case rigid of
                    Nothing -> return (-2) -- Fallback to Conflict for unsupported types
                    Just r -> case r of
                        RSpecial SUnconstrained -> return (-1)
                        RSpecial SConflict      -> return (-2)
                        RValue (VTemplate (TS.FullTemplate (TS.TIdRec i) Nothing) _ _) _ _
                            | i >= 0 && i < length stack -> return (stack !! i)
                        _ -> do
                            let i = nextId
                            put (nextId + 1, Map.insert ty i treeToId, idToNode)
                            rigid' <- traverse (go (i:stack)) r
                            modify $ \(nextId', treeToId', idToNode') ->
                                (nextId', treeToId', IntMap.insert i rigid' idToNode')
                            return i

-- | Converts a 'TypeGraph' back into a 'TypeInfo' tree.
toTypeInfo :: forall p. TypeGraph p -> TypeInfo p
toTypeInfo (TypeGraph nodes root) = TS.normalizeType $ go [] root
  where
    go _ i | i == -1 = TS.Unconstrained
    go _ i | i == -2 = TS.Conflict
    go stack i = case elemIndex i stack of
        Just depth -> TS.Template (TS.TIdRec depth) Nothing
        Nothing ->
            case IntMap.lookup i nodes of
                Just node -> fromRigid (go (i:stack)) node
                Nothing   -> Fix (TS.UnsupportedF $ Text.pack $ "graph corruption: missing node " ++ show i)

--------------------------------------------------------------------------------
-- Product Construction
--------------------------------------------------------------------------------

-- | Computes the Product Automaton of two graphs, handling variance.
productConstruction :: forall p. (Ord (TemplateId p))
                    => (Node p -> Bool) -- ^ Variables to treat as identities/zeros
                    -> Polarity -> TypeGraph p -> TypeGraph p -> TypeGraph p
productConstruction isVar startPol g1 g2 =
    let structuredTerminals = IntMap.fromList [(-1, RSpecial SUnconstrained), (-2, RSpecial SConflict)]

        (gMerged, r1, r2) = GA.merge structuredTerminals [] (minimizeGraph g1) (minimizeGraph g2)

        neutralJoin = identifyNeutralNodes PJoin (GA.gNodes gMerged)
        neutralMeet = identifyNeutralNodes PMeet (GA.gNodes gMerged)

        isDeepNeutral pol i = case pol of
            PJoin -> i `IntSet.member` neutralJoin
            PMeet -> i `IntSet.member` neutralMeet

        identityNode pol = case pol of
            PJoin -> RSpecial SUnconstrained
            PMeet -> RSpecial SConflict

        hasIdentityQuals pol n =
            let (nullability, ownership, constness) = case n of
                    RValue (VPointer _ n' o') c' _ -> (n', o', c')
                    RValue (VTemplate _ n' o') c' _ -> (n', o', c')
                    RValue _ c' _ -> (QUnspecified, QNonOwned', c')
                    RFunction _ _ c' _ -> (QUnspecified, QNonOwned', c')
                    _ -> (QUnspecified, QNonOwned', QMutable')
            in case pol of
                PJoin -> constness == QMutable' && nullability == QNonnull' && ownership == QNonOwned'
                PMeet -> constness == QConst' && nullability == QNullable' && ownership == QOwned'

        allStates = [ ProductState pol qL qR fc
                    | pol <- [PJoin, PMeet]
                    , qL <- [QualTop, QualLevel1Const, QualLevel1Mutable, QualShielded, QualUnshielded]
                    , qR <- [QualTop, QualLevel1Const, QualLevel1Mutable, QualShielded, QualUnshielded]
                    , fc <- [True, False]
                    ]

        maybeIdentity pol nOther i n =
            let isId = case nOther of
                    RSpecial SUnconstrained -> pol == PJoin
                    RSpecial SConflict      -> pol == PMeet
                    _                       -> False
            in if (isVar n || (isDeepNeutral pol i && hasIdentityQuals pol n)) && not isId
               then identityNode pol
               else n

        combineGA i j ps =
            let n1Raw = getGNode i (GA.gNodes gMerged)
                n2Raw = getGNode j (GA.gNodes gMerged)
                pol = psPolarity ps
                n1 = maybeIdentity pol n2Raw i n1Raw
                n2 = maybeIdentity pol n1Raw j n2Raw
                lookupNode idx = Just $ getGNode idx (GA.gNodes gMerged)
                getQuals idx = case getGNode idx (GA.gNodes gMerged) of
                    RValue (VPointer _ n o) c _ -> (n, o, c)
                    RValue (VTemplate _ n o) c _ -> (n, o, c)
                    RValue _ c _ -> (QUnspecified, QNonOwned', c)
                    _ -> (QUnspecified, QNonOwned', QMutable')
                isStrictlyIdentical = (i == j) || (isDeepNeutral pol i && isDeepNeutral pol j)
            in stepTransition ps lookupNode getQuals (-1, -2) isStrictlyIdentical n1 n2

        startState = ProductState startPol QualTop QualTop False
        gRes = GA.universalProduct combineGA structuredTerminals [] allStates gMerged { GA.gRoot = r1 } gMerged { GA.gRoot = r2 } startState
    in gRes
  where
    getGNode idx nodes
        | idx == -1 = RSpecial SUnconstrained
        | idx == -2 = RSpecial SConflict
        | otherwise = IntMap.findWithDefault (RSpecial SConflict) idx nodes

--------------------------------------------------------------------------------
-- Symbolic Operations
--------------------------------------------------------------------------------

-- | Substitutes a template variable with another graph.
substitute :: forall p. (Ord (TemplateId p)) => TS.FullTemplate p -> TypeGraph p -> TypeGraph p -> TypeGraph p
substitute v vGraph (TypeGraph nodes root) =
    let (newRoot, (_, _, newNodes)) = runState (go root) (0, Map.empty, IntMap.empty)
    in normalizeGraph $ TypeGraph newNodes newRoot
  where
    vGraph' = normalizeGraph vGraph
    v' = TS.voidFullTemplate v

    go i | i < 0 = return i
    go i = do
        (_, o2n, _) <- get
        case Map.lookup i o2n of
            Just i' -> return i'
            Nothing -> do
                let node = IntMap.findWithDefault (RSpecial SConflict) i nodes
                case node of
                    RValue (VTemplate ft n o) c s | TS.voidFullTemplate ft == v' -> do
                        i' <- mergeVGraph vGraph'
                        -- Propagate qualifiers from the host template node to the
                        -- substitution graph's root so they are not silently dropped.
                        let applyNO (VPointer a n' o')  = VPointer a (max n n') (max o o')
                            applyNO (VTemplate ft' n' o') = VTemplate ft' (max n n') (max o o')
                            applyNO v'                  = v'
                            applyQ = \case
                                RValue v' c' s' -> RValue (applyNO v') (max c c') (s <|> s')
                                RFunction r ps c' s' -> RFunction r ps (max c c') (s <|> s')
                                nd -> nd
                        when (i' >= 0) $
                            modify $ \(nId, o2n', acc) -> (nId, o2n', IntMap.adjust applyQ i' acc)
                        modify $ \(nId, o2n', acc) -> (nId, Map.insert i i' o2n', acc)
                        return i'
                    _ -> do
                        i' <- state $ \(nId, o2n', acc) -> (nId, (nId + 1, Map.insert i nId o2n', acc))
                        node' <- traverse go node
                        modify $ \(nId, o2n', acc) -> (nId, o2n', IntMap.insert i' node' acc)
                        return i'

    mergeVGraph graph = do
        (idOffset, o2n, acc) <- get
        let vNodes = tgNodes graph
            vRoot = tgRoot graph
            shift id' | id' < 0 = id'
                      | otherwise = id' + idOffset
            shiftedNodes = IntMap.fromList [ (shift k, fmap shift n) | (k, n) <- IntMap.toList vNodes ]
        put (idOffset + IntMap.size shiftedNodes, o2n, IntMap.union acc shiftedNodes)
        return (shift vRoot)

-- | Computes the Least Fixed Point (LFP) for an equi-recursive type equation X = f(X).
lfp :: TS.FullTemplate p -> TypeGraph p -> TypeGraph p
lfp v (TypeGraph nodes root) =
    let v' = TS.voidFullTemplate v
        vNodes = IntMap.filter (\case { RValue (VTemplate ft _ _) _ _ -> TS.voidFullTemplate ft == v'; _ -> False }) nodes
        newRoot = if root `IntMap.member` vNodes then (-1) else root
        sub i | i `IntMap.member` vNodes = newRoot
              | otherwise = i
        newNodes = IntMap.map (fmap sub) nodes
        finalNodes = foldr IntMap.delete newNodes (IntMap.keys vNodes)
    in normalizeGraph $ TypeGraph finalNodes newRoot

--------------------------------------------------------------------------------
-- Minimization and Normalization
--------------------------------------------------------------------------------

-- | Minimizes a 'TypeGraph' using Moore's Algorithm.
minimizeGraph :: forall p. (Ord (TemplateId p)) => TypeGraph p -> TypeGraph p
minimizeGraph (TypeGraph nodes root) =
    let structuredTerminals = IntMap.fromList [(-1, RSpecial SUnconstrained), (-2, RSpecial SConflict)]
        normNodes = IntMap.map stripLexeme nodes
    in normalizeGraph $ GA.minimize structuredTerminals [] (TypeGraph normNodes root)

-- | Strips source positions from lexemes in a type node.
stripLexeme :: RigidNodeF tid a -> RigidNodeF tid a
stripLexeme = \case
    RValue v c s -> RValue (stripStructure v) c (fmap stripL s)
    RFunction r ps c s -> RFunction r ps c (fmap stripL s)
    n -> n
  where
    stripL (C.L _ cl t) = C.L (C.AlexPn 0 0 0) cl t
    stripStructure = \case
        VTypeRef r l args -> VTypeRef r (stripL l) args
        VExternal l -> VExternal (stripL l)
        VIntLit l -> VIntLit (stripL l)
        VNameLit l -> VNameLit (stripL l)
        VEnumMem l -> VEnumMem (stripL l)
        s -> s

-- | Collects template variables directly from graph nodes, avoiding the
-- roundtrip through 'toTypeInfo' and 'collectUniqueTemplateVars'.
collectTemplateVarsFromGraph :: TypeGraph p -> [TS.FullTemplate p]
collectTemplateVarsFromGraph (TypeGraph nodes _) =
    [ fmap (\i -> toTypeInfo (TypeGraph nodes i)) ft
    | RValue (VTemplate ft _ _) _ _ <- IntMap.elems nodes
    ]

-- | Normalizes node IDs in a graph to ensure a canonical 'IntMap' representation.
normalizeGraph :: TypeGraph p -> TypeGraph p
normalizeGraph (TypeGraph nodes root) =
    let (newRoot, (_, _, newNodes)) = runState (goNorm root) (0, Map.empty, IntMap.empty)
    in TypeGraph newNodes newRoot
  where
    goNorm i | i < 0 = return i
    goNorm i = do
        (nextId, oldToNew, acc) <- get
        case Map.lookup i oldToNew of
            Just i' -> return i'
            Nothing -> do
                let node = IntMap.findWithDefault (RSpecial SConflict) i nodes
                let i' = nextId
                put (nextId + 1, Map.insert i i' oldToNew, acc)
                node' <- traverse goNorm node
                (nextId', oldToNew', acc') <- get
                put (nextId', oldToNew', IntMap.insert i' node' acc')
                return i'
