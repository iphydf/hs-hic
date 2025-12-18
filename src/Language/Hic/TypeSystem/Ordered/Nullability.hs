{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE StandaloneDeriving    #-}

module Language.Hic.TypeSystem.Ordered.Nullability
    ( NullabilityFacts
    , NullabilityResult (..)
    , runNullabilityAnalysis
    ) where

import           Control.Monad.Identity     (Identity (..))
import           Data.Aeson                 (ToJSON)
import           Data.Fix                   (Fix (..), foldFix, unFix)
import           Data.Foldable              (foldMap, toList)
import           Data.List                  (foldl')
import           Data.Map.Strict            (Map)
import qualified Data.Map.Strict            as Map
import           Data.Maybe                 (fromMaybe, mapMaybe)
import           Data.Set                   (Set)
import qualified Data.Set                   as Set
import           Data.Text                  (Text)
import qualified Data.Text                  as T
import qualified Debug.Trace                as Debug
import           GHC.Generics               (Generic)
import           Language.Cimple            (NodeF (..))
import qualified Language.Cimple            as C
import qualified Language.Cimple.Program    as Program
import           Language.Hic.Core.AstUtils (getAlexPosn, getParamName, getVar,
                                             isNonnullParam, isNonnullType)
import           Language.Hic.Core.DataFlow (CFG, CFGNode (..), DataFlow (..),
                                             buildCFG, fixpoint)

debugging :: Bool
debugging = False

dtrace :: String -> a -> a
dtrace msg x = if debugging then Debug.trace msg x else x

-- | Variables currently known to be non-null.
type NullabilityFacts = Set Text

data NullabilityResult = NullabilityResult
    { nrFunctionFacts  :: Map Text (Map Int NullabilityFacts)
    -- ^ FunctionName -> (CFGNodeID -> Facts)
    , nrStatementFacts :: Map Text (Map C.AlexPosn NullabilityFacts)
    -- ^ FunctionName -> (Position -> Facts)
    } deriving (Show, Generic, ToJSON)

data NullabilityContext l = NullabilityContext
    { ncNonnullParams :: NonnullParams
    }

instance DataFlow Identity NullabilityContext Text NullabilityFacts () where
    emptyFacts _ = return Set.empty
    join _ a b = return $ Set.intersection a b
    transfer ctx _ _ facts stmt = return (transferStmt (ncNonnullParams ctx) facts stmt, Set.empty)

type NonnullParams = Map Text (Set Int)

buildNonnullParamsMap :: Program.Program Text -> NonnullParams
buildNonnullParamsMap program =
    Map.fromList $ concatMap (collectPrototypes . snd) (Program.toList program)
  where
    collectPrototypes nodes = concatMap collectPrototypes' nodes
    collectPrototypes' (Fix node) =
        let rest = concatMap collectPrototypes' (toList node)
        in case node of
            C.FunctionPrototype _ (C.L _ _ name) params ->
                let nonnulls = Set.fromList [ i | (i, p) <- zip [0..] params, isNonnullParam p ]
                in (name, nonnulls) : rest
            _ -> rest

runNullabilityAnalysis :: Program.Program Text -> NullabilityResult
runNullabilityAnalysis program =
    let allNodes = Program.toList program >>= snd
        nnMap = buildNonnullParamsMap program
        results = concatMap (collectFunctions nnMap) allNodes
        funcFacts = Map.fromList $ map (\(n, f, _) -> (n, f)) results
        stmtFacts = Map.fromList $ map (\(n, _, s) -> (n, s)) results
    in NullabilityResult funcFacts stmtFacts
  where
    collectFunctions :: NonnullParams -> C.Node (C.Lexeme Text) -> [(Text, Map Int NullabilityFacts, Map C.AlexPosn NullabilityFacts)]
    collectFunctions nnMap n@(Fix node) =
        let results = concatMap (collectFunctions nnMap) (toList node)
            current = case node of
                C.FunctionDefn _ proto _ ->
                    case getProtoName proto of
                        Just name ->
                            let initialFacts = getInitialFacts proto
                                ctx = NullabilityContext nnMap
                                cfg = runIdentity $ buildCFG ctx n initialFacts :: CFG Text NullabilityFacts
                                (finalCfg, _) = runIdentity $ fixpoint ctx name cfg
                                facts = Map.map cfgInFacts finalCfg
                                sFacts = Map.unions $ map (computeNodeStatementFacts nnMap name) (Map.elems finalCfg)
                            in [(name, facts, sFacts)]
                        Nothing -> []
                _ -> []
        in current ++ results

    getInitialFacts (Fix (C.FunctionPrototype _ _ params)) =
        Set.fromList $ mapMaybe (\p -> if isNonnullParam p then getParamName p else Nothing) params
    getInitialFacts (Fix (C.Commented _ n)) = getInitialFacts n
    getInitialFacts _ = Set.empty

    getProtoName (Fix (C.FunctionPrototype _ (C.L _ _ name) _)) = Just name
    getProtoName (Fix (C.Commented _ n))                        = getProtoName n
    getProtoName _                                              = Nothing

    computeNodeStatementFacts nnMap funcName node =
        snd $ foldl' (\(facts, acc) stmt ->
            let newFacts = transferStmt nnMap facts stmt
                acc' = case getAlexPosn stmt of
                         Just pos ->
                             dtrace ("Nullability STORE: " ++ T.unpack funcName ++ " at " ++ show pos ++ " facts=" ++ show facts) $
                             Map.insert pos facts acc -- Facts BEFORE statement
                         Nothing  -> acc
            in (newFacts, acc')
        ) (cfgInFacts node, Map.empty) (cfgStmts node)

transferStmt :: NonnullParams -> NullabilityFacts -> C.Node (C.Lexeme Text) -> NullabilityFacts
transferStmt nnMap facts stmt@(Fix node) =
    let implicit = extractImplicitNonnull stmt
        facts' = facts <> implicit
        newFacts = case node of
            C.VarDeclStmt (Fix (C.VarDecl _ (C.L _ _ name) _)) mInit ->
                case mInit of
                    Just initExpr -> if isGuaranteedNonnull facts' initExpr
                                     then Set.insert name facts'
                                     else Set.delete name facts'
                    Nothing -> facts'

            C.ExprStmt (Fix (C.AssignExpr (Fix (C.VarExpr (C.L _ _ name))) _ rhs)) ->
                if isGuaranteedNonnull facts' rhs
                then Set.insert name facts'
                else Set.delete name facts'

            C.ExprStmt (Fix (C.FunctionCall (Fix (C.VarExpr (C.L _ _ "__tokstyle_assume_true"))) [cond])) ->
                facts' <> extractVarsFromNonnullCond cond

            C.ExprStmt (Fix (C.FunctionCall (Fix (C.VarExpr (C.L _ _ "__tokstyle_assume_false"))) [cond])) ->
                facts' <> extractVarsFromNullCond cond

            C.ExprStmt (Fix (C.FunctionCall (Fix (C.VarExpr (C.L _ _ name))) args)) ->
                case Map.lookup name nnMap of
                    Just nnIndices ->
                        let calledWithNonnull = Set.fromList [ var | (i, arg) <- zip [0..] args, Set.member i nnIndices, Just var <- [getVar arg] ]
                        in facts' <> calledWithNonnull
                    Nothing -> facts'

            _ -> facts'
    in dtrace ("Nullability TRANSFER: " ++ show (getAlexPosn stmt) ++ " facts=" ++ show facts ++ " -> " ++ show newFacts) newFacts

extractImplicitNonnull :: C.Node (C.Lexeme Text) -> Set Text
extractImplicitNonnull (Fix node) =
    let self = case node of
            C.UnaryExpr C.UopDeref e -> maybe Set.empty Set.singleton (getVar e)
            C.MemberAccess e _ -> maybe Set.empty Set.singleton (getVar e)
            C.PointerAccess e _ -> maybe Set.empty Set.singleton (getVar e)
            C.ArrayAccess e _ -> maybe Set.empty Set.singleton (getVar e)
            C.CastExpr ty e | isNonnullType ty -> maybe Set.empty Set.singleton (getVar e)
            _ -> Set.empty
    in self <> foldMap extractImplicitNonnull node


isGuaranteedNonnull :: NullabilityFacts -> C.Node (C.Lexeme Text) -> Bool
isGuaranteedNonnull facts (Fix node) = case node of
    C.VarExpr (C.L _ _ name) -> Set.member name facts
    C.LiteralExpr C.String _ -> True
    C.UnaryExpr C.UopAddress _ -> True
    C.ParenExpr e -> isGuaranteedNonnull facts e
    C.CastExpr ty e -> isNonnullType ty || isGuaranteedNonnull facts e
    C.FunctionCall (Fix (C.VarExpr (C.L _ _ "malloc"))) _ -> True
    C.FunctionCall (Fix (C.VarExpr (C.L _ _ "realloc"))) _ -> True
    C.LiteralExpr C.ConstId (C.L _ _ "nullptr") -> False
    C.LiteralExpr C.Int (C.L _ _ "0") -> False
    _ -> False

-- | Extract variable names from a condition that, if true, implies the variables are non-null.
extractVarsFromNonnullCond :: C.Node (C.Lexeme Text) -> Set Text
extractVarsFromNonnullCond (Fix node) = case node of
    C.VarExpr (C.L _ _ name) -> Set.singleton name
    C.ParenExpr e -> extractVarsFromNonnullCond e
    C.BinaryExpr lhs C.BopAnd rhs ->
        extractVarsFromNonnullCond lhs <> extractVarsFromNonnullCond rhs
    C.BinaryExpr lhs C.BopNe rhs ->
        case (unFix lhs, unFix rhs) of
            (C.VarExpr (C.L _ _ v), C.LiteralExpr C.ConstId (C.L _ _ "nullptr")) -> Set.singleton v
            (C.LiteralExpr C.ConstId (C.L _ _ "nullptr"), C.VarExpr (C.L _ _ v)) -> Set.singleton v
            (C.VarExpr (C.L _ _ v), C.LiteralExpr C.Int (C.L _ _ "0"))           -> Set.singleton v
            (C.LiteralExpr C.Int (C.L _ _ "0"), C.VarExpr (C.L _ _ v))           -> Set.singleton v
            _ -> Set.empty
    _ -> Set.empty

-- | Extract variable names from a condition that, if false, implies the variables are non-null.
extractVarsFromNullCond :: C.Node (C.Lexeme Text) -> Set Text
extractVarsFromNullCond (Fix node) = case node of
    C.UnaryExpr C.UopNot e -> extractVarsFromNonnullCond e
    C.ParenExpr e -> extractVarsFromNullCond e
    C.BinaryExpr lhs C.BopOr rhs ->
        extractVarsFromNullCond lhs <> extractVarsFromNullCond rhs
    C.BinaryExpr lhs C.BopEq rhs ->
        case (unFix lhs, unFix rhs) of
            (C.VarExpr (C.L _ _ v), C.LiteralExpr C.ConstId (C.L _ _ "nullptr")) -> Set.singleton v
            (C.LiteralExpr C.ConstId (C.L _ _ "nullptr"), C.VarExpr (C.L _ _ v)) -> Set.singleton v
            (C.VarExpr (C.L _ _ v), C.LiteralExpr C.Int (C.L _ _ "0"))           -> Set.singleton v
            (C.LiteralExpr C.Int (C.L _ _ "0"), C.VarExpr (C.L _ _ v))           -> Set.singleton v
            _ -> Set.empty
    _ -> Set.empty
