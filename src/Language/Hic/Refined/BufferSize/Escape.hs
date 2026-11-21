{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData        #-}

-- | Which pointers a function may keep past a call: put somewhere, returned,
-- or given to a function that may keep them. A variable whose address is
-- only given to functions that don't keep it changes only in those calls.
module Language.Hic.Refined.BufferSize.Escape
    ( Keeps
    , keptParams
    , mayKeep
    , addressesKept
    ) where

import           Data.Fix                                (Fix (..))
import           Data.Foldable                           (toList)
import           Data.Map.Strict                         (Map)
import qualified Data.Map.Strict                         as Map
import           Data.Set                                (Set)
import qualified Data.Set                                as Set
import           Data.Text                               (Text)
import           Language.Cimple                         (Lexeme (..),
                                                          NodeF (..))
import qualified Language.Cimple                         as C
import           Language.Hic.Refined.BufferSize.Env
import           Language.Hic.Refined.BufferSize.Paths
import qualified Language.Hic.Refined.Inference.Platform as Platform

-- | For each function defined in the program, the pointer parameters (by
-- position) it may keep.
type Keeps = Map Text (Set Int)

-- | Whether a call may keep what's given as an argument: a function that
-- isn't defined in the program may, unless it's one of the libc or
-- libsodium functions known not to.
mayKeep :: Keeps -> C.Node (Lexeme Text) -> Int -> Bool
mayKeep keeps (Fix (VarExpr (L _ _ f))) i = case Map.lookup f keeps of
    Just kept -> Set.member i kept
    Nothing   -> not (Platform.keepsNothing f)
mayKeep _ _ _ = True

-- | Starting from no function keeping anything, what each one keeps given
-- what the others do, until nothing changes. A function defined more than
-- once keeps what any of its definitions does.
keptParams :: Env -> [C.Node (Lexeme Text)] -> Keeps
keptParams env nodes = go (Map.fromList [ (name, Set.empty) | (name, _, _) <- defns ])
  where
    defns = concatMap definitions nodes
    definitions (Fix node) = case node of
        FunctionDefn _ (Fix (FunctionPrototype _ (L _ _ name) params)) body ->
            [(name, [ p | Just (p, _) <- map (declType env) params ], body)]
        _ -> concatMap definitions (toList node)
    go keeps =
        let keeps' = Map.fromListWith Set.union
                [ (name, Set.fromList [ i | (i, p) <- zip [0 ..] params, p `Set.member` kept ])
                | (name, params, body) <- defns
                , let kept = keptIn keeps body
                ]
        in if keeps' == keeps then keeps else go keeps'

-- | The variables whose pointer value a function body may keep.
keptIn :: Keeps -> C.Node (Lexeme Text) -> Set Text
keptIn keeps = go
  where
    go (Fix node) = rootsKept node <> foldMap go node
    rootsKept = \case
        AssignExpr _ _ rhs                -> roots rhs
        VarDeclStmt _ (Just e)            -> roots e
        Return (Just e)                   -> roots e
        InitialiserList es                -> foldMap roots es
        FunctionCall f args               -> mconcat [ roots a | (i, a) <- zip [0 ..] args, mayKeep keeps f i ]
        _                                 -> Set.empty

-- | The variables a pointer value is made from: itself, an address in it,
-- or pointer arithmetic on it.
roots :: C.Node (Lexeme Text) -> Set Text
roots (Fix node) = case node of
    VarExpr (L _ _ v)          -> Set.singleton v
    ParenExpr e                -> roots e
    CastExpr _ e               -> roots e
    BinaryExpr a op b
        | op `elem` [C.BopPlus, C.BopMinus] -> roots a <> roots b
    TernaryExpr _ a b          -> roots a <> roots b
    UnaryExpr C.UopAddress x   -> maybe Set.empty (Set.singleton . pathRoot) (pathOf x)
    _                          -> Set.empty

-- | Variables whose memory may be reached past where its address is taken:
-- given to a function that may keep it, or put anywhere but an argument.
-- The address of what a pointer points to isn't the pointer's. An array
-- named anywhere but where it's indexed or measured is its address.
addressesKept :: (Text -> Bool) -> (Text -> Bool) -> Keeps -> C.Node (Lexeme Text) -> Set Text
addressesKept isPointer isArray keeps = go
  where
    go (Fix node) = case node of
        FunctionCall f args -> go f <> mconcat
            [ if mayKeep keeps f i then go a else inner a | (i, a) <- zip [0 ..] args ]
        UnaryExpr C.UopAddress x -> own x <> go x
        VarExpr (L _ _ v) | isArray v -> Set.singleton v
        ArrayAccess (Fix (VarExpr (L _ _ v))) i | isArray v -> go i
        SizeofExpr{} -> Set.empty
        _ -> foldMap go node
    -- An address given straight to a call that doesn't keep it, or an
    -- array, or somewhere in one.
    inner (Fix node) = case node of
        ParenExpr e              -> inner e
        CastExpr _ e             -> inner e
        UnaryExpr C.UopAddress x -> go x
        VarExpr (L _ _ v) | isArray v -> Set.empty
        BinaryExpr a op b
            | op `elem` [C.BopPlus, C.BopMinus] -> inner a <> inner b
        _                        -> go (Fix node)
    own x = case pathOf x of
        Just (Path root steps)
            | Deref `notElem` steps
            , case steps of
                Index{} : _ -> not (isPointer root)
                _           -> True
            -> Set.singleton root
        _ -> Set.empty
