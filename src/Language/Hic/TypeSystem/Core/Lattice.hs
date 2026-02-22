{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE PatternSynonyms     #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Language.Hic.TypeSystem.Core.Lattice
    ( subtypeOf
    , join
    , joinSymbolic
    , joinGraph
    , meet
    , meetSymbolic
    , meetGraph
    , compatible
    ) where

import qualified Data.Text                                     as T
import           Language.Cimple                               (Lexeme (..))
import           Language.Hic.Core.TypeSystem                  (Phase (Local),
                                                                StdType (BoolTy, NullPtrTy, S32Ty),
                                                                TypeInfo,
                                                                pattern Array,
                                                                pattern BuiltinType,
                                                                pattern ExternalType,
                                                                pattern IntLit,
                                                                pattern Nullable,
                                                                pattern Pointer,
                                                                pattern Singleton,
                                                                pattern Template,
                                                                pattern Var,
                                                                templateIdBaseName)
import           Language.Hic.TypeSystem.Core.Base             (isNetworkingStruct)
import qualified Language.Hic.TypeSystem.Core.Base             as TS
import qualified Language.Hic.TypeSystem.Core.Canonicalization as Canonicalization
import           Language.Hic.TypeSystem.Core.Transition       (Polarity (..),
                                                                RigidNodeF (..),
                                                                ValueStructure (..))
import           Language.Hic.TypeSystem.Core.TypeGraph        (TypeGraph,
                                                                productConstruction)
import qualified Language.Hic.TypeSystem.Core.TypeGraph        as TG
import           Language.Hic.TypeSystem.Core.Subtype          (subtypeOfGraph)

subtypeOf :: forall p. (Ord (TS.TemplateId p)) => TypeInfo p -> TypeInfo p -> Bool
subtypeOf t1 t2 =
    let g1 = TG.minimizeGraph (TG.fromTypeInfo t1)
        g2 = TG.minimizeGraph (TG.fromTypeInfo t2)
    in subtypeOfGraph g1 g2

join :: TypeInfo p -> TypeInfo p -> TypeInfo p
join = joinSymbolic (const False)

joinSymbolic :: forall p. (TS.FullTemplate p -> Bool) -> TypeInfo p -> TypeInfo p -> TypeInfo p
joinSymbolic isVar t1 t2 =
    let g1 = TG.fromTypeInfo t1
        g2 = TG.fromTypeInfo t2
    in TG.toTypeInfo $ joinGraph isVar g1 g2

joinGraph :: forall p. (TS.FullTemplate p -> Bool) -> TypeGraph p -> TypeGraph p -> TypeGraph p
joinGraph isVar g1 g2 =
    let isVarNode = \case
            RValue (VTemplate ft _ _) _ _ -> isVar (fmap (const TS.Unconstrained) ft)
            _ -> False
    in productConstruction isVarNode TG.PJoin g1 g2

meetGraph :: forall p. (TS.FullTemplate p -> Bool) -> TypeGraph p -> TypeGraph p -> TypeGraph p
meetGraph isVar g1 g2 =
    let isVarNode = \case
            RValue (VTemplate ft _ _) _ _ -> isVar (fmap (const TS.Unconstrained) ft)
            _ -> False
    in productConstruction isVarNode TG.PMeet g1 g2

meet :: TypeInfo p -> TypeInfo p -> TypeInfo p
meet = meetSymbolic (const False)

meetSymbolic :: forall p. (TS.FullTemplate p -> Bool) -> TypeInfo p -> TypeInfo p -> TypeInfo p
meetSymbolic isVar t1 t2 =
    let g1 = TG.fromTypeInfo t1
        g2 = TG.fromTypeInfo t2
    in TG.toTypeInfo $ meetGraph isVar g1 g2


compatible :: TypeInfo 'Local -> TypeInfo 'Local -> Bool
compatible t1 t2 | t1 == t2 = True
compatible t1 t2 | isNetworkingStruct t1 && isNetworkingStruct t2 = True
compatible (ExternalType (L _ _ n1)) (ExternalType (L _ _ n2)) =
    templateIdBaseName n1 == templateIdBaseName n2
compatible (BuiltinType NullPtrTy) (Pointer _) = True
compatible (Pointer _) (BuiltinType NullPtrTy) = True
compatible (BuiltinType NullPtrTy) (Nullable _) = True
compatible (Nullable _) (BuiltinType NullPtrTy) = True
compatible (Template _ _) _ = True
compatible _ (Template _ _) = True
compatible (Pointer _) (Array _ _) = True
compatible (Array _ _) (Pointer _) = True
compatible (BuiltinType b1) (BuiltinType b2)
    | b1 == b2 = True
    | TS.isInt b1 && TS.isInt b2 = True
    | b1 == BoolTy && TS.isInt b2 = True
    | TS.isInt b1 && b2 == BoolTy = True
    | otherwise = False
compatible (Singleton b1 _) (BuiltinType b2) = compatible (BuiltinType b1) (BuiltinType b2)
compatible (BuiltinType b1) (Singleton b2 _) = compatible (BuiltinType b1) (BuiltinType b2)
compatible (Singleton b1 _) (Singleton b2 _) = compatible (BuiltinType b1) (BuiltinType b2)
compatible (IntLit (L _ _ v1)) (IntLit (L _ _ v2)) = v1 == v2
compatible (IntLit (L _ _ v1)) (Singleton S32Ty v2) =
    (read (T.unpack (templateIdBaseName v1)) :: Integer) == v2
compatible (Singleton S32Ty v1) (IntLit (L _ _ v2)) =
    v1 == (read (T.unpack (templateIdBaseName v2)) :: Integer)
compatible (IntLit _) (BuiltinType b) = TS.isInt b
compatible (BuiltinType b) (IntLit _) = TS.isInt b
compatible (Var _ a) e = compatible a e
compatible a (Var _ e) = compatible a e
compatible _ _ = False
