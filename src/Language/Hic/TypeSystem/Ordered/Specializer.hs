{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms   #-}

module Language.Hic.TypeSystem.Ordered.Specializer
    ( specializeType
    , specializeConstraint
    , collectTemplates
    , collectConstraintTemplates
    , mapTypesPhase
    , toGlobalConstraint
    , toLocalConstraint
    ) where

import           Data.Bifunctor                           (bimap)
import           Data.Fix                                 (Fix (..), foldFix)
import           Data.Set                                 (Set)
import qualified Data.Set                                 as Set
import qualified Data.Text                                as T
import           Language.Cimple                          (Lexeme (..))
import           Language.Hic.Core.Errors                 (Context (..),
                                                           MismatchReason (..))
import           Language.Hic.Core.TypeSystem             (Phase (Global, Local),
                                                           TemplateId (..),
                                                           TypeInfo,
                                                           TypeInfoF (..),
                                                           pattern FullTemplate,
                                                           pattern Template)
import qualified Language.Hic.TypeSystem.Core.Base        as TS
import           Language.Hic.TypeSystem.Core.Constraints (Constraint (..),
                                                           mapTypes)

-- | Deeply specialize a type with a literal index.
specializeType :: TypeInfo 'Local -> TypeInfo 'Local -> TypeInfo 'Local
specializeType idx = TS.indexTemplates idx

-- | Specialize a constraint by applying the index to all templates within it.
specializeConstraint :: TypeInfo 'Local -> Constraint 'Local -> Constraint 'Local
specializeConstraint idx = mapTypes (specializeType idx)

-- | Find all template IDs present in a type.
collectTemplates :: TypeInfo p -> Set (TemplateId p)
collectTemplates = foldFix $ \case
    TemplateF (FullTemplate tid _) -> Set.singleton tid
    f -> Set.unions f

-- | Find all template IDs present in a constraint.
collectConstraintTemplates :: Constraint 'Local -> Set (TemplateId 'Local)
collectConstraintTemplates = \case
    Equality t1 t2 _ _ _ -> collectTemplates t1 `Set.union` collectTemplates t2
    Subtype t1 t2 _ _ _ -> collectTemplates t1 `Set.union` collectTemplates t2
    Lub t1 ts _ _ _ -> collectTemplates t1 `Set.union` Set.unions (map collectTemplates ts)
    Callable t1 ts t2 _ _ _ _ -> collectTemplates t1 `Set.union` collectTemplates t2 `Set.union` Set.unions (map collectTemplates ts)
    HasMember t1 _ t2 _ _ _ -> collectTemplates t1 `Set.union` collectTemplates t2
    CoordinatedPair t1 t2 t3 _ _ _ -> collectTemplates t1 `Set.union` collectTemplates t2 `Set.union` collectTemplates t3

-- | Applies a transformation function to all TypeInfo nodes within the constraint, allowing phase changes.
mapTypesPhase :: (TypeInfo p -> TypeInfo q) -> Constraint p -> Constraint q
mapTypesPhase f = \case
    Equality t1 t2 ml ctx r         -> Equality (f t1) (f t2) ml (map convertCtx ctx) r
    Subtype t1 t2 ml ctx r          -> Subtype (f t1) (f t2) ml (map convertCtx ctx) r
    Lub t1 ts ml ctx r              -> Lub (f t1) (map f ts) ml (map convertCtx ctx) r
    Callable t1 ts t2 ml ctx i s    -> Callable (f t1) (map f ts) (f t2) ml (map convertCtx ctx) i s
    HasMember t1 n t2 ml ctx r      -> HasMember (f t1) n (f t2) ml (map convertCtx ctx) r
    CoordinatedPair t1 t2 t3 ml ctx i -> CoordinatedPair (f t1) (f t2) (f t3) ml (map convertCtx ctx) i
  where
    convertCtx (InUnification e a r) = InUnification (f e) (f a) r
    convertCtx (InFile n)            = InFile n
    convertCtx (InFunction n)        = InFunction n
    convertCtx (InMacro n)           = InMacro n
    convertCtx (InMemberAccess n)    = InMemberAccess n
    convertCtx (InExpr n)            = InExpr n
    convertCtx (InStmt n)            = InStmt n
    convertCtx (InInitializer n)     = InInitializer n

-- | Convert a Local constraint to a Global one.
toGlobalConstraint :: Constraint 'Local -> Constraint 'Global
toGlobalConstraint = mapTypesPhase TS.toGlobal

-- | Convert a Global constraint to a Local one.
toLocalConstraint :: Integer -> TS.Origin -> Constraint 'Global -> Constraint 'Local
toLocalConstraint ph parent = mapTypesPhase (TS.toLocal ph parent)
