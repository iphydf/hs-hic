{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
module Language.Hic.TypeSystem.Core.Substitution
    ( substituteType
    , substituteDescr
    , substituteTypeSystem
    ) where

import           Data.Fix                          (Fix (..), foldFix)
import           Data.Map.Strict                   (Map)
import qualified Data.Map.Strict                   as Map
import           Data.Maybe                        (fromMaybe)
import           Data.Text                         (Text)
import           Language.Hic.Core.TypeSystem      (FullTemplate, Invariant,
                                                    TypeDescr (..), TypeInfo,
                                                    TypeInfoF (..),
                                                    mapInvariant)
import           Language.Hic.TypeSystem.Core.Base (mapTemplates)


-- | Replaces all Template nodes in a TypeInfo with their bound values.
substituteType :: Map (FullTemplate p) (TypeInfo p) -> TypeInfo p -> TypeInfo p
substituteType bindings = mapTemplates (\ft -> fromMaybe (Fix (TemplateF ft)) (Map.lookup ft bindings))

-- | Applies substitution to a TypeDescr.
substituteDescr :: Map (FullTemplate p) (TypeInfo p) -> TypeDescr p -> TypeDescr p
substituteDescr bindings = \case
    StructDescr l ts mems invs -> StructDescr l ts (map (fmap (substituteType bindings)) mems) (map (substituteInvariant bindings) invs)
    UnionDescr l ts mems invs  -> UnionDescr l ts (map (fmap (substituteType bindings)) mems) (map (substituteInvariant bindings) invs)
    EnumDescr l tys           -> EnumDescr l (map (substituteType bindings) tys)
    IntDescr l t              -> IntDescr l t
    FuncDescr l ts r ps       -> FuncDescr l ts (substituteType bindings r) (map (substituteType bindings) ps)
    AliasDescr l ts t         -> AliasDescr l ts (substituteType bindings t)

substituteInvariant :: Map (FullTemplate p) (TypeInfo p) -> Invariant p -> Invariant p
substituteInvariant bindings = mapInvariant (substituteType bindings)

-- | Applies substitution to an entire TypeSystem.
-- Note: This assumes the bindings and TypeSystem are in the same Phase (usually Global for the final result).
substituteTypeSystem :: Map (FullTemplate p) (TypeInfo p) -> Map Text (TypeDescr p) -> Map Text (TypeDescr p)
substituteTypeSystem bindings = Map.map (substituteDescr bindings)
