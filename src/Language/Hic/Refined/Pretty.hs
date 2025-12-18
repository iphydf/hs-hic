{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Language.Hic.Refined.Pretty
    ( ppRefinedType
    , ppAnyRefinedType
    ) where

import           Data.IntMap.Strict            (IntMap)
import qualified Data.IntMap.Strict            as IntMap
import           Data.Map.Strict               (Map)
import qualified Data.Map.Strict               as Map
import           Data.Maybe                    (fromMaybe)
import           Data.Text                     (Text)
import qualified Data.Text                     as T
import           Language.Cimple               (Lexeme (..), lexemeText)
import           Language.Hic.Refined.Types
import           Prettyprinter
import           Prettyprinter.Render.Terminal (AnsiStyle, Color (..), bold,
                                                color)

typeStyle :: Doc AnsiStyle -> Doc AnsiStyle
typeStyle = annotate (color Cyan)

keywordStyle :: Doc AnsiStyle -> Doc AnsiStyle
keywordStyle = annotate (color Magenta)

literalStyle :: Doc AnsiStyle -> Doc AnsiStyle
literalStyle = annotate (color Blue)

varStyle :: Doc AnsiStyle -> Doc AnsiStyle
varStyle = annotate (color Yellow)

ppStdType :: StdType -> Doc AnsiStyle
ppStdType = typeStyle . \case
    BoolTy    -> "bool"
    CharTy    -> "char"
    U08Ty     -> "uint8_t"
    S08Ty     -> "int8_t"
    U16Ty     -> "uint16_t"
    S16Ty     -> "int16_t"
    U32Ty     -> "uint32_t"
    S32Ty     -> "int32_t"
    U64Ty     -> "uint64_t"
    S64Ty     -> "int64_t"
    SizeTy    -> "size_t"
    F32Ty     -> "float"
    F64Ty     -> "double"
    NullPtrTy -> "nullptr_t"

ppAnyRefinedType :: (a -> Doc AnsiStyle) -> AnyRigidNodeF TemplateId a -> Doc AnsiStyle
ppAnyRefinedType pp (AnyRigidNodeF n) = ppRefinedType pp n

ppRefinedType :: (a -> Doc AnsiStyle) -> RigidNodeF k TemplateId a -> Doc AnsiStyle
ppRefinedType pp = \case
    RObject s q -> ppQuals q $ ppObjectStructure pp s
    RReference r n o q -> ppQuals q $ ppRefStructure pp r n o
    RFunction args ret -> ppReturnType pp ret <> parens (hsep $ punctuate comma $ map pp args)
    RTerminal t -> ppTerminalNode pp t

ppQuals :: Quals -> Doc AnsiStyle -> Doc AnsiStyle
ppQuals q d =
    let c = if qConst q then keywordStyle "const" <+> d else d
    in if qPhysical q then keywordStyle "phys" <+> c else c

ppObjectStructure :: (a -> Doc AnsiStyle) -> ObjectStructure TemplateId a -> Doc AnsiStyle
ppObjectStructure pp = \case
    VBuiltin std -> ppStdType std
    VSingleton std v -> ppStdType std <> "=" <> literalStyle (pretty v)
    VNominal l params ->
        let name = T.pack $ show $ lexemeText l
            prefix = if "struct " `T.isPrefixOf` name || "union " `T.isPrefixOf` name then mempty else keywordStyle "struct" <+> mempty
        in prefix <> typeStyle (pretty name) <> if null params then mempty else angles (hsep $ punctuate comma $ map pp params)
    VEnum l -> keywordStyle "enum" <+> typeStyle (pretty $ show $ lexemeText l)
    VVar tid idx -> ppTemplateId tid <> maybe mempty (brackets . ppIndex) idx
    VExistential tids body -> "∃" <> hsep (map ppTemplateId tids) <> "." <+> pp body
    VVariant m -> "Refined Union" <+> braces (hsep $ punctuate comma $ map ppCase $ IntMap.toList m)
    VProperty a pk -> ppProperty pp a pk
    VSizeExpr ts -> "Σ" <> parens (hsep $ punctuate "+" $ map ppTerm ts)
  where
    ppCase (idx, a) = literalStyle (pretty idx) <+> "->" <+> pp a
    ppTerm (a, c) = pretty c <+> "*" <+> pp a

ppTemplateId :: TemplateId -> Doc AnsiStyle
ppTemplateId = varStyle . pretty . \case
    TIdName t -> t
    TIdParam _ i h -> fromMaybe ("P" <> T.pack (show i)) h
    TIdSkolem _ _ i -> "S" <> T.pack (show i)
    TIdInstance i -> "I" <> T.pack (show i)
    TIdDeBruijn i -> "D" <> T.pack (show i)

ppIndex :: Index TemplateId -> Doc AnsiStyle
ppIndex = \case
    ILit i -> literalStyle (pretty i)
    IVar tid -> ppTemplateId tid

ppProperty :: (a -> Doc AnsiStyle) -> a -> PropertyKind -> Doc AnsiStyle
ppProperty pp a = \case
    PSize -> "sizeof" <> parens (pp a)
    PAlign -> "alignof" <> parens (pp a)
    POffset f -> "offsetof" <> parens (pp a <> comma <+> pretty f)

ppRefStructure :: (a -> Doc AnsiStyle) -> RefStructure TemplateId a -> Nullability -> Ownership -> Doc AnsiStyle
ppRefStructure pp r n o =
    let base = case r of
            Arr e dims -> pp e <> hcat (map (brackets . pp) dims)
            Ptr t      -> ppPtrTarget pp t
        nullStr = case n of
            QNonnull'    -> Just $ keywordStyle "Nonnull"
            QNullable'   -> Just $ keywordStyle "Nullable"
            QUnspecified -> Nothing
        ownStr = case o of
            QOwned'    -> Just $ keywordStyle "Owner"
            QNonOwned' -> Nothing
    in hsep $ base : mapMaybe id [nullStr, ownStr]

mapMaybe :: (a -> Maybe b) -> [a] -> [b]
mapMaybe _ [] = []
mapMaybe f (x:xs) = case f x of
    Just y  -> y : mapMaybe f xs
    Nothing -> mapMaybe f xs

ppPtrTarget :: (a -> Doc AnsiStyle) -> PtrTarget TemplateId a -> Doc AnsiStyle
ppPtrTarget pp = \case
    TargetObject a -> pp a <> "*"
    TargetFunction args ret -> ppReturnType pp ret <+> parens ("*" <> parens (hsep $ punctuate comma $ map pp args))
    TargetOpaque tid -> ppTemplateId tid <> "*"

ppReturnType :: (a -> Doc AnsiStyle) -> ReturnType a -> Doc AnsiStyle
ppReturnType pp = \case
    RetVal a -> pp a
    RetVoid -> keywordStyle "void"

ppTerminalNode :: (a -> Doc AnsiStyle) -> TerminalNode a -> Doc AnsiStyle
ppTerminalNode pp = \case
    SBottom -> keywordStyle "Bottom"
    SAny -> keywordStyle "Any"
    SConflict -> annotate (color Red <> bold) "Conflict"
    STerminal a -> pp a
