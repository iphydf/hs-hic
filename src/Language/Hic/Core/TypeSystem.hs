{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DeriveTraversable     #-}
{-# LANGUAGE DerivingVia           #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE StrictData            #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE ViewPatterns          #-}
module Language.Hic.Core.TypeSystem
    ( StdType (..)
    , Phase (..)
    , Origin (..)
    , TemplateId (..)
    , FullTemplate
    , pattern FullTemplate
    , FullTemplateF (..)
    , TypeRef (..)
    , TypeInfo
    , TypeInfoF (..)
    , TypeDescr (..)
    , Invariant (..)
    , TypeSystem
    , mapInvariant
    , mapInvariantM
    , templateIdToText
    , templateIdBaseName
    , templateIdHint
    , templateIdOrigin
    , isConflict
    , isUnconstrained
    , pattern TypeRef
    , pattern Pointer
    , pattern Sized
    , pattern Const
    , pattern Owner
    , pattern Nonnull
    , pattern Nullable
    , pattern Qualified
    , pattern BuiltinType
    , pattern ExternalType
    , pattern Array
    , pattern Var
    , pattern Function
    , pattern Template
    , pattern Singleton
    , pattern VarArg
    , pattern IntLit
    , pattern NameLit
    , pattern EnumMem
    , pattern Unconstrained
    , pattern Conflict
    , pattern Proxy
    , pattern Unsupported
    , Qualifier (..)
    , FlatType (..)
    , toFlat
    , fromFlat
    , normalizeQuals
    , zipWithF
    , voidFullTemplate
    , normalizeType
    , stripLexemes
    , ArbitraryTemplateId (..)
    , isVoid
    , getTemplateVars
    , collectUniqueTemplateVars
    ) where

import           Control.Applicative          ((<|>))
import qualified Control.Monad.State          as State
import           Data.Aeson                   (FromJSON (..), FromJSON1 (..),
                                               ToJSON (..), ToJSON1 (..),
                                               withObject, (.!=), (.:), (.:?),
                                               (.=))
import qualified Data.Aeson                   as JS
import           Data.Aeson.Types             (Options (..), Parser,
                                               defaultOptions, genericParseJSON,
                                               genericToJSON, toJSON)
import           Data.Bifunctor               (Bifunctor (..))
import           Data.Fix                     (Fix (..), foldFix)
import           Data.Foldable                (toList)
import           Data.Functor.Classes         (Eq1, Ord1, Read1, Show1)
import           Data.Functor.Classes.Generic (FunctorClassesDefault (..))
import           Data.List                    (foldl')
import           Data.Map.Strict              (Map)
import qualified Data.Map.Strict              as Map
import           Data.Maybe                   (mapMaybe)
import           Data.Set                     (Set)
import qualified Data.Set                     as Set
import           Data.Text                    (Text)
import qualified Data.Text                    as Text
import qualified Debug.Trace                  as Debug
import           GHC.Generics                 (Generic, Generic1)
import           Language.Cimple              (Lexeme (..))
import qualified Language.Cimple              as C
import           Prettyprinter                (Pretty (..))
import           Test.QuickCheck              (Arbitrary (..), Gen,
                                               arbitraryBoundedEnum, elements,
                                               genericShrink, oneof, scale,
                                               sized)

data StdType
    = VoidTy
    | BoolTy
    | CharTy
    | U08Ty
    | S08Ty
    | U16Ty
    | S16Ty
    | U32Ty
    | S32Ty
    | U64Ty
    | S64Ty
    | SizeTy
    | F32Ty
    | F64Ty
    | NullPtrTy
    deriving (Show, Read, Eq, Ord, Generic)

instance ToJSON StdType
instance FromJSON StdType

instance Arbitrary StdType where
    arbitrary = elements [VoidTy, BoolTy, CharTy, U08Ty, S08Ty, U16Ty, S16Ty, U32Ty, S32Ty, U64Ty, S64Ty, SizeTy, F32Ty, F64Ty, NullPtrTy]
    shrink = genericShrink

data Phase = Global | Local
    deriving (Show, Read, Eq, Ord, Generic, Bounded, Enum)

instance Arbitrary Phase where
    arbitrary = arbitraryBoundedEnum
    shrink = genericShrink

-- | Represents the source of a template identity.
data Origin
    = TopLevel
    | Arg Int
    | Result
    | LocalVar Text
    | Source Text
    | Internal
    | MemberOrigin Origin Text
    | ArrayOrigin Origin (Maybe Integer)
    deriving (Show, Eq, Ord, Generic)

instance ToJSON Origin
instance FromJSON Origin

instance Arbitrary Origin where
    arbitrary = oneof
        [ return TopLevel
        , Arg <$> arbitrary
        , return Result
        , LocalVar . Text.pack <$> arbitrary
        , Source . Text.pack <$> arbitrary
        , return Internal
        , MemberOrigin <$> scale (`div` 2) arbitrary <*> (Text.pack <$> arbitrary)
        , ArrayOrigin <$> scale (`div` 2) arbitrary <*> arbitrary
        ]
    shrink = \case
        MemberOrigin o f -> o : (MemberOrigin <$> shrink o <*> (Text.pack <$> shrink (Text.unpack f)))
        ArrayOrigin o i -> o : (ArrayOrigin <$> shrink o <*> shrink i)
        Arg i      -> TopLevel : (Arg <$> shrink i)
        LocalVar n -> TopLevel : (LocalVar . Text.pack <$> shrink (Text.unpack n))
        Source n   -> TopLevel : (Source . Text.pack <$> shrink (Text.unpack n))
        Result     -> [TopLevel]
        Internal   -> [TopLevel]
        TopLevel   -> []

-- | Structured identity for templates to ensure stable naming during solving.
data TemplateId (p :: Phase) where
    TIdName      :: Text -> TemplateId 'Global        -- ^ Original name from source (e.g. "T")
    TIdParam     :: Int -> Maybe Text -> Origin -> TemplateId 'Global -- ^ Generalized parameter (P0, P1, ...)
    TIdInst      :: Integer -> TemplateId 'Global -> TemplateId 'Local -- ^ Instantiated at a specific call site ID
    TIdPoly      :: Integer -> Int -> Maybe Text -> Origin -> TemplateId 'Local -- ^ Generalized parameter scoped to a phase
    TIdSolver    :: Int -> Maybe Text -> TemplateId 'Local -- ^ Temporary solver template with an optional hint
    TIdAnonymous :: Int -> Maybe Text -> TemplateId p        -- ^ Anonymous template (e.g. from void*)
    TIdRec       :: Int -> TemplateId p               -- ^ Recursion point for equi-recursive types

deriving instance Show (TemplateId p)
deriving instance Eq (TemplateId p)
deriving instance Ord (TemplateId p)

class ArbitraryTemplateId (p :: Phase) where
    arbitraryTemplateId :: Gen (TemplateId p)

instance ArbitraryTemplateId 'Global where
    arbitraryTemplateId = oneof
        [ TIdName . Text.pack <$> arbitrary
        , TIdParam <$> arbitrary <*> (fmap Text.pack <$> arbitrary) <*> arbitrary
        , TIdAnonymous <$> arbitrary <*> (fmap Text.pack <$> arbitrary)
        -- TIdRec is not generated: it's an internal representation for equi-recursive cycles
        ]

instance ArbitraryTemplateId 'Local where
    arbitraryTemplateId = oneof
        [ TIdInst <$> arbitrary <*> arbitraryTemplateId
        , TIdPoly <$> arbitrary <*> arbitrary <*> (fmap Text.pack <$> arbitrary) <*> arbitrary
        , TIdSolver <$> arbitrary <*> (fmap Text.pack <$> arbitrary)
        , TIdAnonymous <$> arbitrary <*> (fmap Text.pack <$> arbitrary)
        -- TIdRec is not generated: it's an internal representation for equi-recursive cycles
        ]

instance ArbitraryTemplateId p => Arbitrary (TemplateId p) where
    arbitrary = arbitraryTemplateId

instance ToJSON (TemplateId p) where
    toJSON (TIdName n)             = JS.object ["tag" .= ("TIdName" :: Text), "contents" .= n]
    toJSON (TIdParam i h o)        = JS.object ["tag" .= ("TIdParam" :: Text), "index" .= i, "hint" .= h, "origin" .= o]
    toJSON (TIdInst i tid)         = JS.object ["tag" .= ("TIdInst" :: Text), "index" .= i, "tid" .= tid]
    toJSON (TIdPoly ph i h o)      = JS.object ["tag" .= ("TIdPoly" :: Text), "phase" .= ph, "index" .= i, "hint" .= h, "origin" .= o]
    toJSON (TIdSolver i h)         = JS.object ["tag" .= ("TIdSolver" :: Text), "index" .= i, "hint" .= h]
    toJSON (TIdAnonymous i h)      = JS.object ["tag" .= ("TIdAnonymous" :: Text), "index" .= i, "hint" .= h]
    toJSON (TIdRec i)              = JS.object ["tag" .= ("TIdRec" :: Text), "index" .= i]

class FromJSONTemplateId (p :: Phase) where
    parseTemplateId :: JS.Value -> Parser (TemplateId p)

instance FromJSONTemplateId 'Global where
    parseTemplateId = withObject "TemplateId Global" $ \v -> do
        tag <- v .: "tag"
        case (tag :: Text) of
            "TIdName"      -> TIdName <$> v .: "contents"
            "TIdParam"     -> TIdParam <$> v .: "index" <*> v .: "hint" <*> (v .:? "origin" .!= TopLevel)
            "TIdAnonymous" -> TIdAnonymous <$> v .: "index" <*> v .: "hint"
            "TIdRec"       -> TIdRec <$> v .: "index"
            _              -> fail $ "Invalid TemplateId Global tag: " ++ Text.unpack tag

instance FromJSONTemplateId 'Local where
    parseTemplateId = withObject "TemplateId Local" $ \v -> do
        tag <- v .: "tag"
        case (tag :: Text) of
            "TIdInst"      -> TIdInst <$> v .: "index" <*> (parseTemplateId =<< v .: "tid")
            "TIdPoly"      -> TIdPoly <$> v .: "phase" <*> v .: "index" <*> v .: "hint" <*> (v .:? "origin" .!= TopLevel)
            "TIdSolver"    -> TIdSolver <$> v .: "index" <*> v .: "hint"
            "TIdAnonymous" -> TIdAnonymous <$> v .: "index" <*> v .: "hint"
            "TIdRec"       -> TIdRec <$> v .: "index"
            _              -> fail $ "Invalid TemplateId Local tag: " ++ Text.unpack tag

instance FromJSONTemplateId p => FromJSON (TemplateId p) where
    parseJSON = parseTemplateId

-- | Unified identity for a template and its optional index.
data FullTemplateF tid a = FT
    { ftId    :: tid
    , ftIndex :: Maybe a
    }
    deriving (Show, Read, Eq, Ord, Generic, Generic1, Functor, Foldable, Traversable)

deriving via FunctorClassesDefault (FullTemplateF tid) instance Show tid => Show1 (FullTemplateF tid)
deriving via FunctorClassesDefault (FullTemplateF tid) instance Read tid => Read1 (FullTemplateF tid)
deriving via FunctorClassesDefault (FullTemplateF tid) instance Eq tid => Eq1 (FullTemplateF tid)
deriving via FunctorClassesDefault (FullTemplateF tid) instance Ord tid => Ord1 (FullTemplateF tid)

instance (ToJSON tid, ToJSON a) => ToJSON (FullTemplateF tid a)
instance (FromJSON tid, FromJSON a) => FromJSON (FullTemplateF tid a)

instance (Arbitrary tid, Arbitrary a) => Arbitrary (FullTemplateF tid a) where
    arbitrary = FT <$> arbitrary <*> arbitrary
    shrink (FT tid idx) = [FT tid' idx | tid' <- shrink tid] ++ [FT tid idx' | idx' <- shrink idx]

instance ToJSON tid => ToJSON1 (FullTemplateF tid)
instance FromJSON tid => FromJSON1 (FullTemplateF tid)

type FullTemplate p = FullTemplateF (TemplateId p) (TypeInfo p)

pattern FullTemplate :: tid -> Maybe a -> FullTemplateF tid a
pattern FullTemplate tid idx = FT tid idx

{-# COMPLETE FullTemplate #-}

instance Pretty (TemplateId p) where
    pretty = pretty . templateIdToText

originToText :: Origin -> Text
originToText = \case
    TopLevel   -> "top"
    Arg i      -> "arg:" <> Text.pack (show i)
    Result     -> "ret"
    LocalVar n -> "var:" <> n
    Source n   -> n
    Internal   -> "int"
    MemberOrigin o f -> originToText o <> "." <> f
    ArrayOrigin o i -> originToText o <> "[" <> maybe "i" (Text.pack . show) i <> "]"

templateIdToText :: TemplateId p -> Text
templateIdToText (TIdName n) = n
templateIdToText (TIdParam i Nothing o) = "P" <> Text.pack (show i) <> maybe "" (\o' -> ":" <> originToText o') (if o == TopLevel then Nothing else Just o)
templateIdToText (TIdParam i (Just n) o)
    | Text.null n = templateIdToText (TIdParam i Nothing o)
    | otherwise   = "P" <> Text.pack (show i) <> "(" <> n <> ")" <> maybe "" (\o' -> ":" <> originToText o') (if o == TopLevel then Nothing else Just o)
templateIdToText (TIdInst i tid) = templateIdToText tid <> ":inst:" <> Text.pack (show i)
templateIdToText (TIdPoly _ i (Just n) _)
    | Text.null n = "P" <> Text.pack (show i)
    | otherwise   = n
templateIdToText (TIdPoly ph i Nothing o) =
    "P" <> Text.pack (show i) <> "@" <> Text.pack (show ph) <> maybe "" (\o' -> ":" <> originToText o') (if o == TopLevel then Nothing else Just o)
templateIdToText (TIdSolver i Nothing) = "T" <> Text.pack (show i)
templateIdToText (TIdSolver i (Just n))
    | Text.null n = "T" <> Text.pack (show i)
    | otherwise   = "T" <> Text.pack (show i) <> "(" <> n <> ")"
templateIdToText (TIdAnonymous _ Nothing) = "ANON"
templateIdToText (TIdAnonymous _ (Just n))
    | Text.null n = "ANON"
    | otherwise   = n
templateIdToText (TIdRec i) = "rec" <> Text.pack (show i)

templateIdBaseName :: TemplateId p -> Text
templateIdBaseName (TIdName n)               = n
templateIdBaseName (TIdParam _ Nothing _)    = ""
templateIdBaseName (TIdParam _ (Just n) _)   = n
templateIdBaseName (TIdInst _ tid)           = templateIdBaseName tid
templateIdBaseName (TIdPoly _ _ Nothing _)   = ""
templateIdBaseName (TIdPoly _ _ (Just n) _)  = n
templateIdBaseName (TIdSolver _ Nothing)     = ""
templateIdBaseName (TIdSolver _ (Just n))    = n
templateIdBaseName (TIdAnonymous _ Nothing)  = ""
templateIdBaseName (TIdAnonymous _ (Just n)) = n
templateIdBaseName (TIdRec i)                = "rec" <> Text.pack (show i)

templateIdHint :: TemplateId p -> Maybe Text
templateIdHint (TIdName n)           = Just n
templateIdHint (TIdParam _ hint _)   = hint
templateIdHint (TIdInst _ tid)       = templateIdHint tid
templateIdHint (TIdPoly _ _ hint _)  = hint
templateIdHint (TIdSolver _ hint)    = hint
templateIdHint (TIdAnonymous _ hint) = hint
templateIdHint (TIdRec _)            = Nothing

templateIdOrigin :: TemplateId p -> Origin
templateIdOrigin (TIdName _)        = TopLevel
templateIdOrigin (TIdParam _ _ o)   = o
templateIdOrigin (TIdInst _ tid)    = templateIdOrigin tid
templateIdOrigin (TIdPoly _ _ _ o)  = o
templateIdOrigin (TIdSolver _ _)    = Internal
templateIdOrigin (TIdAnonymous _ _) = Internal
templateIdOrigin (TIdRec _)         = Internal

data TypeRef
    = UnresolvedRef
    | StructRef
    | UnionRef
    | EnumRef
    | IntRef
    | FuncRef
    deriving (Show, Read, Eq, Ord, Generic, Bounded, Enum)

instance ToJSON TypeRef
instance FromJSON TypeRef

data TypeInfoF lexeme a
    = TypeRefF TypeRef (Lexeme lexeme) [a]
    | PointerF a
    | SizedF a (Lexeme lexeme)
    | QualifiedF (Set Qualifier) a
    | BuiltinTypeF StdType
    | ExternalTypeF (Lexeme lexeme)
    | ArrayF (Maybe a) [a]
    | VarF (Lexeme lexeme) a
    | FunctionF a [a]
    | TemplateF (FullTemplateF lexeme a)
    | SingletonF StdType Integer
    | VarArgF
    | IntLitF (Lexeme lexeme)
    | NameLitF (Lexeme lexeme)
    | EnumMemF (Lexeme lexeme)
    | UnconstrainedF
    | ConflictF
    | ProxyF a
    | UnsupportedF Text
    deriving (Show, Read, Eq, Ord, Generic, Generic1, Functor, Foldable, Traversable)
    deriving (Show1, Read1, Eq1, Ord1) via FunctorClassesDefault (TypeInfoF lexeme)

instance FromJSON lexeme => FromJSON1 (TypeInfoF lexeme)
instance ToJSON lexeme => ToJSON1 (TypeInfoF lexeme)

instance Bifunctor FullTemplateF where
    bimap f g (FT tid idx) = FT (f tid) (fmap g idx)

instance Bifunctor TypeInfoF where
    bimap f g (TypeRefF r l args) = TypeRefF r (fmap f l) (map g args)
    bimap _ g (PointerF a)        = PointerF (g a)
    bimap f g (SizedF a l)        = SizedF (g a) (fmap f l)
    bimap _ g (QualifiedF qs a)   = QualifiedF qs (g a)
    bimap _ _ (BuiltinTypeF s)    = BuiltinTypeF s
    bimap f _ (ExternalTypeF l)   = ExternalTypeF (fmap f l)
    bimap _ g (ArrayF m args)     = ArrayF (fmap g m) (map g args)
    bimap f g (VarF l a)          = VarF (fmap f l) (g a)
    bimap _ g (FunctionF r ps)    = FunctionF (g r) (map g ps)
    bimap f g (TemplateF ft)      = TemplateF (bimap f g ft)
    bimap _ _ (SingletonF s i)    = SingletonF s i
    bimap _ _ VarArgF             = VarArgF
    bimap f _ (IntLitF l)         = IntLitF (fmap f l)
    bimap f _ (NameLitF l)        = NameLitF (fmap f l)
    bimap f _ (EnumMemF l)        = EnumMemF (fmap f l)
    bimap _ _ UnconstrainedF      = UnconstrainedF
    bimap _ _ ConflictF           = ConflictF
    bimap _ g (ProxyF a)          = ProxyF (g a)
    bimap _ _ (UnsupportedF t)    = UnsupportedF t

-- | Zips two TypeInfoF structures together if they have the same constructor.
zipWithF :: Eq tid => (a -> b -> c) -> TypeInfoF tid a -> TypeInfoF tid b -> Maybe (TypeInfoF tid c)
zipWithF f (TypeRefF r1 l1 args1) (TypeRefF r2 l2 args2)
    | r1 == r2 && l1 == l2 && length args1 == length args2 = Just $ TypeRefF r1 l1 (zipWith f args1 args2)
zipWithF f (PointerF a) (PointerF b) = Just $ PointerF (f a b)
zipWithF f (QualifiedF qs1 a) (QualifiedF qs2 b)
    | qs1 == qs2 = Just $ QualifiedF qs1 (f a b)
zipWithF f (SizedF a l1) (SizedF b l2) | l1 == l2 = Just $ SizedF (f a b) l1
zipWithF _ (BuiltinTypeF s1) (BuiltinTypeF s2) | s1 == s2 = Just $ BuiltinTypeF s1
zipWithF _ (ExternalTypeF l1) (ExternalTypeF l2) | l1 == l2 = Just $ ExternalTypeF l1
zipWithF f (ArrayF m1 d1) (ArrayF m2 d2)
    | length d1 == length d2 = Just $ ArrayF (f <$> m1 <*> m2) (zipWith f d1 d2)
zipWithF f (VarF l1 a) (VarF l2 b) | l1 == l2 = Just $ VarF l1 (f a b)
zipWithF f (FunctionF r1 ps1) (FunctionF r2 ps2)
    | length ps1 == length ps2 = Just $ FunctionF (f r1 r2) (zipWith f ps1 ps2)
zipWithF f (TemplateF (FT t1 i1)) (TemplateF (FT t2 i2))
    | t1 == t2 = case (i1, i2) of
        (Just a, Just b)   -> Just $ TemplateF (FT t1 (Just (f a b)))
        (Nothing, Nothing) -> Just $ TemplateF (FT t1 Nothing)
        _                  -> Nothing
zipWithF _ (SingletonF s1 i1) (SingletonF s2 i2) | s1 == s2 && i1 == i2 = Just $ SingletonF s1 i1
zipWithF _ VarArgF VarArgF = Just VarArgF
zipWithF _ (IntLitF l1) (IntLitF l2) | l1 == l2 = Just $ IntLitF l1
zipWithF _ (NameLitF l1) (NameLitF l2) | l1 == l2 = Just $ NameLitF l1
zipWithF _ (EnumMemF l1) (EnumMemF l2) | l1 == l2 = Just $ EnumMemF l1
zipWithF _ UnconstrainedF UnconstrainedF = Just UnconstrainedF
zipWithF _ ConflictF ConflictF = Just ConflictF
zipWithF f (ProxyF a) (ProxyF b) = Just $ ProxyF (f a b)
zipWithF _ (UnsupportedF t1) (UnsupportedF t2) | t1 == t2 = Just $ UnsupportedF t1
zipWithF _ _ _ = Nothing

-- | Strips the index from a FullTemplate.
voidFullTemplate :: FullTemplateF tid a -> FullTemplateF tid ()
voidFullTemplate (FT tid _) = FT tid Nothing

type TypeInfo p = Fix (TypeInfoF (TemplateId p))

instance ArbitraryTemplateId p => Arbitrary (TypeInfo p) where
    arbitrary = sized $ \n ->
        if n <= 0
        then oneof [ BuiltinType <$> arbitrary
                   , Template <$> arbitrary <*> return Nothing
                   , return VarArg
                   , return Unconstrained
                   , return Conflict
                   ]
        else oneof [ BuiltinType <$> arbitrary
                   , Pointer <$> scale (\x -> x - 1) arbitrary
                   , Sized <$> scale (\x -> x - 1) arbitrary <*> arbitrary
                   , Qualified <$> arbitrary <*> scale (\x -> x - 1) arbitrary
                   , Array <$> scale (\x -> x - 1) arbitrary <*> scale (\x -> x - 1) (oneof [return [], (:[]) <$> arbitrary])
                   , Function <$> scale (\x -> x - 1) arbitrary <*> scale (\x -> x - 1) (oneof [return [], (:[]) <$> arbitrary])
                   , Template <$> arbitrary <*> scale (\x -> x - 1) arbitrary
                   , Singleton <$> arbitrary <*> arbitrary
                   , return VarArg
                   , return Unconstrained
                   , return Conflict
                   ]

    shrink (Fix f) =
        toList f ++
        case f of
            PointerF a          -> [Pointer a' | a' <- shrink a]
            SizedF a l          -> [Sized a' l | a' <- shrink a]
            QualifiedF qs a     -> [Qualified qs' a | qs' <- shrink qs] ++
                                   [Qualified qs a' | a' <- shrink a]
            ArrayF m ds         -> [Array m' ds | m' <- shrink m] ++
                                   [Array m ds' | ds' <- shrink ds]
            VarF l a            -> [Var l a' | a' <- shrink a]
            FunctionF r ps      -> [Function r' ps | r' <- shrink r] ++
                                   [Function r ps' | ps' <- shrink ps]
            TemplateF (FT t m)  -> [Template t m' | m' <- shrink m]
            TypeRefF r l args   -> [TypeRef r l args' | args' <- shrink args]
            ProxyF a            -> [a' | a' <- shrink a]
            _                   -> []

pattern TypeRef :: TypeRef -> Lexeme (TemplateId p) -> [TypeInfo p] -> TypeInfo p
pattern TypeRef r l args = Fix (TypeRefF r l args)

pattern Pointer :: TypeInfo p -> TypeInfo p
pattern Pointer a = Fix (PointerF a)

pattern Sized :: TypeInfo p -> Lexeme (TemplateId p) -> TypeInfo p
pattern Sized a l = Fix (SizedF a l)

matchQual :: Qualifier -> TypeInfo p -> Maybe (TypeInfo p)
matchQual q (Fix f) = case f of
    QualifiedF qs t | Set.member q qs -> Just $ wrapQualified (Set.delete q qs) t
    _ -> Nothing

pattern Const :: TypeInfo p -> TypeInfo p
pattern Const a <- (matchQual QConst -> Just a) where
    Const a = wrapQualified (Set.singleton QConst) a

pattern Owner :: TypeInfo p -> TypeInfo p
pattern Owner a <- (matchQual QOwner -> Just a) where
    Owner a = wrapQualified (Set.singleton QOwner) a

pattern Nonnull :: TypeInfo p -> TypeInfo p
pattern Nonnull a <- (matchQual QNonnull -> Just a) where
    Nonnull a = wrapQualified (Set.singleton QNonnull) a

pattern Nullable :: TypeInfo p -> TypeInfo p
pattern Nullable a <- (matchQual QNullable -> Just a) where
    Nullable a = wrapQualified (Set.singleton QNullable) a

pattern Qualified :: Set Qualifier -> TypeInfo p -> TypeInfo p
pattern Qualified qs a <- Fix (QualifiedF qs a)
  where Qualified qs a = wrapQualified qs a


pattern BuiltinType :: StdType -> TypeInfo p
pattern BuiltinType s = Fix (BuiltinTypeF s)

pattern ExternalType :: Lexeme (TemplateId p) -> TypeInfo p
pattern ExternalType l = Fix (ExternalTypeF l)

pattern Array :: Maybe (TypeInfo p) -> [TypeInfo p] -> TypeInfo p
pattern Array m args = Fix (ArrayF m args)

pattern Var :: Lexeme (TemplateId p) -> TypeInfo p -> TypeInfo p
pattern Var l a = Fix (VarF l a)

pattern Function :: TypeInfo p -> [TypeInfo p] -> TypeInfo p
pattern Function r ps = Fix (FunctionF r ps)

pattern Template :: TemplateId p -> Maybe (TypeInfo p) -> TypeInfo p
pattern Template l m = Fix (TemplateF (FullTemplate l m))


pattern Singleton :: StdType -> Integer -> TypeInfo p
pattern Singleton s i = Fix (SingletonF s i)

pattern VarArg :: TypeInfo p
pattern VarArg = Fix VarArgF

pattern IntLit :: Lexeme (TemplateId p) -> TypeInfo p
pattern IntLit l = Fix (IntLitF l)

pattern NameLit :: Lexeme (TemplateId p) -> TypeInfo p
pattern NameLit l = Fix (NameLitF l)

pattern EnumMem :: Lexeme (TemplateId p) -> TypeInfo p
pattern EnumMem l = Fix (EnumMemF l)

pattern Unconstrained :: TypeInfo p
pattern Unconstrained = Fix UnconstrainedF

pattern Conflict :: TypeInfo p
pattern Conflict = Fix ConflictF

pattern Proxy :: TypeInfo p -> TypeInfo p
pattern Proxy a = Fix (ProxyF a)

pattern Unsupported :: Text -> TypeInfo p
pattern Unsupported t = Fix (UnsupportedF t)

{-# COMPLETE TypeRef, Pointer, Sized, Const, Owner, Nonnull, Nullable, Qualified, BuiltinType, ExternalType, Array, Var, Function, Template, Singleton, VarArg, IntLit, NameLit, EnumMem, Unconstrained, Conflict, Proxy, Unsupported #-}

data Qualifier = QOwner | QNullable | QNonnull | QConst
    deriving (Show, Read, Eq, Ord, Generic, Enum, Bounded)

instance ToJSON Qualifier
instance FromJSON Qualifier

instance Arbitrary Qualifier where
    arbitrary = arbitraryBoundedEnum
    shrink = genericShrink

instance (Arbitrary lexeme, Arbitrary a) => Arbitrary (TypeInfoF lexeme a) where
    arbitrary = sized $ \n ->
        if n <= 0
        then oneof [ BuiltinTypeF <$> arbitrary
                   , TemplateF <$> arbitrary
                   , pure VarArgF
                   , pure UnconstrainedF
                   , pure ConflictF
                   ]
        else oneof [ TypeRefF <$> arbitrary <*> arbitrary <*> scale (\x -> x - 1) arbitrary
                   , PointerF <$> scale (\x -> x - 1) arbitrary
                   , SizedF <$> scale (\x -> x - 1) arbitrary <*> arbitrary
                   , QualifiedF <$> arbitrary <*> scale (\x -> x - 1) arbitrary
                   , BuiltinTypeF <$> arbitrary
                   , ExternalTypeF <$> arbitrary
                   , ArrayF <$> scale (\x -> x - 1) (oneof [return Nothing, Just <$> arbitrary]) <*> scale (\x -> x - 1) (oneof [return [], (:[]) <$> arbitrary])
                   , VarF <$> arbitrary <*> scale (\x -> x - 1) arbitrary
                   , FunctionF <$> scale (\x -> x - 1) arbitrary <*> scale (\x -> x - 1) (oneof [return [], (:[]) <$> arbitrary])
                   , TemplateF <$> arbitrary
                   , SingletonF <$> arbitrary <*> arbitrary
                   , pure VarArgF
                   , IntLitF <$> arbitrary
                   , NameLitF <$> arbitrary
                   , EnumMemF <$> arbitrary
                   , pure UnconstrainedF
                   , pure ConflictF
                   , ProxyF <$> scale (\x -> x - 1) arbitrary
                   , UnsupportedF <$> (Text.pack <$> arbitrary)
                   ]
    shrink = \case
        TypeRefF r l args -> [TypeRefF r l args' | args' <- shrink args]
        PointerF a -> [PointerF a' | a' <- shrink a]
        SizedF a l -> [SizedF a' l | a' <- shrink a]
        QualifiedF qs a -> [QualifiedF qs' a | qs' <- shrink qs] ++ [QualifiedF qs a' | a' <- shrink a]
        ArrayF m ds -> [ArrayF m' ds | m' <- shrink m] ++ [ArrayF m ds' | ds' <- shrink ds]
        VarF l a -> [VarF l a' | a' <- shrink a]
        FunctionF r ps -> [FunctionF r' ps | r' <- shrink r] ++ [FunctionF r ps' | ps' <- shrink ps]
        TemplateF ft -> [TemplateF ft' | ft' <- shrink ft]
        ProxyF a -> [ProxyF a' | a' <- shrink a]
        _ -> []

instance Arbitrary TypeRef where
    arbitrary = arbitraryBoundedEnum

isConflict :: TypeInfo p -> Bool
isConflict = \case
    Fix ConflictF -> True
    Fix (QualifiedF _ t) -> isConflict t
    Fix (SizedF t _) -> isConflict t
    Fix (VarF _ t) -> isConflict t
    Fix (ProxyF t) -> isConflict t
    _ -> False

isUnconstrained :: TypeInfo p -> Bool
isUnconstrained = \case
    Fix UnconstrainedF -> True
    Fix (QualifiedF _ t) -> isUnconstrained t
    Fix (SizedF t _) -> isUnconstrained t
    Fix (VarF _ t) -> isUnconstrained t
    Fix (ProxyF t) -> isUnconstrained t
    _ -> False

data FlatType p = FlatType
    { ftStructure :: TypeInfoF (TemplateId p) (TypeInfo p)
    , ftQuals     :: Set Qualifier
    , ftSize      :: Maybe (Lexeme (TemplateId p))
    } deriving (Show, Eq, Generic)

toFlat :: TypeInfo p -> FlatType p
toFlat ty = go Set.empty Nothing (normalizeType ty)
  where
    go qs sz (Fix f) = case f of
        UnconstrainedF -> FlatType UnconstrainedF (normalizeQuals (Set.insert QNonnull qs)) Nothing
        ConflictF      -> FlatType ConflictF (normalizeQuals (Set.insert QNullable $ Set.insert QConst $ Set.insert QOwner qs)) Nothing
        BuiltinTypeF NullPtrTy | QNonnull `Set.member` qs -> FlatType UnconstrainedF (normalizeQuals qs) Nothing
        SingletonF NullPtrTy 0 | QNonnull `Set.member` qs -> FlatType UnconstrainedF (normalizeQuals qs) Nothing
        QualifiedF qs' t -> go (qs <> qs') sz t
        SizedF t l  -> go qs (sz <|> Just l) t
        VarF _ t    -> go qs sz t
        ProxyF t    -> go qs sz t
        _           ->
            let qs' = case f of
                        PointerF _  -> qs
                        TemplateF _ -> qs
                        TypeRefF {} -> qs
                        FunctionF {} -> Set.insert QNonnull qs
                        ArrayF {}    -> Set.insert QNonnull qs
                        _           -> Set.filter (\q -> q == QConst || q == QNonnull || q == QNullable) qs
            in FlatType f (normalizeQuals qs') sz

normalizeQuals :: Set Qualifier -> Set Qualifier
normalizeQuals qs =
    if Set.member QNullable qs then Set.delete QNonnull qs else qs

wrapQualified :: Set Qualifier -> TypeInfo p -> TypeInfo p
wrapQualified qs (Fix (QualifiedF qs' t)) = wrapQualified (qs <> qs') t
wrapQualified qs (Fix (SizedF t l))       = Sized (wrapQualified qs t) l
wrapQualified _ (Fix UnconstrainedF)      = Unconstrained
wrapQualified _ (Fix ConflictF)           = Conflict
wrapQualified qs t                        | Set.null qs = t
wrapQualified qs t                        = Fix (QualifiedF (normalizeQuals qs) t)

normalizeType :: TypeInfo p -> TypeInfo p
normalizeType = foldFix $ \case
    ArrayF Nothing ds -> Array (Just Unconstrained) ds
    QualifiedF qs t   -> wrapQualified qs t
    SizedF t (C.L _ cl l) -> Fix $ SizedF t (C.L (C.AlexPn 0 0 0) cl l)
    VarF _ t          -> t
    ProxyF t    -> t
    TypeRefF r (C.L _ cl t) args -> Fix $ TypeRefF r (C.L (C.AlexPn 0 0 0) cl t) args

    ExternalTypeF (C.L _ cl t) -> Fix $ ExternalTypeF (C.L (C.AlexPn 0 0 0) cl t)
    IntLitF (C.L _ cl t) -> Fix $ IntLitF (C.L (C.AlexPn 0 0 0) cl t)
    NameLitF (C.L _ cl t) -> Fix $ NameLitF (C.L (C.AlexPn 0 0 0) cl t)
    EnumMemF (C.L _ cl t) -> Fix $ EnumMemF (C.L (C.AlexPn 0 0 0) cl t)
    f                 -> Fix f

stripLexemes :: TypeInfo p -> TypeInfo p
stripLexemes = foldFix $ \case
    TypeRefF r (C.L _ cl t) args -> Fix $ TypeRefF r (C.L (C.AlexPn 0 0 0) cl t) args
    SizedF a (C.L _ cl t) -> Fix $ SizedF a (C.L (C.AlexPn 0 0 0) cl t)
    ExternalTypeF (C.L _ cl t) -> Fix $ ExternalTypeF (C.L (C.AlexPn 0 0 0) cl t)
    VarF (C.L _ cl t) a -> Fix $ VarF (C.L (C.AlexPn 0 0 0) cl t) a
    IntLitF (C.L _ cl t) -> Fix $ IntLitF (C.L (C.AlexPn 0 0 0) cl t)
    NameLitF (C.L _ cl t) -> Fix $ NameLitF (C.L (C.AlexPn 0 0 0) cl t)
    EnumMemF (C.L _ cl t) -> Fix $ EnumMemF (C.L (C.AlexPn 0 0 0) cl t)
    f -> Fix f

fromFlat :: FlatType p -> TypeInfo p
fromFlat (FlatType ConflictF _ _) = Conflict
fromFlat (FlatType UnconstrainedF _ _) = Unconstrained
fromFlat (FlatType s qs sz) =
    let base = Fix (normalizeStructure s)
        withQuals = if Set.null qs then base else Qualified qs base
    in maybe withQuals (Sized withQuals) sz
  where
    normalizeStructure (ArrayF Nothing ds) = ArrayF (Just Unconstrained) ds
    normalizeStructure f                   = f

data Invariant (p :: Phase)
    = InvCallable (TypeInfo p) [TypeInfo p] (TypeInfo p)
    | InvEquality (TypeInfo p) (TypeInfo p)
    | InvSubtype (TypeInfo p) (TypeInfo p)
    | InvCoordinatedPair (TypeInfo p) (TypeInfo p) (TypeInfo p)
    deriving (Show, Eq, Ord, Generic)

instance ToJSON (Invariant p) where
    toJSON = genericToJSON defaultOptions

instance FromJSONTemplateId p => FromJSON (Invariant p) where
    parseJSON = genericParseJSON defaultOptions

mapInvariant :: (TypeInfo p -> TypeInfo q) -> Invariant p -> Invariant q
mapInvariant f = \case
    InvCallable ft as rt -> InvCallable (f ft) (map f as) (f rt)
    InvEquality t1 t2     -> InvEquality (f t1) (f t2)
    InvSubtype t1 t2      -> InvSubtype (f t1) (f t2)
    InvCoordinatedPair tr a e -> InvCoordinatedPair (f tr) (f a) (f e)

mapInvariantM :: Monad m => (TypeInfo p -> m (TypeInfo q)) -> Invariant p -> m (Invariant q)
mapInvariantM f = \case
    InvCallable ft as rt -> InvCallable <$> f ft <*> mapM f as <*> f rt
    InvEquality t1 t2     -> InvEquality <$> f t1 <*> f t2
    InvSubtype t1 t2      -> InvSubtype <$> f t1 <*> f t2
    InvCoordinatedPair tr a e -> InvCoordinatedPair <$> f tr <*> f a <*> f e

data TypeDescr (p :: Phase)
    = StructDescr (Lexeme Text) [TemplateId p] [(Lexeme Text, TypeInfo p)] [Invariant p]
    | UnionDescr (Lexeme Text) [TemplateId p] [(Lexeme Text, TypeInfo p)] [Invariant p]
    | EnumDescr (Lexeme Text) [TypeInfo p]
    | IntDescr (Lexeme Text) StdType
    | FuncDescr (Lexeme Text) [TemplateId p] (TypeInfo p) [TypeInfo p]
    | AliasDescr (Lexeme Text) [TemplateId p] (TypeInfo p)
    deriving (Show, Eq, Generic)

instance ToJSON (TypeDescr p) where
    toJSON = genericToJSON defaultOptions

instance FromJSONTemplateId p => FromJSON (TypeDescr p) where
    parseJSON = genericParseJSON defaultOptions

type TypeSystem = Map Text (TypeDescr 'Global)

isVoid :: TypeInfo p -> Bool
isVoid = foldFix $ \case
    BuiltinTypeF VoidTy -> True
    QualifiedF _ t      -> t
    VarF _ t            -> t
    SizedF t _          -> t
    _                   -> False

getTemplateVars :: TypeInfo p -> [FullTemplate p]
getTemplateVars ty =
    let (_, (_, res, _)) = State.runState (snd (foldFix alg ty) (TIdAnonymous 0 (Just ""))) (Set.empty, [], 0)
    in reverse res
  where
    alg :: TypeInfoF (TemplateId p) (TypeInfo p, TemplateId p -> State.State (Set (FullTemplate p), [FullTemplate p], Int) ()) -> (TypeInfo p, TemplateId p -> State.State (Set (FullTemplate p), [FullTemplate p], Int) ())
    alg f = (Fix (fmap fst f), \hint -> case f of
        VarF l (_, getInner) -> getInner (TIdAnonymous 0 (Just (templateIdBaseName (C.lexemeText l))))
        TemplateF (FullTemplate t mi) -> do
            let i' = fmap fst mi
                k = FullTemplate t i'
            (seen, acc, next) <- State.get
            if Set.member k seen then return ()
            else do
                State.put (Set.insert k seen, k : acc, next)
                maybe (return ()) (\(_, getInner) -> getInner hint) mi
        PointerF (orig, getInner) | isVoid orig -> do
            (seen, acc, next) <- State.get
            let tid = TIdAnonymous next (templateIdHint hint)
                k = FullTemplate tid Nothing
            State.put (Set.insert k seen, k : acc, next + 1)
            getInner hint
        _ -> mapM_ (\(_, getInner) -> getInner hint) (toList f))

collectUniqueTemplateVars :: [TypeInfo p] -> [FullTemplate p]
collectUniqueTemplateVars tys =
    let (_, (_, res, _)) = State.runState (mapM_ (\t -> snd (foldFix alg t) (TIdAnonymous 0 (Just ""))) tys) (Set.empty, [], 0)
    in reverse res
  where
    alg :: TypeInfoF (TemplateId p) (TypeInfo p, TemplateId p -> State.State (Set (FullTemplate p), [FullTemplate p], Int) ()) -> (TypeInfo p, TemplateId p -> State.State (Set (FullTemplate p), [FullTemplate p], Int) ())
    alg f = (Fix (fmap fst f), \hint -> case f of
        VarF l (_, getInner) -> getInner (TIdAnonymous 0 (Just (templateIdBaseName (C.lexemeText l))))
        TemplateF (FullTemplate t mi) -> do
            let i' = fmap fst mi
                k = FullTemplate t i'
            (seen, acc, next) <- State.get
            if Set.member k seen then return ()
            else do
                State.put (Set.insert k seen, k : acc, next)
                maybe (return ()) (\(_, getInner) -> getInner hint) mi
        PointerF (orig, getInner) | isVoid orig -> do
            (seen, acc, next) <- State.get
            let tid = TIdAnonymous next (templateIdHint hint)
                k = FullTemplate tid Nothing
            State.put (Set.insert k seen, k : acc, next + 1)
            getInner hint
        _ -> mapM_ (\(_, getInner) -> getInner hint) (toList f))
