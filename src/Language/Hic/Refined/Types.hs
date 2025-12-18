{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveFoldable     #-}
{-# LANGUAGE DeriveFunctor      #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DeriveTraversable  #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE KindSignatures     #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StrictData         #-}
{-# LANGUAGE TupleSections      #-}

module Language.Hic.Refined.Types
    ( -- * Core Rigid Node
      RigidNodeF (..)
    , AnyRigidNodeF (..)
    , ObjectStructure (..)
    , RefStructure (..)
    , PtrTarget (..)
    , ReturnType (..)
    , TerminalNode (..)
    , PropertyKind (..)
    , StructureKind (..)

      -- * Attributes
    , Quals (..)
    , Nullability (..)
    , Ownership (..)

      -- * Identifiers and Primitives
    , TemplateId (..)
    , LatticePhase (..)
    , Index (..)
    , StdType (..)
    ) where

import           Data.Aeson         (ToJSON (..))
import           Data.Hashable      (Hashable)
import           Data.IntMap.Strict (IntMap)
import           Data.Map.Strict    (Map)
import qualified Data.Map.Strict    as Map
import           Data.Text          (Text)
import           Data.Word          (Word32)
import           GHC.Generics       (Generic)
import           Language.Cimple    (Lexeme (..))

-- | Standard C base types supported by the solver.
data StdType
    = BoolTy
    | CharTy
    | U08Ty | S08Ty
    | U16Ty | S16Ty
    | U32Ty | S32Ty
    | U64Ty | S64Ty
    | SizeTy
    | F32Ty | F64Ty
    | NullPtrTy  -- ^ Semantic type for null pointer constants
    deriving (Show, Read, Eq, Ord, Generic, Bounded, Enum)

instance Hashable StdType
instance ToJSON StdType

-- | Classification of type structures for compile-time safety.
data StructureKind = KObject | KReference | KFunction
    deriving (Show, Eq, Ord, Generic, Bounded, Enum)

instance Hashable StructureKind

-- | The core layered attribute model for the Refined Type System.
-- Kind-Indexed GADT to enforce 'Correct-by-Construction' invariants.
-- Notation: τ ::= RObject(σ, q) | RReference(ρ, n, o, q) | RFunction(args, ret) | ⊥ | ⊤
data RigidNodeF (k :: StructureKind) tid a where
    RObject    :: ObjectStructure tid a -> Quals -> RigidNodeF 'KObject tid a
    RReference :: RefStructure tid a -> Nullability -> Ownership -> Quals -> RigidNodeF 'KReference tid a
    RFunction  :: [a] -> ReturnType a -> RigidNodeF 'KFunction tid a
    RTerminal  :: TerminalNode a -> RigidNodeF k tid a

-- | Existential wrapper for 'RigidNodeF' to allow homogeneous storage (e.g. Maps).
-- Notation: ∃k. RigidNodeF(k, tid, a)
data AnyRigidNodeF tid a where
    AnyRigidNodeF :: RigidNodeF k tid a -> AnyRigidNodeF tid a

deriving instance (Show tid, Show a) => Show (RigidNodeF k tid a)
deriving instance (Eq tid, Eq a)     => Eq (RigidNodeF k tid a)
deriving instance (Ord tid, Ord a)   => Ord (RigidNodeF k tid a)
deriving instance Functor (RigidNodeF k tid)
deriving instance Foldable (RigidNodeF k tid)
deriving instance Traversable (RigidNodeF k tid)

deriving instance (Show tid, Show a) => Show (AnyRigidNodeF tid a)
instance (Eq tid, Eq a) => Eq (AnyRigidNodeF tid a) where
    (AnyRigidNodeF l) == (AnyRigidNodeF r) =
        case (l, r) of
            (RObject s1 q1, RObject s2 q2) -> s1 == s2 && q1 == q2
            (RReference s1 n1 o1 q1, RReference s2 n2 o2 q2) -> s1 == s2 && n1 == n2 && o1 == o2 && q1 == q2
            (RFunction a1 r1, RFunction a2 r2) -> a1 == a2 && r1 == r2
            (RTerminal t1, RTerminal t2) -> t1 == t2
            _ -> False

instance (Ord tid, Ord a) => Ord (AnyRigidNodeF tid a) where
    compare (AnyRigidNodeF l) (AnyRigidNodeF r) =
        case (l, r) of
            (RObject s1 q1, RObject s2 q2) -> compare (s1, q1) (s2, q2)
            (RObject{}, _) -> LT
            (_, RObject{}) -> GT
            (RReference s1 n1 o1 q1, RReference s2 n2 o2 q2) -> compare (s1, n1, o1, q1) (s2, n2, o2, q2)
            (RReference{}, _) -> LT
            (_, RReference{}) -> GT
            (RFunction a1 r1, RFunction a2 r2) -> compare (a1, r1) (a2, r2)
            (RFunction{}, _) -> LT
            (_, RFunction{}) -> GT
            (RTerminal t1, RTerminal t2) -> compare t1 t2

instance Functor (AnyRigidNodeF tid) where
    fmap f (AnyRigidNodeF n) = AnyRigidNodeF (fmap f n)
instance Foldable (AnyRigidNodeF tid) where
    foldMap f (AnyRigidNodeF n) = foldMap f n
instance Traversable (AnyRigidNodeF tid) where
    traverse f (AnyRigidNodeF n) = AnyRigidNodeF <$> traverse f n

-- | Object Structure represents values (Structs, Enums, Builtins).
-- Correct-by-construction: Functions and Void are not objects.
-- Notation:
--   σ ::= Builtin(T) | Singleton(T, i) | Nominal(L, params) | Var(tid, index)
--       | ∃tid. σ | Σ (tag -> type) | PSize(τ) | Σ ci*Pi + k
data ObjectStructure tid a
    = VBuiltin   StdType
    | VSingleton StdType Integer         -- ^ Refined literal (e.g., '0')
    | VNominal   (Lexeme tid) [a]        -- ^ Nominal types with parameters
    | VEnum      (Lexeme tid)
    | VVar       tid (Maybe (Index tid)) -- ^ Type variable with optional index
    | VExistential [tid] a               -- ^ ∃T. a (Hides parameters in 'a')
    | VVariant     (IntMap a)            -- ^ Tag-to-Type mapping (Refined Union)
    | VProperty   a PropertyKind         -- ^ Algebraic metadata (sizeof, alignof)
    | VSizeExpr   [(a, Integer)]         -- ^ Pure linear expression: Σ (Ci * Propertyi)
    deriving (Show, Eq, Ord, Generic, Functor, Foldable, Traversable)

instance (ToJSON tid, ToJSON a) => ToJSON (ObjectStructure tid a)

-- | Kinds of algebraic properties derived from types.
-- Notation: PSize | PAlign | POffset(f)
data PropertyKind = PSize | PAlign | POffset Text
    deriving (Show, Eq, Ord, Generic)

instance Hashable PropertyKind
instance ToJSON PropertyKind

-- | Reference Structure represents indirection (Pointers and Arrays).
-- Notation: ρ ::= Arr(a, dims) | Ptr(target)
data RefStructure tid a
    = Arr a [a] -- ^ Element type (must resolve to RObject), Dimensions
    | Ptr (PtrTarget tid a)
    deriving (Show, Eq, Ord, Generic, Functor, Foldable, Traversable)

instance (ToJSON tid, ToJSON a) => ToJSON (RefStructure tid a)

-- | Valid targets for a pointer.
-- Notation: TargetObject(a) | TargetFunction(sig) | TargetOpaque(tid)
data PtrTarget tid a
    = TargetObject   a                   -- ^ Pointer to a value (must be RObject)
    | TargetFunction [a] (ReturnType a)  -- ^ Pointer to a function: args, return
    | TargetOpaque   tid                 -- ^ Semantic replacement for void*
    deriving (Show, Eq, Ord, Generic, Functor, Foldable, Traversable)

instance (ToJSON tid, ToJSON a) => ToJSON (PtrTarget tid a)

-- | Possible return types for a function.
-- Notation: RetVal(τ) | RetVoid
data ReturnType a where
    RetVal  :: a -> ReturnType a
    RetVoid :: ReturnType a

deriving instance Show a => Show (ReturnType a)
deriving instance Eq a   => Eq (ReturnType a)
deriving instance Ord a  => Ord (ReturnType a)
deriving instance Functor ReturnType
deriving instance Foldable ReturnType
deriving instance Traversable ReturnType

instance ToJSON a => ToJSON (ReturnType a) where
    toJSON (RetVal a) = toJSON a
    toJSON RetVoid    = "void"

-- | Absolute lattice terminals.
data TerminalNode a
    = SBottom
    | SAny         -- ^ Lattice Top (Universal supertype, Identity for Meet)
    | SConflict    -- ^ Absorbing Error State (Inescapable conflict)
    | STerminal a  -- ^ Deferred product state (e.g., recursive meet)
    deriving (Show, Eq, Ord, Generic, Functor, Foldable, Traversable)

instance ToJSON a => ToJSON (TerminalNode a)

-- | Immutability bitfield.
data Quals = Quals { qConst :: Bool, qPhysical :: Bool }
    deriving (Show, Eq, Ord, Generic)

instance ToJSON Quals

-- | Nullability Lattice: Nonnull < Unspecified < Nullable
data Nullability = QNonnull' | QUnspecified | QNullable'
    deriving (Show, Eq, Ord, Generic, Bounded, Enum)

instance ToJSON Nullability

-- | Ownership states for linear types.
data Ownership = QNonOwned' | QOwned'
    deriving (Show, Eq, Ord, Generic, Bounded, Enum)

instance ToJSON Ownership

-- | Indexing for polymorphic variables (e.g., cbs[i]).
data Index tid
    = ILit Integer
    | IVar tid
    deriving (Show, Eq, Ord, Generic, Functor, Foldable, Traversable)

instance ToJSON tid => ToJSON (Index tid)

-- | Phase of analysis for template identification.
data LatticePhase = PGlobal | PLocal
    deriving (Show, Read, Eq, Ord, Generic, Bounded, Enum)

instance Hashable LatticePhase
instance ToJSON LatticePhase

-- | Unique identity for templates and refined variables.
-- Supports locally stable Skolem variables for bisimulation.
data TemplateId
    = TIdName Text
    | TIdParam LatticePhase Word32 (Maybe Text)
    | TIdSkolem {
        skParentL :: Word32, -- ^ ID of the left parent node in product
        skParentR :: Word32, -- ^ ID of the right parent node in product
        skIndex   :: Word32  -- ^ Index of the binder
      }
    | TIdInstance Integer    -- ^ Bind to a unique pointer instance ID
    | TIdDeBruijn Word32     -- ^ Canonicalized variable for memoization
    deriving (Show, Eq, Ord, Generic)

instance Hashable TemplateId
instance ToJSON TemplateId
