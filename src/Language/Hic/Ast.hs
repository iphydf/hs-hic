{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DeriveTraversable     #-}
{-# LANGUAGE DerivingVia           #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE Strict                #-}
{-# LANGUAGE TemplateHaskell       #-}
module Language.Hic.Ast
    ( Node, NodeF (..)
    , HicNode (..)
    , TaggedUnionMember (..)
    , MatchCase (..)
    , CleanupAction (..)
    , ReturnIntent (..)
    ) where

import           Data.Aeson                   (FromJSON, FromJSON1, ToJSON,
                                               ToJSON1)
import           Data.Aeson.TH                (defaultOptions, deriveJSON1)
import           Data.Bifunctor               (Bifunctor (..))
import           Data.Fix                     (Fix (..), foldFix)
import           Data.Foldable                (fold)
import           Data.Functor.Classes         (Eq1, Ord1, Read1, Show1)
import           Data.Functor.Classes.Generic (FunctorClassesDefault (..))
import           Data.Hashable                (Hashable (..))
import           Data.Hashable.Lifted         (Hashable1)
import           Data.Text                    (Text)
import qualified Data.Text                    as Text
import           GHC.Generics                 (Generic, Generic1)
import qualified Language.Cimple              as C

-- | The High-level Cimple (Hic) AST.
-- It wraps the base Cimple AST and adds a 'HicNode' constructor for lifted constructs.
data NodeF lexeme a
    = CimpleNode (C.NodeF lexeme a)
    | HicNode (HicNode lexeme a)
    deriving (Show, Read, Eq, Ord, Generic, Generic1, Functor, Foldable, Traversable)
    deriving (Show1, Read1, Eq1, Ord1) via FunctorClassesDefault (NodeF lexeme)

instance Bifunctor NodeF where
    bimap f g (CimpleNode cn) = CimpleNode (bimap f g cn)
    bimap f g (HicNode hn)    = HicNode (bimap f g hn)

type Node lexeme = Fix (NodeF lexeme)

instance C.Concats (NodeF lexeme [lexeme]) lexeme where
    concats (CimpleNode f) = C.concats f
    concats (HicNode h)    = C.concats h

instance C.Concats (HicNode lexeme [lexeme]) lexeme where
    concats (Scoped r b c)    = r ++ b ++ concatMap C.concats c
    concats (Raise o v r)     = fold o ++ v ++ C.concats r
    concats (Transition f t)  = f ++ t
    concats (TaggedUnion n tt tf ut uf m) =
        [n] ++ tt ++ [tf] ++ ut ++ [uf] ++ concatMap C.concats m
    concats (TaggedUnionGet _ p o _isPtr tf tv uf m e) = p ++ o ++ [tf] ++ tv ++ [uf] ++ [m] ++ e
    concats (Match o _ tf c d) = o ++ [tf] ++ concatMap C.concats c ++ fold d
    concats (TaggedUnionMemberAccess o uf m) = o ++ [uf] ++ [m]
    concats (TaggedUnionGetTag _ p o _isPtr tf) = p ++ o ++ [tf]
    concats (TaggedUnionConstruct o _isPtr ty tf tv uf m d) = o ++ [ty] ++ [tf] ++ tv ++ [uf] ++ [m] ++ d
    concats (ForEach is in_ c s cons b _hi) = is ++ in_ ++ c ++ s ++ concat cons ++ b
    concats (Find i in_ c s con p f m) = [i] ++ in_ ++ c ++ s ++ con ++ p ++ f ++ fold m
    concats (IterationElement i c) = i : c
    concats (IterationIndex i) = [i]

instance C.Concats (TaggedUnionMember lexeme [lexeme]) lexeme where
    concats (TaggedUnionMember e m t) = [e, m] ++ t

instance C.Concats (MatchCase lexeme [lexeme]) lexeme where
    concats (MatchCase v b) = v ++ b

instance C.Concats (CleanupAction [lexeme]) lexeme where
    concats (CleanupAction l b) = fold l ++ b

instance C.Concats (ReturnIntent [lexeme]) lexeme where
    concats (ReturnValue v) = v
    concats (ReturnError e) = e
    concats ReturnVoid      = []

instance C.HasLocation lexeme => C.HasLocation (Node lexeme) where
    sloc file (n :: Node lexeme) =
        case foldFix (C.concats :: NodeF lexeme [lexeme] -> [lexeme]) n of
            []  -> Text.pack file <> ":0:0"
            l:_ -> C.sloc file (l :: lexeme)

-- | Generic high-level language constructs inferred from C.
data HicNode lexeme a
    -- | A scoped block with mandatory cleanup.
    -- Inferred from: { resource = alloc(); ... if (err) goto CLEANUP; ... CLEANUP: free(resource); }
    = Scoped
        { scopedResource :: a
        , scopedBody     :: a
        , scopedCleanup  :: [CleanupAction a]
        }

    -- | Explicit error propagation.
    | Raise
        { raiseOutParam :: Maybe a
        , raiseValue    :: a
        , raiseReturn   :: ReturnIntent a
        }

    -- | A structured protocol/state-machine transition.
    | Transition
        { transitionFrom :: a
        , transitionTo   :: a
        }

    -- | A tagged union (sum type).
    -- Inferred from: struct { Enum tag; union { ... } data; }
    | TaggedUnion
        { tuName       :: lexeme
        , tuTagType    :: a
        , tuTagField   :: lexeme
        , tuUnionType  :: a
        , tuUnionField :: lexeme
        , tuMembers    :: [TaggedUnionMember lexeme a]
        }

    -- | A type-safe getter for a tagged union member.
    -- Inferred from: Member* get(TaggedUnion *u) { return u->tag == VAL ? u->data.member : NULL; }
    | TaggedUnionGet
        { tugScope      :: C.Scope
        , tugProto      :: a
        , tugObject     :: a
        , tugIsPointer  :: Bool
        , tugTagField   :: lexeme
        , tugTagValue   :: a
        , tugUnionField :: lexeme
        , tugMember     :: lexeme
        , tugElse       :: a
        }

    -- | A pattern match over a tagged union.
    -- Inferred from: switch (u->tag) { case VAL: ... u->data.member ... }
    | Match
        { matchObject   :: a
        , matchIsPtr    :: Bool
        , matchTagField :: lexeme
        , matchCases    :: [MatchCase lexeme a]
        , matchDefault  :: Maybe a
        }

    -- | A high-level access to a member of a tagged union.
    -- Inferred from: u->data.member
    | TaggedUnionMemberAccess
        { tumaObject     :: a
        , tumaUnionField :: lexeme
        , tumaMember     :: lexeme
        }

    -- | Safe access to the tag of a tagged union.
    | TaggedUnionGetTag
        { tugtScope     :: C.Scope
        , tugtProto     :: a
        , tugtObject    :: a
        , tugtIsPointer :: Bool
        , tugtTagField  :: lexeme
        }

    -- | Atomic construction of a tagged union.
    -- Inferred from: *u = (TaggedUnion) { tag, data };
    -- Or coalesced from sequential assignments: u.tag = val; u.data.mem = val;
    | TaggedUnionConstruct
        { tucObject     :: a
        , tucIsPointer  :: Bool
        , tucType       :: lexeme
        , tucTagField   :: lexeme
        , tucTagValue   :: a
        , tucUnionField :: lexeme
        , tucMember     :: lexeme
        , tucDataValue  :: a
        }

    -- | A high-level iteration over one or more collections (zipped).
    -- Inferred from: for (init; cond; step) { ... c1[i] ... c2[i] ... }
    | ForEach
        { feIterators  :: [lexeme]
        , feInit       :: a
        , feCond       :: a
        , feStep       :: a
        , feContainers :: [a]
        , feBody       :: a
        , feHasIndex   :: Bool
        }

    -- | A high-level search operation.
    -- Inferred from: for (init; cond; step) { if (pred) foundAction; } missingAction;
    | Find
        { fIterator  :: lexeme
        , fInit      :: a
        , fCond      :: a
        , fStep      :: a
        , fContainer :: a
        , fPredicate :: a
        , fOnFound   :: a
        , fOnMissing :: Maybe a
        }

    -- | A high-level access to the current element in an iteration.
    | IterationElement
        { ieIterator  :: lexeme
        , ieContainer :: a
        }

    -- | A high-level access to the current index in an iteration.
    | IterationIndex
        { iiIterator :: lexeme
        }

    deriving (Show, Read, Eq, Ord, Generic, Generic1, Functor, Foldable, Traversable)
    deriving (Show1, Read1, Eq1, Ord1) via FunctorClassesDefault (HicNode lexeme)

instance Bifunctor HicNode where
    bimap _ g (Scoped r b c) = Scoped (g r) (g b) (map (fmap g) c)
    bimap _ g (Raise o v r) = Raise (fmap g o) (g v) (fmap g r)
    bimap _ g (Transition fr to) = Transition (g fr) (g to)
    bimap f g (TaggedUnion n tt tf ut uf m) =
        TaggedUnion (f n) (g tt) (f tf) (g ut) (f uf) (map (bimap f g) m)
    bimap f g (TaggedUnionGet sc p o isPtr tf tv uf m e) =
        TaggedUnionGet sc (g p) (g o) isPtr (f tf) (g tv) (f uf) (f m) (g e)
    bimap f g (Match o isPtr tf c d) = Match (g o) isPtr (f tf) (map (bimap f g) c) (fmap g d)
    bimap f g (TaggedUnionMemberAccess o uf m) = TaggedUnionMemberAccess (g o) (f uf) (f m)
    bimap f g (TaggedUnionGetTag sc p o isPtr tf) = TaggedUnionGetTag sc (g p) (g o) isPtr (f tf)
    bimap f g (TaggedUnionConstruct o isPtr ty tf tv uf m d) =
        TaggedUnionConstruct (g o) isPtr (f ty) (f tf) (g tv) (f uf) (f m) (g d)
    bimap f g (ForEach is in_ c s cons b hi) = ForEach (map f is) (g in_) (g c) (g s) (map g cons) (g b) hi
    bimap f g (Find i in_ c s con p found missing) = Find (f i) (g in_) (g c) (g s) (g con) (g p) (g found) (fmap g missing)
    bimap f g (IterationElement i c) = IterationElement (f i) (g c)
    bimap f _ (IterationIndex i) = IterationIndex (f i)

data TaggedUnionMember lexeme a = TaggedUnionMember
    { tumEnumVal :: lexeme
    , tumMember  :: lexeme
    , tumType    :: a
    }
    deriving (Show, Read, Eq, Ord, Generic, Generic1, Functor, Foldable, Traversable)
    deriving (Show1, Read1, Eq1, Ord1) via FunctorClassesDefault (TaggedUnionMember lexeme)

instance Bifunctor TaggedUnionMember where
    bimap f g (TaggedUnionMember e m t) = TaggedUnionMember (f e) (f m) (g t)

data MatchCase lexeme a = MatchCase
    { mcValue :: a
    , mcBody  :: a
    }
    deriving (Show, Read, Eq, Ord, Generic, Generic1, Functor, Foldable, Traversable)
    deriving (Show1, Read1, Eq1, Ord1) via FunctorClassesDefault (MatchCase lexeme)

instance Bifunctor MatchCase where
    bimap _ g (MatchCase v b) = MatchCase (g v) (g b)

data CleanupAction a
    = CleanupAction
        { cleanupLabel :: Maybe a
        , cleanupBody  :: a
        }
    deriving (Show, Read, Eq, Ord, Generic, Generic1, Functor, Foldable, Traversable)
    deriving (Show1, Read1, Eq1, Ord1) via FunctorClassesDefault CleanupAction

data ReturnIntent a
    = ReturnVoid
    | ReturnValue a
    | ReturnError a -- The "sentinel" return value like -1 or nullptr
    deriving (Show, Read, Eq, Ord, Generic, Generic1, Functor, Foldable, Traversable)
    deriving (Show1, Read1, Eq1, Ord1) via FunctorClassesDefault ReturnIntent

instance (Hashable lexeme, Hashable a) => Hashable (NodeF lexeme a)
instance (Hashable lexeme, Hashable a) => Hashable (HicNode lexeme a)
instance (Hashable lexeme, Hashable a) => Hashable (TaggedUnionMember lexeme a)
instance (Hashable lexeme, Hashable a) => Hashable (MatchCase lexeme a)
instance Hashable a => Hashable (CleanupAction a)
instance Hashable a => Hashable (ReturnIntent a)

instance Hashable lexeme => Hashable1 (NodeF lexeme)
instance Hashable lexeme => Hashable1 (HicNode lexeme)
instance Hashable lexeme => Hashable1 (TaggedUnionMember lexeme)
instance Hashable lexeme => Hashable1 (MatchCase lexeme)
instance Hashable1 CleanupAction
instance Hashable1 ReturnIntent

deriveJSON1 defaultOptions ''CleanupAction
deriveJSON1 defaultOptions ''ReturnIntent
deriveJSON1 defaultOptions ''MatchCase
deriveJSON1 defaultOptions ''TaggedUnionMember
deriveJSON1 defaultOptions ''HicNode
deriveJSON1 defaultOptions ''NodeF
