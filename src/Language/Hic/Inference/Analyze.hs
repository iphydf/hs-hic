{-# LANGUAGE LambdaCase #-}
module Language.Hic.Inference.Analyze
    ( nodeName
    ) where

import           Language.Hic.Ast (HicNode (..))

nodeName :: HicNode lexeme a -> String
nodeName = \case
    Scoped{}         -> "Scoped"
    Raise{}          -> "Raise"
    Transition{}     -> "Transition"
    TaggedUnion{}    -> "TaggedUnion"
    TaggedUnionGet{} -> "TaggedUnionGet"
    Match{}          -> "Match"
    TaggedUnionMemberAccess{} -> "TaggedUnionMemberAccess"
    TaggedUnionGetTag{} -> "TaggedUnionGetTag"
    TaggedUnionConstruct{} -> "TaggedUnionConstruct"
    ForEach{}        -> "ForEach"
    Find{}           -> "Find"
    IterationElement{} -> "IterationElement"
    IterationIndex{} -> "IterationIndex"
