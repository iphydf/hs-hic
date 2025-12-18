{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData        #-}
module Language.Hic.Inference.Context
    ( Context (..)
    , emptyContext
    , collectContext
    ) where

import           Data.Fix                          (Fix (..))
import           Data.Map.Strict                   (Map)
import qualified Data.Map.Strict                   as Map
import           Data.Text                         (Text)
import qualified Language.Cimple                   as C
import qualified Language.Cimple.Program           as Program
import           Language.Hic.Ast                  (HicNode, Node)
import           Language.Hic.Core.TypeSystem      (TypeSystem)
import qualified Language.Hic.TypeSystem.Core.Base as TS

data Context = Context
    { ctxEnums         :: Map Text [Text]
    , ctxUnions        :: Map Text [Text]
    , ctxTypedefs      :: Map Text (C.Node (C.Lexeme Text))
    -- | Registry of inferred TaggedUnions.
    -- This is populated by the TaggedUnion feature.
    , ctxTaggedUnions  :: Map Text (HicNode (C.Lexeme Text) (Node (C.Lexeme Text)))
    , ctxTypeSystem    :: TypeSystem
    } deriving (Eq, Show)


emptyContext :: Context
emptyContext = Context Map.empty Map.empty Map.empty Map.empty Map.empty

collectContext :: Program.Program Text -> Context
collectContext prog =
    let tus = Program.toList prog
        typeSystem = TS.collect tus
        ctx = foldl (flip collectFile) (emptyContext { ctxTypeSystem = typeSystem }) tus
    in ctx
  where
    collectFile (_, nodes) ctx = foldl (flip collectNode) ctx nodes

    collectNode (Fix node) ctx =
        let ctx' = case node of
                C.EnumDecl name members _ ->
                    ctx { ctxEnums = Map.insert (C.lexemeText name) (map extractEnumMember members) (ctxEnums ctx) }
                C.Union name members ->
                    ctx { ctxUnions = Map.insert (C.lexemeText name) (map extractMemberName members) (ctxUnions ctx) }
                C.Struct name members ->
                    ctx { ctxUnions = Map.insert (C.lexemeText name) (map extractMemberName members) (ctxUnions ctx) }
                C.Typedef ty name _ ->
                    ctx { ctxTypedefs = Map.insert (C.lexemeText name) ty (ctxTypedefs ctx) }
                _ -> ctx
        in foldl (flip collectNode) ctx' node

    extractEnumMember (Fix (C.Enumerator name _)) = C.lexemeText name
    extractEnumMember _                           = ""

    extractMemberName (Fix node) = case node of
        C.MemberDecl (Fix (C.VarDecl _ name _)) Nothing ->
            C.lexemeText name
        _ -> ""
