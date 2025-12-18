{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
module Language.Hic.Pretty
    ( ppNode
    , showNode
    , showNodePlain
    ) where

import           Data.Fix                      (foldFix)
import           Data.Text                     (Text)
import qualified Data.Text                     as T
import qualified Language.Cimple               as C
import qualified Language.Cimple.Pretty        as CP
import           Language.Hic.Ast
import           Prettyprinter
import           Prettyprinter.Render.Terminal (AnsiStyle, renderStrict)

ppLexeme :: Pretty a => C.Lexeme a -> Doc AnsiStyle
ppLexeme = pretty . C.lexemeText

ppNode :: Pretty a => Node (C.Lexeme a) -> Doc AnsiStyle
ppNode = foldFix $ \case
    CimpleNode f -> CP.ppNodeF f
    HicNode h    -> ppHicNode h

ppHicNode :: Pretty a => HicNode (C.Lexeme a) (Doc AnsiStyle) -> Doc AnsiStyle
ppHicNode = \case
    Scoped r b c ->
        pretty ("scoped" :: Text) <+> parens (removeSemi r) <+> lbrace <> line <>
        indent 2 b <> (if null c then mempty else line <> vsep (map ppCleanup c)) <> line <> rbrace
    Raise o v r ->
        pretty ("raise" :: Text) <>
        (case o of
            Just out -> parens (out <> comma <+> v)
            Nothing  -> parens v) <+>
        ppReturnIntent r
    Transition f t ->
        (pretty ("transition" :: Text)) <+> f <+> (pretty ("->" :: Text)) <+> t
    TaggedUnion n _tt tf _ut uf m ->
        (pretty ("tagged union" :: Text)) <+> ppLexeme n <+>
        lbrace <> line <>
        indent 2 (
          (pretty ("tag field:" :: Text)) <+> ppLexeme tf <> line <>
          (pretty ("union field:" :: Text)) <+> ppLexeme uf <> line <>
          vsep (map ppMember m)
        ) <> line <> rbrace
    TaggedUnionGet _ _ o _isPtr tf _ _uf m _ ->
        (pretty ("get" :: Text)) <+> o <> dot <> ppLexeme tf <+> (pretty ("==" :: Text)) <+> (pretty ("?" :: Text)) <+> o <> dot <> ppLexeme m
    Match o _isPtr _tf c d ->
        (pretty ("match" :: Text)) <+> o <+> lbrace <> line <>
        indent 2 (vsep (map ppMatchCase c) <> maybe mempty (\def -> line <> (pretty ("default" :: Text)) <+> (pretty ("=>" :: Text)) <+> ppBraced' def) d) <> line <> rbrace
    TaggedUnionMemberAccess o _uf m ->
        o <> dot <> ppLexeme m
    TaggedUnionGetTag _ _ o isPtr tf ->
        let op = if isPtr then pretty ("->" :: Text) else dot
        in (pretty ("get tag" :: Text)) <+> o <> op <> ppLexeme tf
    TaggedUnionConstruct o isPtr _ty tagField tagVal _unionField _member d ->
        let op = if isPtr then pretty ("->" :: Text) else dot
        in o <> op <> ppLexeme tagField <+> equals <+> tagVal <+> (pretty ("<=" :: Text)) <+> d <> semi
    ForEach is _in _c _s cons b hi ->
        let ppI = case cons of
                    [_] -> case is of
                            (i:_) -> if hi then parens (pretty ("index" :: Text) <> comma <+> ppLexeme i) else ppLexeme i
                            []    -> pretty ("<missing iterator>" :: Text)
                    _   -> pretty ("index" :: Text)
            ppC = case cons of
                    [c] -> if hi then (pretty ("enumerate" :: Text)) <> parens c else c
                    _   -> parens (commaSep cons)
        in (pretty ("for_each" :: Text)) <+> ppI <+> (pretty ("in" :: Text)) <+> ppC <+> ppBraced' b
    Find i _in _c _s con p f m ->
        (pretty ("find" :: Text)) <+> ppLexeme i <+> (pretty ("in" :: Text)) <+> con <+> (pretty ("where" :: Text)) <+> p <+> ppBraced' f
        <> maybe mempty (\missing -> space <> (pretty ("else" :: Text)) <+> ppBraced' missing) m
    IterationElement i _ -> ppLexeme i
    IterationIndex _ -> pretty ("index" :: Text)

ppMatchCase :: Pretty a => MatchCase (C.Lexeme a) (Doc AnsiStyle) -> Doc AnsiStyle
ppMatchCase (MatchCase v b) = v <+> (pretty ("=>" :: Text)) <+> ppBraced' b

ppBraced' :: Doc AnsiStyle -> Doc AnsiStyle
ppBraced' b =
    let rendered = renderStrict (layoutPretty defaultLayoutOptions (unAnnotate b))
    in if "{" `T.isPrefixOf` T.strip rendered
       then b
       else lbrace <> line <> indent 2 b <> line <> rbrace

removeSemi :: Doc AnsiStyle -> Doc AnsiStyle
removeSemi doc =
    let rendered = renderStrict (layoutPretty defaultLayoutOptions (unAnnotate doc))
    in if ";" `T.isSuffixOf` T.strip rendered
       then pretty (T.strip (T.dropEnd 1 (T.strip rendered)))
       else doc

commaSep :: [Doc a] -> Doc a
commaSep = hsep . punctuate comma

ppMember :: Pretty a => TaggedUnionMember (C.Lexeme a) (Doc AnsiStyle) -> Doc AnsiStyle
ppMember (TaggedUnionMember e m _t) = ppLexeme e <+> (pretty ("=>" :: Text)) <+> ppLexeme m

ppCleanup :: CleanupAction (Doc AnsiStyle) -> Doc AnsiStyle
ppCleanup (CleanupAction l b) =
    maybe b (\lbl -> lbl <> colon <+> b) l

ppReturnIntent :: ReturnIntent (Doc AnsiStyle) -> Doc AnsiStyle
ppReturnIntent = \case
    ReturnVoid      -> pretty ("return void" :: Text)
    ReturnValue v   -> (pretty ("return" :: Text)) <+> v
    ReturnError e   -> (pretty ("return" :: Text)) <+> e <> semi

showNode :: Pretty a => Node (C.Lexeme a) -> Text
showNode = CP.render . ppNode

showNodePlain :: Pretty a => Node (C.Lexeme a) -> Text
showNodePlain = renderStrict . layoutPretty defaultLayoutOptions . unAnnotate . ppNode
