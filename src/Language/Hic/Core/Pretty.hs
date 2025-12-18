{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE KindSignatures    #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms   #-}
module Language.Hic.Core.Pretty
    ( ppErrorInfo
    , ppTypeError
    , ppContext
    , ppReason
    , ppProvenance
    , explainType
    , ppType
    , ppStdType
    , ppTypeDescr
    , showType
    , renderPlain
    , dedupDocs
    ) where

import           Control.Monad.State.Strict    (State, evalState)
import qualified Control.Monad.State.Strict    as State
import           Data.Fix                      (Fix (..), foldFix)
import qualified Data.Graph                    as Graph
import           Data.Map.Strict               (Map)
import qualified Data.Map.Strict               as Map
import           Data.Maybe                    (mapMaybe)
import           Data.Set                      (Set)
import qualified Data.Set                      as Set
import           Data.Text                     (Text)
import qualified Data.Text                     as T
import qualified Data.Text.IO                  as T
import qualified Data.Tree                     as Tree
import           Language.Cimple               (AlexPosn (..), Lexeme (..),
                                                sloc)
import qualified Language.Cimple               as C
import           Language.Hic.Core.Errors
import           Language.Hic.Core.TypeSystem  (FullTemplate,
                                                FullTemplateF (..),
                                                StdType (..), TemplateId (..),
                                                TypeDescr (..), TypeInfo,
                                                TypeInfoF (..), TypeRef (..),
                                                pattern Array,
                                                pattern BuiltinType,
                                                pattern Const, pattern EnumMem,
                                                pattern ExternalType,
                                                pattern FullTemplate,
                                                pattern Function,
                                                pattern IntLit, pattern NameLit,
                                                pattern Nonnull,
                                                pattern Nullable, pattern Owner,
                                                pattern Pointer,
                                                pattern Singleton,
                                                pattern Sized, pattern Template,
                                                pattern TypeRef,
                                                pattern Unsupported,
                                                pattern Var, pattern VarArg,
                                                templateIdToText)
import qualified Language.Hic.Core.TypeSystem  as TypeSystem
import           Prettyprinter
import           Prettyprinter.Render.Terminal (AnsiStyle, Color (..), bold,
                                                color, renderStrict)

ppLexeme :: Pretty a => C.Lexeme a -> Doc AnsiStyle
ppLexeme = pretty . C.lexemeText

keywordStyle :: Doc AnsiStyle -> Doc AnsiStyle
keywordStyle = annotate (color Magenta)

typeStyle :: Doc AnsiStyle -> Doc AnsiStyle
typeStyle = annotate (color Cyan)

varStyle :: Doc AnsiStyle -> Doc AnsiStyle
varStyle = annotate (color Yellow)

literalStyle :: Doc AnsiStyle -> Doc AnsiStyle
literalStyle = annotate (color Blue)

errorStyle :: Doc AnsiStyle -> Doc AnsiStyle
errorStyle = annotate (color Red <> bold)

locationStyle :: Doc AnsiStyle -> Doc AnsiStyle
locationStyle = annotate (color White <> bold)

ppErrorInfo :: FilePath -> ErrorInfo p -> Maybe Text -> Doc AnsiStyle
ppErrorInfo path ei mSnippet =
    let locStr = case errLoc ei of
                    Just l  -> locationStyle (pretty (sloc path l) <> ":") <> " "
                    Nothing -> locationStyle (pretty path <> ":") <> " "
        interestingCtxs = dedupUnifications $ filterInteresting (errContext ei)
        ctxDocs = map ppContext interestingCtxs
        ctxPart = if null ctxDocs
                 then mempty
                 else line <> indent 2 (vsep ctxDocs)
        errPart = errorStyle (ppTypeError (errType ei))
        explPart = if null (errExplanation ei)
                  then mempty
                  else line <> indent 2 ("where" <+> align (vsep (errExplanation ei)))
        snippetPart = case (mSnippet, errLoc ei) of
            (Just snippet, Just (L (AlexPn _ _ col) _ _)) ->
                let caret = replicate (col - 1) ' ' ++ "^"
                in line <> line <> indent 2 (pretty snippet <> line <> errorStyle (pretty caret))
            _ -> mempty
    in locStr <> errPart <> ctxPart <> explPart <> snippetPart

dedupUnifications :: [Context p] -> [Context p]
dedupUnifications = \case
    [] -> []
    (c1@(InUnification e1 a1 _) : c2@(InUnification e2 a2 _) : rest)
        | e1 == e2 && a1 == a2 -> dedupUnifications (c1:rest)
        | otherwise -> c1 : dedupUnifications (c2:rest)
    (c:cs) -> c : dedupUnifications cs

filterInteresting :: [Context p] -> [Context p]
filterInteresting [] = []
filterInteresting (c:cs) =
    let cs' = filterInteresting cs
    in if isBoring c && any (not . isBoring) cs'
       then cs'
       else c : cs'

isBoring :: Context p -> Bool
isBoring = \case
    InExpr _ -> True
    InStmt _ -> True
    InUnification {} -> False
    _        -> False

ppContext :: Context p -> Doc AnsiStyle
ppContext = \case
    InFile _ -> mempty
    InFunction n -> "in function" <+> squotes (varStyle (pretty n))
    InMacro n -> "in macro" <+> squotes (varStyle (pretty n))
    InMemberAccess n -> "in member access" <+> squotes (varStyle (pretty n))
    InExpr (Fix node) -> "in expression:" <+> ppNodeSnippet node
    InStmt (Fix (C.Return _)) -> "in return statement"
    InStmt (Fix (C.IfStmt _ _ _)) -> "in if statement"
    InStmt (Fix (C.WhileStmt _ _)) -> "in while loop"
    InStmt (Fix (C.ForStmt _ _ _ _)) -> "in for loop"
    InStmt (Fix (C.VarDeclStmt _ _)) -> "in variable declaration"
    InStmt (Fix node) -> "in statement:" <+> ppNodeSnippet node
    InInitializer _ -> "in initializer"
    InUnification e a reason -> "while unifying" <+> ppType e <+> "and" <+> ppType a <+> parens (ppReason reason)

ppReason :: MismatchReason -> Doc AnsiStyle
ppReason = \case
    GeneralMismatch -> "general mismatch"
    ReturnMismatch -> "return type"
    ArgumentMismatch i -> "argument" <+> pretty i
    AssignmentMismatch -> "assignment"
    InitializerMismatch -> "initializer"

ppNodeSnippet :: C.NodeF (Lexeme Text) a -> Doc AnsiStyle
ppNodeSnippet = \case
    C.VarExpr (L _ _ n) -> varStyle (pretty n)
    C.LiteralExpr _ (L _ _ n) -> literalStyle (pretty n)
    C.BinaryExpr _ op _ -> "binary" <+> pretty (show op)
    C.UnaryExpr op _ -> "unary" <+> pretty (show op)
    C.FunctionCall _ _ -> "function call"
    C.AssignExpr _ _ _ -> "assignment"
    C.Return _ -> "return"
    C.IfStmt {} -> "if"
    C.WhileStmt {} -> "while"
    C.ForStmt {} -> "for"
    C.MemberAccess _ (L _ _ n) -> "." <> varStyle (pretty n)
    C.PointerAccess _ (L _ _ n) -> "->" <> varStyle (pretty n)
    _ -> "..."

ppTypeError :: TypeError p -> Doc AnsiStyle
ppTypeError = \case
    TypeMismatch exp' act reason mDetail ->
        let reasonDoc = case reason of
                            GeneralMismatch -> "type mismatch"
                            ReturnMismatch -> "return type mismatch"
                            ArgumentMismatch i -> "argument" <+> literalStyle (pretty i) <+> "type mismatch"
                            AssignmentMismatch -> "assignment type mismatch"
                            InitializerMismatch -> "initializer type mismatch"
            baseErr = reasonDoc <> ":" <+> "expected" <+> ppType exp' <> "," <+> "got" <+> ppType act
        in case mDetail of
            Just detail -> baseErr <> line <> indent 2 (ppMismatchDetail detail)
            Nothing     -> baseErr
    UndefinedVariable n -> "undefined variable:" <+> varStyle (pretty n)
    UndefinedType n -> "undefined type:" <+> typeStyle (pretty n)
    MemberNotFound f ty -> "member" <+> varStyle (pretty f) <+> "not found in type" <+> ppType ty
    NotAStruct ty -> "not a struct or union:" <+> ppType ty
    TooManyArgs exp' act -> "too many arguments in function call: expected" <+> literalStyle (pretty exp') <> "," <+> "got" <+> literalStyle (pretty act)
    TooFewArgs exp' act -> "too few arguments in function call: expected" <+> literalStyle (pretty exp') <> "," <+> "got" <+> literalStyle (pretty act)
    NotALValue -> "assignment to non-lvalue"
    CallingNonFunction n ty -> "calling non-function type:" <+> varStyle (pretty n) <+> parens ("type:" <+> ppType ty)
    SwitchConditionNotIntegral ty -> "switch condition must be an integral type or enum (got" <+> ppType ty <> ")"
    DereferencingNonPointer ty -> "dereferencing non-pointer type:" <+> ppType ty
    ArrayAccessNonArray ty -> "array access on non-array type:" <+> ppType ty
    MacroArgumentMismatch n exp' act -> "macro" <+> varStyle (pretty n) <+> "expected" <+> literalStyle (pretty exp') <+> "arguments, got" <+> literalStyle (pretty act)
    MissingReturnValue ty -> "return statement with no value in function returning" <+> ppType ty
    InfiniteType n ty -> "infinite type detected: template" <+> typeStyle (pretty n) <+> "occurs in" <+> ppType ty
    UnhandledConstruct n -> "unhandled construct:" <+> pretty n
    CustomError msg -> pretty msg
    RefinedVariantMismatch -> "refined variant mismatch"
    RefinedNullabilityMismatch -> "refined nullability mismatch"

ppMismatchDetail :: MismatchDetail p -> Doc AnsiStyle
ppMismatchDetail = \case
    MismatchDetail e a _ Nothing ->
        "types" <+> ppType e <+> "and" <+> ppType a <+> "are incompatible"
    MismatchDetail e a _ (Just (ctx, inner)) ->
        "while checking" <+> ppMismatchContext ctx <+> "of" <+> ppType e <+> "and" <+> ppType a <> ":" <> line <> indent 2 (ppMismatchDetail inner)
    MissingQualifier q _ _ ->
        "actual type is missing" <+> ppQualifier q <+> "qualifier"
    UnexpectedQualifier q _ _ ->
        "actual type has unexpected" <+> ppQualifier q <+> "qualifier"
    BaseMismatch e a ->
        "expected" <+> ppType e <> "," <+> "but got" <+> ppType a
    ArityMismatch e a ->
        "expected" <+> literalStyle (pretty e) <+> "arguments, but got" <+> literalStyle (pretty a)

ppMismatchContext :: MismatchContext -> Doc AnsiStyle
ppMismatchContext = \case
    InPointer -> "pointer target"
    InArray -> "array element"
    InFunctionReturn -> "return type"
    InFunctionParam i -> "parameter" <+> literalStyle (pretty i)

ppQualifier :: Qualifier -> Doc AnsiStyle
ppQualifier = keywordStyle . \case
    QOwner -> "owner"
    QNonnull -> "nonnull"
    QNullable -> "nullable"
    QConst -> "const"

ppProvenance :: Provenance p -> Doc AnsiStyle
ppProvenance = \case
    FromDefinition n (Just (L _ _ _)) -> parens ("definition of" <+> varStyle (pretty n))
    FromDefinition n Nothing -> parens ("definition of" <+> varStyle (pretty n))
    FromContext info -> "due to" <+> ppTypeError (errType info)
    FromInference _ -> parens "inferred from context"
    Builtin -> parens "builtin"

-- | Trace the origin of a type to provide a "Chain of Logic"
explainType :: Map (FullTemplate p) (TypeInfo p, Provenance p) -> TypeInfo p -> [Doc AnsiStyle]
explainType bindings ty =
    let initialKeys = TypeSystem.collectUniqueTemplateVars [ty]
        allTargetTemplates = concatMap (TypeSystem.collectUniqueTemplateVars . return . fst) (Map.elems bindings)
        allKeys = Set.fromList (initialKeys ++ Map.keys bindings ++ allTargetTemplates)

        mkNode key =
            let (tid, mIdx) = (ftId key, ftIndex key) in
            case Map.lookup key bindings of
                Just (target, prov) ->
                    let doc = "template" <+> typeStyle (ppType (Template tid mIdx)) <+> "was bound to" <+> ppType target <+> ppProvenance prov
                        deps = TypeSystem.collectUniqueTemplateVars [target]
                    in (doc, key, deps)
                Nothing ->
                    let doc = case mIdx of
                                Just idx -> "template" <+> pretty (TypeSystem.templateIdToText tid) <+> "indexed by" <+> pretty (showType idx)
                                Nothing  -> "template" <+> typeStyle (pretty (TypeSystem.templateIdToText tid)) <+> "is unbound"
                    in (doc, key, [])

        nodes = map mkNode (Set.toList allKeys)
        (graph, nodeFromVertex, vertexFromKey) = Graph.graphFromEdges nodes

        startVertices = mapMaybe vertexFromKey initialKeys
        forest = Graph.dfs graph startVertices
    in concatMap (Tree.flatten . fmap ((\(d, _, _) -> d) . nodeFromVertex)) forest


ppStdType :: StdType -> Doc AnsiStyle
ppStdType = typeStyle . \case
    VoidTy    -> "void"
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

ppType :: TypeInfo p -> Doc AnsiStyle
ppType = foldFix $ \case
    TypeRefF ref l args ->
        let prefix = keywordStyle $ case ref of
                StructRef -> "struct "
                UnionRef  -> "union "
                EnumRef   -> "enum "
                _         -> ""
        in prefix <> typeStyle (ppLexeme l) <> if null args then mempty else angles (hsep $ punctuate comma args)
    PointerF t -> t <> "*"
    SizedF t l -> t <> brackets (varStyle (ppLexeme l))
    QualifiedF qs t ->
        t <+> hsep (map ppQualifier (Set.toList qs))
    BuiltinTypeF std -> ppStdType std
    ExternalTypeF l -> typeStyle (ppLexeme l)
    ArrayF mt dims ->
        maybe (typeStyle "void") id mt <> hcat (map brackets dims)
    VarF l t -> t <+> varStyle (ppLexeme l)
    FunctionF ret params ->
        ret <> parens (hsep $ punctuate comma params)
    TemplateF (FullTemplate t i) -> typeStyle (pretty t) <> maybe mempty brackets i
    SingletonF std v -> ppStdType std <> "=" <> literalStyle (pretty v)
    VarArgF -> "..."
    IntLitF l -> literalStyle (ppLexeme l)
    NameLitF l -> varStyle (ppLexeme l)
    EnumMemF l -> varStyle (ppLexeme l)
    UnconstrainedF -> errorStyle "unconstrained"
    ConflictF -> errorStyle "conflict"
    ProxyF t -> t
    UnsupportedF msg -> errorStyle "unsupported" <> parens (pretty msg)

ppTypeDescr :: TypeDescr p -> Doc AnsiStyle
ppTypeDescr = \case
    StructDescr l _ mems _ -> keywordStyle "struct" <+> typeStyle (ppLexeme l) <+> lbrace <> line <> indent 2 (vsep (map ppMember mems)) <> line <> rbrace
    UnionDescr l _ mems _  -> keywordStyle "union" <+> typeStyle (ppLexeme l) <+> lbrace <> line <> indent 2 (vsep (map ppMember mems)) <> line <> rbrace
    EnumDescr l _        -> keywordStyle "enum" <+> typeStyle (ppLexeme l)
    IntDescr l std       -> keywordStyle "typedef" <+> ppStdType std <+> typeStyle (ppLexeme l)
    FuncDescr l _ ret ps -> keywordStyle "typedef" <+> ppType ret <+> typeStyle (ppLexeme l) <> parens (hsep $ punctuate comma $ map ppType ps)
    AliasDescr l _ t     -> keywordStyle "typedef" <+> ppType t <+> typeStyle (ppLexeme l)
  where
    ppMember (l, t) = ppType t <+> varStyle (ppLexeme l) <> semi

showType :: TypeInfo p -> Text
showType = renderPlain . ppType

renderPlain :: Doc AnsiStyle -> Text
renderPlain = renderStrict . layoutPretty defaultLayoutOptions . unAnnotate

dedupDocs :: [Doc AnsiStyle] -> [Doc AnsiStyle]
dedupDocs = go Set.empty
  where
    go _ [] = []
    go seen (d:ds) =
        let rendered = renderPlain d
        in if Set.member rendered seen
           then go seen ds
           else d : go (Set.insert rendered seen) ds
