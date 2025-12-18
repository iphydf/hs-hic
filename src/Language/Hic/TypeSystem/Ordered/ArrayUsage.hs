{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms   #-}
module Language.Hic.TypeSystem.Ordered.ArrayUsage
    ( ArrayUsageResult (..)
    , ArrayFlavor (..)
    , ArrayIdentity (..)
    , runArrayUsageAnalysis
    ) where

import           Control.Applicative               ((<|>))
import           Control.Monad.State.Strict        (State, execState)
import qualified Control.Monad.State.Strict        as State
import           Data.Aeson                        (ToJSON, ToJSONKey)
import           Data.Fix                          (foldFix)
import           Data.Map.Strict                   (Map)
import qualified Data.Map.Strict                   as Map
import           Data.Set                          (Set)
import qualified Data.Set                          as Set
import           Data.Text                         (Text)
import qualified Data.Text                         as T
import           GHC.Generics                      (Generic)
import           Language.Cimple                   (Lexeme (..), Node,
                                                    NodeF (..))
import qualified Language.Cimple                   as C
import qualified Language.Cimple.Program           as Program
import           Language.Hic.Core.AstUtils        (parseInteger)
import           Language.Hic.Core.TypeSystem      (Phase (..), StdType (..),
                                                    TypeDescr (..), TypeInfo,
                                                    TypeRef (..), TypeSystem,
                                                    pattern BuiltinType,
                                                    pattern Pointer,
                                                    pattern TypeRef)
import qualified Language.Hic.TypeSystem.Core.Base as TS

data ArrayFlavor
    = FlavorHomogeneous   -- Only variable indices
    | FlavorHeterogeneous  -- Only literal indices
    | FlavorMixed         -- Both literal and variable indices
    deriving (Show, Eq, Generic)

instance ToJSON ArrayFlavor

data ArrayIdentity
    = GlobalArray Text
    | MemberArray Text Text -- StructName, MemberName
    | LocalArray Text Text  -- FunctionName, VarName
    deriving (Show, Eq, Ord, Generic)

instance ToJSON ArrayIdentity
instance ToJSONKey ArrayIdentity

data ArrayUsageResult = ArrayUsageResult
    { aurFlavors  :: Map ArrayIdentity ArrayFlavor
    , aurAccesses :: Map ArrayIdentity (Set (Maybe Integer))
    } deriving (Show, Generic)

instance ToJSON ArrayUsageResult

data AnalysisState = AnalysisState
    { asAccesses    :: Map ArrayIdentity (Set (Maybe Integer))
    , asTypeSystem  :: TypeSystem
    , asCurrentFunc :: Maybe Text
    , asLocalVars   :: [Map Text (TypeInfo 'Global)]
    }

type Analyze = State AnalysisState

enterScope :: Analyze ()
enterScope = State.modify $ \s -> s { asLocalVars = Map.empty : asLocalVars s }

exitScope :: Analyze ()
exitScope = State.modify $ \s -> s { asLocalVars = drop 1 (asLocalVars s) }

addVar :: Text -> TypeInfo 'Global -> Analyze ()
addVar name ty = State.modify $ \s ->
    case asLocalVars s of
        (m:ms) -> s { asLocalVars = Map.insert name ty m : ms }
        []     -> s { asLocalVars = [Map.singleton name ty] }

lookupVar :: Text -> Analyze (Maybe (TypeInfo 'Global))
lookupVar name = do
    vars <- State.gets asLocalVars
    return $ foldl (\acc m -> acc <|> Map.lookup name m) Nothing vars

data Result = Result
    { resAction   :: Analyze ()
    , resType     :: Analyze (Maybe (TypeInfo 'Global))
    , resId       :: Analyze (Maybe ArrayIdentity)
    , resIdx      :: Maybe Integer
    , resTypeInfo :: TypeInfo 'Global
    , resNode     :: NodeF (Lexeme Text) Result
    }

runArrayUsageAnalysis :: TypeSystem -> Program.Program Text -> ArrayUsageResult
runArrayUsageAnalysis ts program =
    let initialState = AnalysisState Map.empty ts Nothing [Map.empty]
        finalState = execState (mapM_ (mapM_ traverseNode . snd) (Program.toList program)) initialState
        flavors = Map.map categorize (asAccesses finalState)
    in ArrayUsageResult flavors (asAccesses finalState)
  where
    categorize indices =
        let hasLiteral = any (\case Just _ -> True; _ -> False) indices
            hasVariable = Set.member Nothing indices
        in case (hasLiteral, hasVariable) of
            (True, True)  -> FlavorMixed
            (True, False) -> FlavorHeterogeneous
            _             -> FlavorHomogeneous

    traverseNode :: Node (Lexeme Text) -> Analyze ()
    traverseNode = resAction . foldFix alg

    alg :: NodeF (Lexeme Text) Result -> Result
    alg node = Result
        { resAction = doAction node
        , resType   = doType node
        , resId     = doId node
        , resIdx    = doIdx node
        , resTypeInfo = doTypeInfo node
        , resNode   = node
        }

    doAction = \case
        C.FunctionDefn _ proto body -> do
            case resNode proto of
                C.FunctionPrototype _ (L _ _ name) params -> do
                    oldFunc <- State.gets asCurrentFunc
                    oldVars <- State.gets asLocalVars
                    let globalScope = case oldVars of
                            (g:_) -> g
                            []    -> error "traverseNode: Scope stack empty"
                    State.modify $ \s -> s { asCurrentFunc = Just name, asLocalVars = [globalScope] }
                    enterScope
                    mapM_ registerParam params
                    resAction body
                    State.modify $ \s -> s { asCurrentFunc = oldFunc, asLocalVars = oldVars }
                _ -> resAction body

        C.CompoundStmt stmts -> do
            enterScope
            mapM_ resAction stmts
            exitScope

        C.VarDeclStmt r mInit -> do
            case resNode r of
                C.VarDecl ty (L _ _ name) _ -> do
                    let t = resTypeInfo ty
                    addVar name t
                    mapM_ resAction mInit
                _ -> mapM_ resAction mInit

        C.ForStmt init' cond step body -> do
            enterScope
            resAction init'
            resAction cond
            resAction step
            resAction body
            exitScope

        C.ArrayAccess base idx -> do
            resAction base
            resAction idx
            mId <- resId base
            let mIdx = resIdx idx
            case mId of
                Just ident -> State.modify $ \s ->
                    s { asAccesses = Map.insertWith Set.union ident (Set.singleton mIdx) (asAccesses s) }
                Nothing -> return ()

        other -> mapM_ resAction other

    doType = \case
        C.VarExpr (L _ _ name) -> lookupVar name
        C.ParenExpr e -> resType e
        C.MemberAccess obj (L _ _ field) -> do
            mTy <- resType obj
            case mTy of
                Just (TypeRef _ (L _ _ tid) _) -> lookupMemberType (TS.templateIdBaseName tid) field
                _ -> return Nothing
        C.PointerAccess obj (L _ _ field) -> do
            mTy <- resType obj
            case mTy of
                Just (Pointer (TypeRef _ (L _ _ tid) _)) -> lookupMemberType (TS.templateIdBaseName tid) field
                Just (TypeRef _ (L _ _ tid) _) -> lookupMemberType (TS.templateIdBaseName tid) field
                _ -> return Nothing
        _ -> return Nothing

    doId = \case
        C.VarExpr (L _ _ name) -> do
            mFunc <- State.gets asCurrentFunc
            return $ Just $ case mFunc of
                Just f  -> LocalArray f name
                Nothing -> GlobalArray name
        C.MemberAccess obj (L _ _ field) -> do
            mObjTy <- resType obj
            case mObjTy of
                Just (TypeRef _ (L _ _ tid) _) ->
                    return $ Just $ MemberArray (TS.templateIdBaseName tid) field
                _ -> return Nothing
        C.PointerAccess obj (L _ _ field) -> do
            mObjTy <- resType obj
            case mObjTy of
                Just (Pointer (TypeRef _ (L _ _ tid) _)) ->
                    return $ Just $ MemberArray (TS.templateIdBaseName tid) field
                Just (TypeRef _ (L _ _ tid) _) ->
                    return $ Just $ MemberArray (TS.templateIdBaseName tid) field
                _ -> return Nothing
        C.ParenExpr e -> resId e
        _ -> return Nothing

    doIdx = \case
        C.LiteralExpr C.Int (L _ _ val) -> parseInteger val
        C.ParenExpr e -> resIdx e
        _ -> Nothing

    doTypeInfo = \case
        C.TyStd l -> TS.builtin l
        C.TyPointer t -> TS.Pointer (resTypeInfo t)
        C.TyStruct (L p t name) -> TS.TypeRef TS.StructRef (L p t (TS.TIdName name)) []
        C.TyUserDefined (L p t name) -> TS.TypeRef TS.UnresolvedRef (L p t (TS.TIdName name)) []
        _ -> BuiltinType VoidTy

    registerParam r = case resNode r of
        C.VarDecl ty (L _ _ name) _ -> do
            let t = resTypeInfo ty
            addVar name t
        C.NonNullParam p -> registerParam p
        C.NullableParam p -> registerParam p
        _ -> return ()

    lookupMemberType structName field = do
        ts' <- State.gets asTypeSystem
        return $ TS.lookupMemberType field =<< TS.lookupType structName ts'

