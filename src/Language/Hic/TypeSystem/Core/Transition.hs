{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE RecordWildCards #-}
module Language.Hic.TypeSystem.Core.Transition
    ( module Language.Hic.TypeSystem.Core.Transition.Types
    , stepTransition
    , toRigid
    , fromRigid
    ) where

import           Data.Fix                                         (Fix (..))
import           Data.Functor                                     (void)
import           Data.Maybe                                       (fromMaybe)
import           Data.Set                                         (Set)
import qualified Data.Set                                         as Set
import           Data.Text                                        (Text)
import qualified Data.Text                                        as Text
import qualified Debug.Trace                                      as Debug
import           Language.Cimple                                  (Lexeme (..))
import           Language.Hic.Core.TypeSystem                     (FlatType (..),
                                                                   FullTemplateF (..),
                                                                   Qualifier (..),
                                                                   StdType (..),
                                                                   TemplateId (..),
                                                                   TypeInfo,
                                                                   TypeInfoF (..),
                                                                   TypeRef (..),
                                                                   toFlat)
import qualified Language.Hic.TypeSystem.Core.Base                as TS (isInt)
import           Language.Hic.TypeSystem.Core.Qualification       (Constness (..),
                                                                   Nullability (..),
                                                                   Ownership (..),
                                                                   QualState (..),
                                                                   allowCovariance,
                                                                   fromQuals,
                                                                   stepQual,
                                                                   toQuals)
import           Language.Hic.TypeSystem.Core.Transition.Atoms
import           Language.Hic.TypeSystem.Core.Transition.Types
import           Language.Hic.TypeSystem.Core.Transition.Variance

debugging :: Bool
debugging = False

dtrace :: String -> a -> a
dtrace msg x = if debugging then Debug.trace msg x else x

-- | Projects a TypeInfo into its RigidNode form (one level).
toRigid :: TypeInfo p -> Maybe (RigidNodeF (TemplateId p) (TypeInfo p))
toRigid ty =
    let FlatType structure quals size = toFlat ty
        (nullability, ownership, constness) = toQuals quals
    in case structure of
        UnconstrainedF -> Just $ RSpecial SUnconstrained
        ConflictF      -> Just $ RSpecial SConflict
        FunctionF r ps -> Just $ RFunction r ps constness size
        UnsupportedF _ -> Just $ RSpecial SConflict
        _ -> RValue <$> toValueStructure structure nullability ownership <*> pure constness <*> pure size

toValueStructure :: TypeInfoF tid a -> Nullability -> Ownership -> Maybe (ValueStructure tid a)
toValueStructure structure n o = case structure of
    TypeRefF r l args -> Just $ VTypeRef r l args
    PointerF a        -> Just $ VPointer a n o
    BuiltinTypeF s    -> Just $ VBuiltin s
    ExternalTypeF l   -> Just $ VExternal l
    ArrayF m ds       -> Just $ VArray m ds
    TemplateF ft      -> Just $ VTemplate ft n o
    SingletonF s i    -> Just $ VSingleton s i
    IntLitF l         -> Just $ VIntLit l
    NameLitF l        -> Just $ VNameLit l
    EnumMemF l        -> Just $ VEnumMem l
    VarArgF           -> Just $ VVarArg
    _                 -> Nothing

-- | Reconstructs a TypeInfo from a RigidNode.
fromRigid :: (a -> TypeInfo p) -> RigidNodeF (TemplateId p) a -> TypeInfo p
fromRigid f = \case
    RFunction r ps c s -> fromValueNode' f r ps c s
    RValue v c s   -> fromValueNode f v c s
    RSpecial s     -> fromSpecialNode s

fromValueNode' :: (a -> TypeInfo p) -> a -> [a] -> Constness -> Maybe (Lexeme (TemplateId p)) -> TypeInfo p
fromValueNode' f r ps c s =
    let base = Fix (FunctionF (f r) (map f ps))
        qs = fromQuals QUnspecified QNonOwned' c
        withQuals = if Set.null qs then base else Fix (QualifiedF qs base)
    in maybe withQuals (Fix . SizedF withQuals) s

fromValueNode :: (a -> TypeInfo p) -> ValueStructure (TemplateId p) a -> Constness -> Maybe (Lexeme (TemplateId p)) -> TypeInfo p
fromValueNode f v c s =
    let (base, n, o) = fromValueStructure f v
        qs = fromQuals n o c
        withQuals = if Set.null qs then base else Fix (QualifiedF qs base)
    in maybe withQuals (Fix . SizedF withQuals) s

fromValueStructure :: (a -> TypeInfo p) -> ValueStructure (TemplateId p) a -> (TypeInfo p, Nullability, Ownership)
fromValueStructure f = \case
    VBuiltin s       -> (Fix (BuiltinTypeF s), QUnspecified, QNonOwned')
    VPointer a n o   -> (Fix (PointerF (f a)), n, o)
    VTemplate ft n o -> (Fix (TemplateF (fmap f ft)), n, o)
    VTypeRef r l as  -> (Fix (TypeRefF r l (map f as)), QUnspecified, QNonOwned')
    VArray m ds      -> (Fix (ArrayF (fmap f m) (map f ds)), QUnspecified, QNonOwned')
    VSingleton s i   -> (Fix (SingletonF s i), QUnspecified, QNonOwned')
    VExternal l      -> (Fix (ExternalTypeF l), QUnspecified, QNonOwned')
    VIntLit l        -> (Fix (IntLitF l), QUnspecified, QNonOwned')
    VNameLit l       -> (Fix (NameLitF l), QUnspecified, QNonOwned')
    VEnumMem l       -> (Fix (EnumMemF l), QUnspecified, QNonOwned')
    VVarArg          -> (Fix VarArgF, QUnspecified, QNonOwned')

fromSpecialNode :: SpecialNode -> TypeInfo p
fromSpecialNode = \case
    SUnconstrained -> Fix UnconstrainedF
    SConflict      -> Fix ConflictF

nodeQual :: RigidNodeF tid a -> Constness
nodeQual = \case
    RValue _ c _ -> c
    RFunction _ _ c _ -> c
    _ -> QMutable'

nodeWithQual :: RigidNodeF tid a -> Constness -> RigidNodeF tid a
nodeWithQual n c = case n of
    RValue v _ s      -> RValue v c s
    RFunction r p _ s -> RFunction r p c s
    _                 -> n

-- | The core transition function for the product automaton.
stepTransition :: (Eq tid, Show tid, Eq a, Show a, Ord a)
               => ProductState
               -> (a -> Maybe (RigidNodeF tid a)) -- ^ Rigid node lookup
               -> (a -> (Nullability, Ownership, Constness)) -- ^ Lookup quals for children
               -> (a, a) -- ^ (bot, top)
               -> Bool -- ^ True if nodes are strictly identical
               -> RigidNodeF tid a
               -> RigidNodeF tid a
               -> RigidNodeF tid (a, a, ProductState)
stepTransition ps lookupNode getQuals terminals identical nL nR =
    let res = step ps lookupNode getQuals terminals identical nL nR
    in dtrace ("stepTransition: ps=" ++ show ps ++ " nL=" ++ show (void nL) ++ " nR=" ++ show (void nR) ++ " -> res=" ++ show (void res)) res

step :: (Eq tid, Show tid, Eq a, Show a, Ord a)
     => ProductState
     -> (a -> Maybe (RigidNodeF tid a))
     -> (a -> (Nullability, Ownership, Constness))
     -> (a, a)
     -> Bool
     -> RigidNodeF tid a
     -> RigidNodeF tid a
     -> RigidNodeF tid (a, a, ProductState)
step ps@ProductState{..} lookupNode getQuals terminals isStrictlyIdentical nL nR
    | isIdentityFor psPolarity nL = stepSpecial ps getQuals terminals nR True
    | isIdentityFor psPolarity nR = stepSpecial ps getQuals terminals nL False
    | isZeroFor psPolarity nL || isZeroFor psPolarity nR = zero ps
    | otherwise = case (nL, nR) of
        (RValue vL cL sL, RValue vR cR sR) ->
            case stepValueStructure ps lookupNode getQuals terminals cL cR vL vR of
                Just (resV, identLV, identRV) ->
                    let resC = case psPolarity of { PJoin -> max cL cR; PMeet -> min cL cR }
                        resC' = if psForceConst then QConst' else resC
                        (resS, sizeConflict) = case psPolarity of
                            PJoin -> (if sL == sR then sL else Nothing, False)
                            PMeet -> case (sL, sR) of
                                (Just l1, Just l2) -> if l1 == l2 then (Just l1, False) else (Nothing, True)
                                (Just l, Nothing)  -> (Just l, False)
                                (Nothing, Just l)  -> (Just l, False)
                                (Nothing, Nothing) -> (Nothing, False)

                        forceConstJoin = psPolarity == PJoin && not (isStrictlyIdentical || (identLV && identRV && cL == cR) || (isNull vL && isNull vR)) && not (allowCovariance psQualL || allowCovariance psQualR)
                        resC'' = if forceConstJoin then QConst' else resC'

                        identL = isStrictlyIdentical || (identLV && cL == resC'') || isNull vL
                        identR = isStrictlyIdentical || (identRV && cR == resC'') || isNull vR

                        invarianceL = not (psForceConst || allowCovariance psQualL)
                        invarianceR = not (psForceConst || allowCovariance psQualR)

                    in if sizeConflict || (invarianceL && not identL) || (invarianceR && not identR) then zero ps
                       else RValue resV resC'' resS
                Nothing -> zero ps

        (RFunction rL pL cL sL, RFunction rR pR cR sR) ->
            if length pL /= length pR then zero ps
            else
                let resC = case psPolarity of { PJoin -> max cL cR; PMeet -> min cL cR }
                    resC' = if psForceConst then QConst' else resC

                    forceConstJoin = psPolarity == PJoin && not (isStrictlyIdentical || (rL == rR && pL == pR && cL == cR)) && not (allowCovariance psQualL || allowCovariance psQualR)
                    resC'' = if forceConstJoin then QConst' else resC'

                    identL = isStrictlyIdentical || (cL == resC'')
                    identR = isStrictlyIdentical || (cR == resC'')

                    invarianceL = not (psForceConst || allowCovariance psQualL)
                    invarianceR = not (psForceConst || allowCovariance psQualR)

                    psRes = ps { psQualL = QualTop, psQualR = QualTop, psForceConst = False }
                    psContra = psRes { psPolarity = flipPol psPolarity }

                    (resS, sizeConflict) = case psPolarity of
                        PJoin -> (if sL == sR then sL else Nothing, False)
                        PMeet -> case (sL, sR) of
                            (Just l1, Just l2) -> if l1 == l2 then (Just l1, False) else (Nothing, True)
                            (Just l, Nothing)  -> (Just l, False)
                            (Nothing, Just l)  -> (Just l, False)
                            (Nothing, Nothing) -> (Nothing, False)
                in if sizeConflict || (invarianceL && not identL) || (invarianceR && not identR) then zero ps
                   else RFunction (rL, rR, psRes) (zipWith (\l r -> (l, r, psContra)) pL pR) resC'' resS

        _ -> zero ps

-- | Handles stepping through an identity node (Unconstrained in Join, Conflict in Meet).
-- This ensures that the identity acts as a neutral element even inside structures.
stepSpecial :: (Eq tid, Eq a, Show a, Ord a)
            => ProductState
            -> (a -> (Nullability, Ownership, Constness)) -- ^ Qualifier lookup
            -> (a, a)
            -> RigidNodeF tid a
            -> Bool -- ^ True if nL was identity
            -> RigidNodeF tid (a, a, ProductState)
stepSpecial ps getQuals terminals n isLeft =
    let c = nodeQual n
        resC = if psForceConst ps then QConst' else c
        n' = nodeWithQual n resC
        ident = if psPolarity ps == PJoin then fst terminals else snd terminals
    in fmap (\child ->
        let (ps', _) = if isLeft
                       then getTargetState ps terminals getQuals QMutable' c ident child
                       else getTargetState ps terminals getQuals c QMutable' child ident
            resPs = if isLeft then ps' { psQualL = QualTop } else ps' { psQualR = QualTop }
            resTriple = if isLeft then (ident, child, resPs) else (child, ident, resPs)
        in resTriple) n'

isNull :: ValueStructure tid a -> Bool
isNull (VBuiltin NullPtrTy)     = True
isNull (VSingleton NullPtrTy _) = True
isNull _                        = False

stepValueStructure :: (Eq tid, Eq a, Show a, Ord a)
                   => ProductState
                   -> (a -> Maybe (RigidNodeF tid a))
                   -> (a -> (Nullability, Ownership, Constness))
                   -> (a, a)
                   -> Constness
                   -> Constness
                   -> ValueStructure tid a
                   -> ValueStructure tid a
                   -> Maybe (ValueStructure tid (a, a, ProductState), Bool, Bool)
stepValueStructure ps@ProductState{..} _ getQuals terminals cL cR sL sR =
    let bot = fst terminals
        top = snd terminals
        isIdentity t = t == (if psPolarity == PJoin then bot else top)
        isNeutral' t = isIdentity t
    in case mergeAtoms ps sL sR of
        Just (res, identL, identR) -> Just (fmap (\x -> (x, x, ps)) res, identL, identR)
        Nothing -> case (sL, sR) of
            (VPointer tL nL oL, VPointer tR nR oR) ->
                let (resState, canJoin) = getTargetState ps terminals getQuals cL cR tL tR
                    resN = case psPolarity of { PJoin -> max nL nR; PMeet -> min nL nR }
                    resO = case psPolarity of { PJoin -> max oL oR; PMeet -> min oL oR }
                    identL = tL == tR || isNeutral' tR || isNeutral' tL
                    identR = tR == tL || isNeutral' tL || isNeutral' tR
                in if canJoin then Just (VPointer (tL, tR, resState) resN resO, identL, identR)
                   else Nothing

            (VPointer tL nullL oL, VArray mR dsR) ->
                let tR = fromMaybe bot mR
                    (resState, canJoin) = getTargetState ps terminals getQuals cL cR tL tR
                    resN = case psPolarity of { PJoin -> max nullL QUnspecified; PMeet -> min nullL QUnspecified }
                    resO = case psPolarity of { PJoin -> max oL QNonOwned'; PMeet -> min oL QNonOwned' }
                    identL = (tL == tR || isNeutral' tR || isNeutral' tL) && null dsR
                    identR = (tR == tL || isNeutral' tL || isNeutral' tR) && null dsR
                in if canJoin then case psPolarity of
                    PJoin -> Just (VPointer (tL, tR, resState) resN resO, identL, identR)
                    PMeet -> Just (VArray (Just (tL, tR, resState)) (map (\r -> (top, r, ps { psQualL = QualTop, psQualR = QualTop })) dsR), identL, identR)
                   else Nothing

            (VArray mL dsL, VPointer tR nullR oR) ->
                let tL = fromMaybe bot mL
                    (resState, canJoin) = getTargetState ps terminals getQuals cL cR tL tR
                    resN = case psPolarity of { PJoin -> max QUnspecified nullR; PMeet -> min QUnspecified nullR }
                    resO = case psPolarity of { PJoin -> max QNonOwned' oR; PMeet -> min QNonOwned' oR }
                    identL = (tL == tR || isNeutral' tR || isNeutral' tL) && null dsL
                    identR = (tR == tL || isNeutral' tL || isNeutral' tR) && null dsL
                in if canJoin then case psPolarity of
                    PJoin -> Just (VPointer (tL, tR, resState) resN resO, identL, identR)
                    PMeet -> Just (VArray (Just (tL, tR, resState)) (map (\l -> (l, top, ps { psQualL = QualTop, psQualR = QualTop })) dsL), identL, identR)
                   else Nothing

            (VArray mL dsL, VArray mR dsR) ->
                let tL = fromMaybe bot mL
                    tR = fromMaybe bot mR
                    (resState, canJoin) = getTargetState ps terminals getQuals cL cR tL tR
                    isNeutralL = isNeutral' tL
                    isNeutralR = isNeutral' tR
                in if not canJoin then Nothing
                   else case psPolarity of
                    PJoin ->
                        let resDs = if length dsL == length dsR then zipWith (\l r -> (l, r, ps { psQualL = QualTop, psQualR = QualTop })) dsL dsR
                                    else if null dsL && isNeutralL then map (\r -> (bot, r, ps { psQualL = QualTop, psQualR = QualTop })) dsR
                                    else if null dsR && isNeutralR then map (\l -> (l, bot, ps { psQualL = QualTop, psQualR = QualTop })) dsL
                                    else []
                            resM = case (mL, mR) of { (Nothing, Nothing) -> Nothing; _ -> Just (tL, tR, resState) }
                            identL = (tL == tR || isNeutralR || isNeutralL) && (length dsL == length dsR || (null dsL && isNeutralL))
                            identR = (tR == tL || isNeutralL || isNeutralR) && (length dsL == length dsR || (null dsR && isNeutralR))
                        in Just (VArray resM resDs, identL, identR)
                    PMeet ->
                        let resDs = if null dsL then map (\r -> (top, r, ps { psQualL = QualTop, psQualR = QualTop })) dsR
                                    else if null dsR then map (\l -> (l, top, ps { psQualL = QualTop, psQualR = QualTop })) dsL
                                    else if length dsL == length dsR then zipWith (\l r -> (l, r, ps { psQualL = QualTop, psQualR = QualTop })) dsL dsR
                                    else []
                            resM = case (mL, mR) of { (Nothing, Nothing) -> Nothing; _ -> Just (tL, tR, resState) }
                            identL = (tL == tR || isNeutralR || isNeutralL) && (null dsL || length dsL == length dsR)
                            identR = (tR == tL || isNeutralL || isNeutralR) && (null dsR || length dsL == length dsR)
                        in if null dsL || null dsR || length dsL == length dsR
                           then Just (VArray resM resDs, identL, identR)
                           else Nothing

            -- nullptr_t vs Pointer/Array (Decay)
            (vL, VPointer tR nullR oR) | isNull vL ->
                let (resState, _) = getTargetState ps terminals getQuals cL cR bot tR
                in case psPolarity of
                    PJoin -> Just (VPointer (bot, tR, resState) QNullable' oR, False, True)
                    PMeet -> if allowCovariance psQualL && allowCovariance psQualR && nullR /= QNonnull'
                             then Just (fmap (\x -> (x, x, ps)) vL, True, False)
                             else Nothing

            (VPointer tL nullL oL, vR) | isNull vR ->
                let (resState, _) = getTargetState ps terminals getQuals cL cR tL bot
                in case psPolarity of
                    PJoin -> Just (VPointer (tL, bot, resState) QNullable' oL, True, False)
                    PMeet -> if allowCovariance psQualL && allowCovariance psQualR && nullL /= QNonnull'
                             then Just (fmap (\x -> (x, x, ps)) vR, False, True)
                             else Nothing

            (vL, VArray mR _) | isNull vL ->
                let tR = fromMaybe bot mR
                    (resState, _) = getTargetState ps terminals getQuals cL cR bot tR
                in case psPolarity of
                    PJoin -> Just (VPointer (bot, tR, resState) QNullable' QNonOwned', False, True)
                    PMeet -> Nothing

            (VArray mL _, vR) | isNull vR ->
                let tL = fromMaybe bot mL
                    (resState, _) = getTargetState ps terminals getQuals cL cR tL bot
                in case psPolarity of
                    PJoin -> Just (VPointer (tL, bot, resState) QNullable' QNonOwned', True, False)
                    PMeet -> Nothing

            -- Identical non-standard constructors (TypeRef, External, etc.)
            (l, r) | void l == void r ->
                Just (fmap (\(a, b) -> (a, b, ps { psForceConst = False })) (zipValueStructures l r), True, True)

            _ -> Nothing

zipValueStructures :: ValueStructure tid a -> ValueStructure tid b -> ValueStructure tid (a, b)
zipValueStructures (VBuiltin s) (VBuiltin _) = VBuiltin s
zipValueStructures (VPointer a n o) (VPointer b _ _) = VPointer (a, b) n o
zipValueStructures (VTemplate ft n o) (VTemplate ft2 _ _) = VTemplate (zipFT ft ft2) n o
zipValueStructures (VTypeRef r l as1) (VTypeRef _ _ as2) = VTypeRef r l (zip as1 as2)
zipValueStructures (VArray m1 ds1) (VArray m2 ds2) = VArray (zipWithMaybe (,) m1 m2) (zip ds1 ds2)
zipValueStructures (VSingleton s i) (VSingleton _ _) = VSingleton s i
zipValueStructures (VExternal l) (VExternal _) = VExternal l
zipValueStructures (VIntLit l) (VIntLit _) = VIntLit l
zipValueStructures (VNameLit l) (VNameLit _) = VNameLit l
zipValueStructures (VEnumMem l) (VEnumMem _) = VEnumMem l
zipValueStructures VVarArg VVarArg = VVarArg
zipValueStructures _ _ = error "zipValueStructures: mismatch"

zipFT :: FullTemplateF tid a -> FullTemplateF tid b -> FullTemplateF tid (a, b)
zipFT (FT tid i1) (FT _ i2) = FT tid (zipWithMaybe (,) i1 i2)

zipWithMaybe :: (a -> b -> c) -> Maybe a -> Maybe b -> Maybe c
zipWithMaybe f (Just a) (Just b) = Just (f a b)
zipWithMaybe _ _ _               = Nothing

flipPol :: Polarity -> Polarity
flipPol PJoin = PMeet
flipPol PMeet = PJoin

zero :: ProductState -> RigidNodeF tid (a, b, ProductState)
zero ps = case psPolarity ps of
    PJoin -> RSpecial SConflict
    PMeet -> RSpecial SUnconstrained
