{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData        #-}

-- | C's integer types, on every platform the code builds for: what each type
-- holds, the type arithmetic is done in, and when a conversion or a sum or
-- difference keeps a value.
module Language.Hic.Refined.BufferSize.Integers
    ( Range (..)
    , unknownRange
    , exactly
    , rangeArith
    , arith
    , parseIntLiteral
    , IntType (..)
    , intTypes
    , limits
    , arithmeticHolds
    , promote
    , commonType
    , literalType
    , arithType
    , binaryType
    , within
    , keepsValue
    , noWrap
    , fewestBits
    , hull
    , intersectRange
    , isEmptyRange
    , Cmp (..)
    , comparison
    , negateCmp
    , flipCmp
    , sizeType
    , ptrdiffType
    , intType
    ) where

import           Control.Applicative        ((<|>))
import           Data.Fix                   (Fix (..))
import           Data.List                  (find)
import           Data.Map.Strict            (Map)
import qualified Data.Map.Strict            as Map
import           Data.Maybe                 (isJust, mapMaybe)
import           Data.Text                  (Text)
import qualified Data.Text                  as T
import           Language.Cimple            (Lexeme (..), NodeF (..))
import qualified Language.Cimple            as C
import           Language.Hic.Core.AstUtils (parseInteger)

-- | Bounds of an integer variable.
data Range = Range
    { rLow  :: Maybe Integer
    , rHigh :: Maybe Integer
    }
    deriving (Show, Eq)

unknownRange :: Range
unknownRange = Range Nothing Nothing

exactly :: Integer -> Range
exactly n = Range (Just n) (Just n)

-- | Arithmetic on bounds. Only what can be bounded is: anything else is
-- unknown.
rangeArith :: C.BinaryOp -> Range -> Range -> Range
rangeArith op (Range alo ahi) (Range blo bhi) = case op of
    C.BopPlus  -> Range ((+) <$> alo <*> blo) ((+) <$> ahi <*> bhi)
    C.BopMinus -> Range ((-) <$> alo <*> bhi) ((-) <$> ahi <*> blo)
    C.BopMul | Just x <- alo, Just y <- blo, x >= 0, y >= 0 ->
        Range (Just (x * y)) ((*) <$> ahi <*> bhi)
    C.BopMul | Just a1 <- alo, Just a2 <- ahi, Just b1 <- blo, Just b2 <- bhi ->
        let corners = [a1 * b1, a1 * b2, a2 * b1, a2 * b2]
        in Range (Just (minimum corners)) (Just (maximum corners))
    -- Shifts of a number of at least 0, by as many bits as it can be.
    C.BopLsh | Just x <- alo, x >= 0, Just s1 <- blo, Just s2 <- bhi, s1 >= 0, s2 < 64 ->
        Range (Just (x * 2 ^ s1)) ((* 2 ^ s2) <$> ahi)
    C.BopRsh | Just x <- alo, x >= 0, Just s1 <- blo, s1 >= 0 ->
        Range (Just (maybe 0 (\s2 -> if s2 < 64 then x `div` 2 ^ s2 else 0) bhi)) ((`div` 2 ^ min 64 s1) <$> ahi)
    _ | Just x <- exact alo ahi, Just y <- exact blo bhi -> maybe unknownRange exactly (arith op x y)
    -- What's left of a division by a number, or what a mask keeps.
    C.BopMod | Just lo <- alo, lo >= 0, Just k <- exact blo bhi, k > 0 -> Range (Just 0) (Just (maybe (k - 1) (min (k - 1)) ahi))
    C.BopMod | Just lo <- alo, lo >= 0, Just b1 <- blo, b1 > 0 ->
        Range (Just 0) (case (subtract 1 <$> bhi, ahi) of
            (Just x, Just y) -> Just (min x y)
            (x, y)           -> x <|> y)
    C.BopBitAnd | Just k <- exact blo bhi, k >= 0 -> Range (Just 0) (Just k)
    C.BopBitAnd | Just k <- exact alo ahi, k >= 0 -> Range (Just 0) (Just k)
    -- A quotient by a positive number, rounded towards 0 as C does.
    C.BopDiv | Just b1 <- blo, b1 > 0, maybe True (>= b1) bhi, Just a1 <- alo, Just a2 <- ahi ->
        Range (Just (if a1 >= 0 then maybe 0 (a1 `quot`) bhi else a1 `quot` b1))
              (Just (if a2 >= 0 then a2 `quot` b1 else maybe 0 (a2 `quot`) bhi))
    -- The bits of numbers of at least 0: no more than the larger has, and
    -- for @&@, no more than the smaller is.
    C.BopBitAnd | nonNegative -> Range (Just 0) (min <$> ahi <*> bhi)
    C.BopBitOr | nonNegative -> Range (max <$> alo <*> blo) (bitsOf <$> (max <$> ahi <*> bhi))
    C.BopBitXor | nonNegative -> Range (Just 0) (bitsOf <$> (max <$> ahi <*> bhi))
    _ -> unknownRange
  where
    nonNegative = maybe False (>= 0) alo && maybe False (>= 0) blo
    -- The largest number with no more bits than n.
    bitsOf n = go 1
      where
        go p = if p > n then p - 1 else go (2 * p)
    exact (Just x) (Just y) | x == y = Just x
    exact _ _                        = Nothing

arith :: C.BinaryOp -> Integer -> Integer -> Maybe Integer
arith op x y = case op of
    C.BopPlus  -> Just (x + y)
    C.BopMinus -> Just (x - y)
    C.BopMul   -> Just (x * y)
    C.BopDiv   -> if y == 0 then Nothing else Just (x `quot` y)
    C.BopMod   -> if y == 0 then Nothing else Just (x `rem` y)
    C.BopLsh   -> if y < 0 || y > 64 then Nothing else Just (x * 2 ^ y)
    C.BopRsh   -> if y < 0 || y > 64 then Nothing else Just (x `div` 2 ^ y)
    _          -> Nothing

-- | An integer literal, without its @U@ and @L@ suffixes.
parseIntLiteral :: Text -> Maybe Integer
parseIntLiteral = parseInteger . T.dropWhileEnd (`elem` ("uUlL" :: String))

-- | An integer type, on every platform the code builds for: its conversion
-- rank, whether it's signed, the values it holds on all of them and on any
-- of them, and its size in bytes.
data IntType = IntType
    { itRank    :: Int
    , itSigned  :: Bool
    , itHolds   :: Range
    , itCanHold :: Range
    , itBytes   :: Range
    }
    deriving (Show, Eq)

intTypes :: Map Text IntType
intTypes = Map.fromList $
    [ ("bool", IntType 0 False (Range (Just 0) (Just 1)) (Range (Just 0) (Just 1)) (exactly 1))
    -- Signed or not depending on the platform.
    , ("char", IntType 1 True (Range (Just 0) (Just 127)) (Range (Just (-128)) (Just 255)) (exactly 1))
    ]
    ++ [ (name, sized rank signed bits bits) | (names, rank, signed, bits) <- fixed, name <- names ]
    ++ [ (name, sized 4 signed 32 64) | (name, signed) <- [("long", True), ("unsigned long", False), ("size_t", False), ("ssize_t", True), ("ptrdiff_t", True)] ]
  where
    fixed =
        [ (["int8_t"], 1, True, 8)
        , (["uint8_t"], 1, False, 8)
        , (["int16_t"], 2, True, 16)
        , (["uint16_t"], 2, False, 16)
        , (["int", "signed int", "int32_t"], 3, True, 32)
        , (["unsigned", "unsigned int", "uint32_t"], 3, False, 32)
        , (["long long", "int64_t"], 5, True, 64)
        , (["unsigned long long", "uint64_t"], 5, False, 64)
        ]
    sized rank signed fewest most =
        IntType rank signed (bitsHold signed fewest) (bitsHold signed most) (Range (Just (fewest `div` 8)) (Just (most `div` 8)))
    bitsHold :: Bool -> Integer -> Range
    bitsHold True bits  = Range (Just (negate (2 ^ (bits - 1)))) (Just (2 ^ (bits - 1) - 1))
    bitsHold False bits = Range (Just 0) (Just (2 ^ bits - 1))

-- | The limits of @<stdint.h>@: each one's type and what it is on every
-- platform. Those below an int are ints.
limits :: Map Text (IntType, Range)
limits = Map.fromList $
    [ (prefix <> "INT" <> bits <> suffix, (promote t, bound t))
    | bits <- ["8", "16", "32", "64"]
    , (prefix, signed) <- [("", True), ("U", False)]
    , Just t <- [Map.lookup ((if signed then "int" else "uint") <> bits <> "_t") intTypes]
    , (suffix, bound) <- ("_MAX", exactly' rHigh) : [ ("_MIN", exactly' rLow) | signed ]
    ]
    ++ [ ("SIZE_MAX", (sizeType, Range (rHigh (itHolds sizeType)) (rHigh (itCanHold sizeType)))) ]
  where
    exactly' end t = maybe unknownRange exactly (end (itHolds t))

intType, sizeType, ptrdiffType :: IntType
intType = intTypes Map.! "int"
sizeType = intTypes Map.! "size_t"
ptrdiffType = intTypes Map.! "ptrdiff_t"

-- | What every integer type that arithmetic is done in holds (int and up).
arithmeticHolds :: Range
arithmeticHolds = Range (Just 0) (Just (2 ^ (31 :: Integer) - 1))

-- | An operand as arithmetic sees it: anything smaller than int is an int.
promote :: IntType -> IntType
promote t = if itRank t < itRank intType then intType else t

-- | The type arithmetic on 2 integers is done in.
commonType :: IntType -> IntType -> IntType
commonType x y
    | itSigned a == itSigned b = if itRank a >= itRank b then a else b
    | itRank u >= itRank s = u
    | itCanHold u `within` itHolds s = s
    -- Signed on some platforms and unsigned on others: only what both hold.
    | otherwise = s
        { itSigned = False
        , itHolds = Range (Just 0) (rHigh (itHolds s))
        , itCanHold = Range (rLow (itCanHold s)) ((\hi -> 2 * hi + 1) <$> rHigh (itCanHold s))
        }
  where
    a = promote x
    b = promote y
    (u, s) = if itSigned a then (b, a) else (a, b)

-- | The type of an integer literal: the first that holds it, as C picks.
literalType :: Text -> Maybe IntType
literalType t = do
    n <- parseIntLiteral t
    let suffix = T.toLower (T.takeWhileEnd (`elem` ("uUlL" :: String)) t)
        decimal = T.length t - T.length suffix == 1 || not ("0" `T.isPrefixOf` t)
        names
            | "u" `T.isInfixOf` suffix = ["unsigned int", "unsigned long", "unsigned long long"]
            | decimal = ["int", "long", "long long"]
            | otherwise = ["int", "unsigned int", "long", "unsigned long", "long long", "unsigned long long"]
        longest = itRank intType + T.count "l" suffix
    find (\it -> itRank it >= longest && exactly n `within` itHolds it) (mapMaybe (`Map.lookup` intTypes) names)

-- | The integer type of an arithmetic expression, as C works it out from
-- the types of its parts. Anything else is asked of the given function.
arithType :: (C.Node (Lexeme Text) -> Maybe IntType) -> C.Node (Lexeme Text) -> Maybe IntType
arithType other = go
  where
    go e@(Fix node) = case node of
        LiteralExpr C.Int (L _ _ t) -> literalType t
        LiteralExpr C.Char _ -> Just intType
        ParenExpr x -> go x
        SizeofType _ -> Just sizeType
        SizeofExpr _ -> Just sizeType
        UnaryExpr C.UopNot _ -> Just intType
        UnaryExpr op x | op `elem` [C.UopMinus, C.UopNeg] -> promote <$> go x
        BinaryExpr a op b -> binaryType op (go a) (go b) <|> other e
        TernaryExpr _ a b -> commonType <$> go a <*> go b
        _ -> other e

-- | The type of a binary operation on operands of these types.
binaryType :: C.BinaryOp -> Maybe IntType -> Maybe IntType -> Maybe IntType
binaryType op ta tb
    | isJust (comparison op) || op `elem` [C.BopAnd, C.BopOr] = Just intType
    | op `elem` [C.BopLsh, C.BopRsh] = promote <$> ta
    | otherwise = commonType <$> ta <*> tb

-- | Whether one range is known to be inside another.
within :: Range -> Range -> Bool
within (Range lo hi) (Range outerLo outerHi) =
    and ((>=) <$> lo <*> outerLo) && and ((<=) <$> hi <*> outerHi)
    && isJust lo && isJust hi && isJust outerLo && isJust outerHi

-- | Whether a value keeps its value converted from one integer type to
-- another: if they're the same type, if every value of the one fits the
-- other, or if what's known of the value does.
keepsValue :: Maybe IntType -> Maybe IntType -> Range -> Bool
keepsValue from to r = case to of
    Nothing -> r `within` arithmeticHolds
    Just t  -> from == to || maybe False ((`within` itHolds t) . itCanHold) from || r `within` itHolds t

-- | Whether a sum or difference done in an integer type is the sum or
-- difference of the numbers: it's in what the type holds, or it's between
-- an operand and where the other moves it.
noWrap :: Maybe IntType -> C.BinaryOp -> Range -> Range -> Range -> Bool
noWrap t op ra rb result = (above || grows) && (below || shrinks)
  where
    Range lo hi = maybe arithmeticHolds itHolds t
    above = and ((>=) <$> rLow result <*> lo) && isJust (rLow result) && isJust lo
    below = and ((<=) <$> rHigh result <*> hi) && isJust (rHigh result) && isJust hi
    nonNegative = maybe False (>= 0) . rLow
    nonPositive = maybe False (<= 0) . rHigh
    (grows, shrinks) = case op of
        C.BopPlus  -> (nonNegative ra || nonNegative rb, nonPositive ra || nonPositive rb)
        C.BopMinus -> (nonPositive rb, nonNegative rb)
        _          -> (False, False)

-- | The fewest bits an integer type has; none if it's not known.
fewestBits :: Maybe IntType -> Integer
fewestBits = maybe 0 (* 8) . (>>= rLow . itBytes)

-- | What either of 2 ranges allows.
hull :: Range -> Range -> Range
hull (Range alo ahi) (Range blo bhi) = Range (min <$> alo <*> blo) (max <$> ahi <*> bhi)

-- | Whether a range holds no number at all.
isEmptyRange :: Range -> Bool
isEmptyRange (Range (Just lo) (Just hi)) = lo > hi
isEmptyRange _                           = False

intersectRange :: Range -> Range -> Range
intersectRange (Range alo ahi) (Range blo bhi) = Range (maxM alo blo) (minM ahi bhi)
  where
    maxM x y = (max <$> x <*> y) <|> x <|> y
    minM x y = (min <$> x <*> y) <|> x <|> y

data Cmp = CLt | CLe | CGt | CGe | CEq | CNe
    deriving (Eq)

comparison :: C.BinaryOp -> Maybe Cmp
comparison = \case
    C.BopLt -> Just CLt
    C.BopLe -> Just CLe
    C.BopGt -> Just CGt
    C.BopGe -> Just CGe
    C.BopEq -> Just CEq
    C.BopNe -> Just CNe
    _       -> Nothing

negateCmp :: Cmp -> Cmp
negateCmp = \case
    CLt -> CGe
    CLe -> CGt
    CGt -> CLe
    CGe -> CLt
    CEq -> CNe
    CNe -> CEq

flipCmp :: Cmp -> Cmp
flipCmp = \case
    CLt -> CGt
    CLe -> CGe
    CGt -> CLt
    CGe -> CLe
    c   -> c
