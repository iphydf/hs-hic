{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData        #-}

-- | What's known at a point in a function: where pointers point, bounds of
-- integer variables, and sums of them known to be at least a bound.
module Language.Hic.Refined.BufferSize.Facts
    ( Lin (..)
    , linConstant
    , linVar
    , linPlus
    , linScale
    , linMinus
    , linMentions
    , Size (..)
    , elements
    , Pointer (..)
    , offsetVar
    , noneVar
    , Facts (..)
    , noFacts
    , normalise
    , substitute
    , lowerLin
    , upperLin
    , rangeOfLin
    , lowerBound
    , advance
    , arrayOrigin
    , joinFacts
    , joinLoopFacts
    , joinPointer
    , widenFacts
    , widenFactsKeeping
    , keepingEntry
    , same
    , forgetInt
    , forgetVar
    , setRange
    , setLinear
    , addIneq
    , settle
    , equate
    , setIntLin
    , moveInt
    , setPointer
    , setNewPointer
    , comparableOrigin
    ) where

import           Control.Applicative                      ((<|>))
import           Control.Monad                            ((>=>))
import           Data.Containers.ListUtils                (nubOrd)
import qualified Data.List                                as List
import           Data.Map.Strict                          (Map)
import qualified Data.Map.Strict                          as Map
import           Data.Maybe                               (catMaybes)
import qualified Data.Set                                 as Set
import           Data.Text                                (Text)
import qualified Data.Text                                as T
import qualified Language.Cimple                          as C
import           Language.Hic.Refined.BufferSize.Integers
import           Text.Read                                (readMaybe)

-- | A sum of integer variables, each with a coefficient, plus a constant.
data Lin = Lin
    { linVars  :: Map Text Integer
    , linConst :: Integer
    }
    deriving (Show, Eq, Ord)

linConstant :: Integer -> Lin
linConstant = Lin Map.empty

linVar :: Text -> Lin
linVar v = Lin (Map.singleton v 1) 0

linPlus :: Lin -> Lin -> Lin
linPlus (Lin a c) (Lin b d) = Lin (Map.filter (/= 0) (Map.unionWith (+) a b)) (c + d)

linScale :: Integer -> Lin -> Lin
linScale k (Lin a c) = Lin (Map.filter (/= 0) (Map.map (* k) a)) (k * c)

linMinus :: Lin -> Lin -> Lin
linMinus a b = linPlus a (linScale (-1) b)

linMentions :: Text -> Lin -> Bool
linMentions v = Map.member v . linVars

-- | At least how many elements a pointer has.
data Size
    = Size Lin
    | NullPointer
      -- ^ Says nothing about size: whether it may be null is the
      -- nullability check's.
    deriving (Show, Eq)

elements :: Integer -> Size
elements = Size . linConstant

-- | Where a pointer variable points: into a buffer, from a position in it
-- (its origin) that has at least so many elements after it. How far the
-- pointer is from there is the integer variable 'offsetVar'.
data Pointer = Pointer
    { ptOrigin :: Text
    , ptBase   :: Size
    }
    deriving (Show, Eq)

offsetVar :: Text -> Text
offsetVar p = p <> "@"

-- | Whether a variable is still the number for none ('unlessNone'): its
-- z, if what was said of them is as it was.
noneVar :: Text -> Integer -> Text
noneVar v k = v <> "=" <> T.pack (show k)

-- | The variable and number a 'noneVar' is of.
noneOf :: Text -> Maybe (Text, Integer)
noneOf z = case T.breakOnEnd "=" z of
    (pre, k) | Just v <- T.stripSuffix "=" pre, not (T.null v), Just n <- readMaybe (T.unpack k) -> Just (v, n)
    _ -> Nothing

-- | Whether an integer variable is a pointer's 'offsetVar'.
isOffsetVar :: Text -> Bool
isOffsetVar = T.isSuffixOf "@"

data Facts
    = Unreached
    | Facts
        { fPointers :: Map Text Pointer
        , fInts     :: Map Text Range
        , fLinear   :: Map Text (Text, Integer)
          -- ^ Integer variables known to be another one plus a constant.
        , fIneqs    :: Map (Map Text Integer) Integer
          -- ^ Sums of integer variables (with coefficients) known to be at
          -- least a bound.
        , fDefs     :: Map Text Lin
          -- ^ Integer variables known to be a sum of more than one other.
          -- The sums known of them say it too: this is to work out bounds
          -- with, and goes when any of them changes.
        }
    deriving (Show, Eq)

noFacts :: Facts
noFacts = Facts Map.empty Map.empty Map.empty Map.empty Map.empty

-- | A sum with what's known exactly put in: a variable made from another
-- (v = w + c) as that one, a variable with one value as the value. Only
-- for working out bounds: a sum kept as a fact stays as written.
normalise :: Facts -> Lin -> Lin
normalise Unreached l = l
normalise facts l = substitute known (substitute made l)
  where
    made v = case Map.lookup v (fLinear facts) of
        Just (w, d) -> linPlus (linVar w) (linConstant d)
        Nothing     -> linVar v
    known v = case Map.lookup v (fInts facts) of
        Just (Range (Just lo) (Just hi)) | lo == hi -> linConstant lo
        _                                           -> linVar v

substitute :: (Text -> Lin) -> Lin -> Lin
substitute f (Lin vars c) = foldl' (\acc (v, k) -> linPlus acc (linScale k (f v))) (linConstant c) (Map.toList vars)

-- | The least a sum can be: from the bounds of its variables, or from a
-- known sum and the bounds of what's left. A variable that is a sum of
-- others is tried as itself, and as that sum. What it takes from the facts
-- is worked out once for all the sums asked of the same facts.
lowerLin :: Facts -> Lin -> Maybe Integer
lowerLin Unreached = const Nothing
lowerLin facts = \l -> case catMaybes (unscaled l : [ (`ceilDiv` s) <$> unscaled (linScale s l) | s <- scales l ]) of
    []     -> Nothing
    bounds -> Just (maximum bounds)
  where
    direct = lowerWith (normalise facts) made facts
    throughDefs = lowerWith expanded (made >=> parts >=> parts >=> made) facts
    unscaled x
        | Map.null (fDefs facts) = direct x
        | otherwise = case catMaybes [direct x, throughDefs x] of
            []     -> Nothing
            bounds -> Just (maximum bounds)
    -- For one variable, a known sum with it so many times over, which only
    -- l that many times over can take whole: l >= b / s.
    manyTimes = Map.fromListWith (++) [ (x, [n]) | g <- Map.keys (fIneqs facts), (x, n) <- Map.toList g, abs n > 1 ]
    scales l = case Map.toList (linVars l) of
        [(x, m)] -> nubOrd [ q | n <- Map.findWithDefault [] x manyTimes, (q, 0) <- [n `quotRem` m], q > 1 ]
        _        -> []
    ceilDiv b s = negate (negate b `div` s)
    expanded = normalise facts . substitute defined . substitute defined . normalise facts
    defined v = Map.findWithDefault (linVar v) v (fDefs facts)
    made v = [maybe v fst (Map.lookup v (fLinear facts))]
    parts v = maybe [v] (Map.keys . linVars) (Map.lookup v (fDefs facts))

-- | The least a sum can be, with the sums made the same way by a function
-- and, for each variable, those that may stand for it after.
lowerWith :: (Lin -> Lin) -> (Text -> [Text]) -> Facts -> Lin -> Maybe Integer
lowerWith norm into facts = \l ->
    let Lin vars c = norm l
        -- Known sums g >= b in the same terms as l, each so many times
        -- over as takes a variable out of what's left of l: one, or one and
        -- then another, and the bounds of what's left after them.
        -- A sum is put in those terms only if it may share a variable with
        -- what's left.
        taken left = [ (k * b, Map.filter (/= 0) (Map.unionWith (+) left (Map.map (* negate k) g)))
                     | (vs, (g, b)) <- sums
                     , any (`Map.member` left) vs
                     , k <- take 1 [ q | (x, n) <- Map.toList g, Just m <- [Map.lookup x left], (q, 0) <- [m `quotRem` n], q > 0 ] ]
        fromSums = [ b1 + r | (b1, left1) <- taken vars, Just r <- [fromRanges left1] ]
            ++ [ b1 + b2 + r | (b1, left1) <- taken vars, (b2, left2) <- taken left1, Just r <- [fromRanges left2] ]
        candidates = maybe fromSums (: fromSums) (fromRanges vars)
    in if null candidates then Nothing else Just (maximum candidates + c)
  where
    -- The known sums in the same terms, made once for all that's asked.
    sums = [ (concatMap into (Map.keys g), (g', b - gc)) | (g, b) <- Map.toList (fIneqs facts), let Lin g' gc = norm (Lin g 0) ]
    fromRanges vs = sum <$> traverse bound (Map.toList vs)
    bound (v, k) =
        let Range lo hi = Map.findWithDefault unknownRange v (fInts facts)
        in (* k) <$> (if k > 0 then lo else hi)

upperLin :: Facts -> Lin -> Maybe Integer
upperLin facts l = negate <$> lowerLin facts (linScale (-1) l)

rangeOfLin :: Facts -> Lin -> Range
rangeOfLin facts l = Range (lowerLin facts l) (upperLin facts l)

lowerBound :: Facts -> Size -> Maybe Integer
lowerBound facts = \case
    Size l      -> lowerLin facts l
    NullPointer -> Nothing

-- | Takes elements off a size, for a pointer moved forward by an amount of
-- which only the bounds are known.
advance :: Range -> Size -> Maybe Size
advance r size = do
    k <- rHigh r
    lo <- rLow r
    if lo < 0 then Nothing else case size of
        Size l      -> Just (Size (l `linMinus` linConstant k))
        NullPointer -> Nothing

-- | The origin of an array variable's buffer: the array itself.
arrayOrigin :: Text -> Text
arrayOrigin v = v <> "#"

-- | Facts that hold on both sides. A pointer's size may be one of the
-- sums the hints give for it (a buffer field's length field).
joinFacts :: (Text -> [Lin]) -> Facts -> Facts -> Facts
joinFacts _ Unreached b = b
joinFacts _ a Unreached = a
joinFacts hints a b =
    let ints = Map.intersectionWith hull (fInts a) (fInts b)
        linear = Map.mapMaybe id (Map.intersectionWith same (fLinear a) (fLinear b))
        -- A sum known on one side (or a variable made from another) holds
        -- after the join if the other side knows at least something of it.
        made fs = Set.fromList (concat [ [Map.fromList [(v, 1), (w, -1)], Map.fromList [(v, -1), (w, 1)]] | (v, (w, _)) <- Map.toList (fLinear fs) ])
        -- A sum on one side of a variable another is made from there, or
        -- made from, is one of the other too, for one that comes in
        -- differently from each side: what a loop found is its index, and
        -- what that's known to be.
        renamed fs = Set.fromList
            [ Map.insert to n (Map.delete from g)
            | g <- Map.keys (fIneqs fs)
            , (v, (w, _)) <- Map.toList (fLinear fs)
            , (from, to) <- [(w, v), (v, w)]
            , Map.lookup to (fInts a) /= Map.lookup to (fInts b)
            , Just n <- [Map.lookup from g]
            , Map.notMember to g
            ]
        -- Where a variable isn't the number for none on one side, what's
        -- known of it there holds with its 'noneVar' z: v <= u is
        -- v <= u + (k + 1) * z, if the other side knows that much of it.
        lifted x y = Set.fromList
            [ Map.insert z (k + 1) g
            | (z, r) <- Map.toList (fInts x)
            , r == exactly 0
            , Just (v, k) <- [noneOf z]
            , Map.member z (fInts y)
            , g <- Map.singleton v (-1) : [ g' | g' <- Set.toList sums, Map.lookup v g' == Just (-1), Map.notMember z g' ]
            ]
        sums = Map.keysSet (fIneqs a) <> Map.keysSet (fIneqs b) <> made a <> made b <> renamed a <> renamed b
        ineqs = Map.fromList
            [ (g, min x y)
            | g <- Set.toList (sums <> lifted a b <> lifted b a)
            , Just x <- [Map.lookup g (fIneqs a) <|> lowA (Lin g 0)]
            , Just y <- [Map.lookup g (fIneqs b) <|> lowB (Lin g 0)]
            ]
        lowA = lowerLin a
        lowB = lowerLin b
        defs = Map.mapMaybe id (Map.intersectionWith same (fDefs a) (fDefs b))
        joined = Facts Map.empty ints linear ineqs defs
        pointers = Map.toList (Map.intersectionWith (,) (fPointers a) (fPointers b))
    in foldl' (joinPointer hints a b) joined pointers

-- | Facts that hold on both sides where a loop goes back to. Two variables
-- that come in differently from each side may still be as far apart on
-- both, or one so many times as far as the other has moved: what a loop's
-- count, or a cursor moved by a step each time, is to its index.
joinLoopFacts :: (Text -> [Lin]) -> [(Text, Text, Integer)] -> Facts -> Facts -> Facts
joinLoopFacts hints guesses a b = case joinFacts hints a b of
    joined@Facts{} | Facts{} <- a, Facts{} <- b ->
        let moved = [ v | (v, r) <- Map.toList (fInts a), maybe False (/= r) (Map.lookup v (fInts b)) ]
            point fs v = case Map.lookup v (fInts fs) of
                Just (Range (Just x) (Just y)) | x == y -> Just x
                _                                       -> Nothing
            -- u - k * w, from how far each moved between the sides: as far
            -- apart, or, for a pointer and what's left of its length,
            -- adding up to the same (one up as the other goes down).
            steps u w = (u, w, 1) : [ (u, w, -1) | any isOffsetVar [u, w] ] ++
                [ step
                | Just ua <- [point a u], Just ub <- [point b u], Just wa <- [point a w], Just wb <- [point b w]
                , (x, dx, y, dy) <- [(u, ub - ua, w, wb - wa), (w, wb - wa, u, ub - ua)]
                , dy /= 0
                , (k, 0) <- [dx `quotRem` dy]
                , abs k > 1
                , let step = (x, y, k)
                ]
            apart = Map.fromList
                [ (g, min p q)
                | (u : ws) <- List.tails moved
                , w <- ws
                , (x, y, k) <- steps u w
                , g <- [Map.fromList [(x, 1), (y, negate k)], Map.fromList [(x, -1), (y, k)]]
                , Map.notMember g (fIneqs joined)
                , Just p <- [lowerLin a (Lin g 0)]
                , Just q <- [lowerLin b (Lin g 0)]
                -- Adding up, only as much on both sides.
                , k /= -1 || p == q
                ]
            -- What the loop's steps say may stay so far apart: something
            -- moved by at least k each time round, and a counter moved by 1.
            stepped = Map.fromList
                [ (g, min p q)
                | (w, u, k) <- guesses
                , let g = Map.fromList [(w, 1), (u, negate k)]
                , Map.notMember g (fIneqs joined)
                , Just p <- [lowerLin a (Lin g 0)]
                , Just q <- [lowerLin b (Lin g 0)]
                ]
        in joined { fIneqs = Map.unions [fIneqs joined, apart, stepped] }
    joined -> joined

-- | A pointer after a join: the same as before if both sides agree where it
-- points; else at a new origin, with as much as both sides knew it had.
joinPointer :: (Text -> [Lin]) -> Facts -> Facts -> Facts -> (Text, (Pointer, Pointer)) -> Facts
joinPointer hints a b acc (p, (pa, pb))
    | pa == pb = case acc of
        Unreached -> Unreached
        Facts{}   -> acc { fPointers = Map.insert p pa (fPointers acc) }
    | otherwise =
        let size facts pt = case ptBase pt of
                Size l      -> Just (normalise facts (l `linMinus` linVar (offsetVar p)))
                NullPointer -> Nothing
            -- A sum of variables both sides have at least as many as: a
            -- hint, or one side's if the other has that many too (a cursor
            -- moved along with its length), else the least both have.
            -- Beside nullptr, what the other side has.
            base = case (size a pa, size b pb) of
                (Nothing, Just y)  -> fitting b y (hints p) <|> kept b y
                (Just x, Nothing)  -> fitting a x (hints p) <|> kept a x
                (Just x, Just y) -> case [ c | c <- hints p ++ lengths x y ++ [x, y], movable c, atMost a x c, atMost b y c ] of
                    c : _ -> Just (Size c)
                    []    -> elements <$> (min <$> lowerLin a x <*> lowerLin b y)
                (Nothing, Nothing) -> Just NullPointer
            fitting facts l cs = case [ c | c <- cs, movable c, atMost facts l c ] of
                c : _ -> Just (Size c)
                []    -> Nothing
            -- A variable that's as many as the elements on each side, where
            -- they're numbers: a length chosen with the pointer.
            lengths (Lin xs m) (Lin ys n)
                | Map.null xs, Map.null ys, m /= n =
                    [ linVar v | (v, r) <- Map.toList (fInts a), r == exactly m, Map.lookup v (fInts b) == Just (exactly n) ]
                | otherwise = []
            -- The pointer starts again from where it is.
            movable = not . linMentions (offsetVar p)
            kept facts l = if movable l then Just (Size l) else elements <$> lowerLin facts l
            atMost facts l c = maybe False (>= 0) (lowerLin facts (l `linMinus` c))
        in case base of
            Just sz -> setNewPointer p (p <> "#joined") sz (forgetInt (offsetVar p) acc)
            Nothing -> forgetVar p acc

-- | Drops what still changes: a bound that moved, a sum whose bound moved,
-- a pointer that moved to somewhere else.
widenFacts :: Facts -> Facts -> Facts
widenFacts = widenFactsKeeping Set.empty

-- | Facts where a loop starts again: a variable the loop doesn't change
-- (and its 'noneVar') is as it was before the loop.
keepingEntry :: Set.Set Text -> Facts -> Facts -> Facts
keepingEntry _ Unreached joined = joined
keepingEntry _ _ Unreached = Unreached
keepingEntry keep before@Facts{} joined@Facts{} = joined
    { fInts = Map.restrictKeys (fInts before) kept `Map.union` fInts joined
    , fIneqs = Map.unionWith max (Map.filterWithKey (\g _ -> Map.keysSet g `Set.isSubsetOf` kept) (fIneqs before)) (fIneqs joined)
    }
  where
    kept = keep <> Set.fromList [ z | z <- Map.keys (fInts before), Just (v, _) <- [noneOf z], Set.member v keep ]

-- | Widening that keeps the bounds of some variables as they are: those a
-- loop doesn't change.
widenFactsKeeping :: Set.Set Text -> Facts -> Facts -> Facts
widenFactsKeeping _ Unreached new = new
widenFactsKeeping _ _ Unreached = Unreached
widenFactsKeeping keep old@Facts{} new@Facts{} = new
    { fPointers = Map.mapMaybe id (Map.intersectionWith same (fPointers old) (fPointers new))
    , fInts = Map.restrictKeys (fInts new) keep `Map.union` Map.intersectionWith bound (fInts old) (fInts new)
    , fLinear = Map.mapMaybe id (Map.intersectionWith same (fLinear old) (fLinear new))
    , fIneqs = Map.mapMaybe id (Map.intersectionWith same (fIneqs old) (fIneqs new))
    , fDefs = Map.mapMaybe id (Map.intersectionWith same (fDefs old) (fDefs new))
    }
  where
    bound (Range olo ohi) (Range nlo nhi) =
        Range (if nlo == olo then nlo else Nothing) (if nhi == ohi then nhi else Nothing)

same :: Eq a => a -> a -> Maybe a
same x y = if x == y then Just x else Nothing

-- | Forgets an integer variable's value. If it's another variable plus a
-- constant (the one it's made from, or one made from it), what was known of
-- it is known of that one; else a sum it was in keeps what it said of the
-- others, with the variable's bounds put in.
forgetInt :: Text -> Facts -> Facts
forgetInt _ Unreached = Unreached
forgetInt v facts
    | not (mentioned v facts) = facts
    | otherwise = case Map.lookup v (fLinear facts) of
        Just (w, c) -> moveTo w c
        Nothing -> case [ (x, d) | (x, (r, d)) <- Map.toList (fLinear facts), r == v ] ++ equalities of
            (x, d) : _ -> moveTo x (negate d)
            []         -> eliminateInt v facts
  where
    -- x = v + d from x - v >= d and v - x >= -d.
    equalities =
        [ (x, d)
        | (g, d) <- Map.toList (fIneqs facts)
        , [(x, 1)] <- [Map.toList (Map.delete v g)]
        , Map.lookup v g == Just (-1)
        , x /= v
        , Map.lookup (Map.fromList [(v, 1), (x, -1)]) (fIneqs facts) == Just (negate d)
        ]
    -- v = w + c: everything said of v is said of w + c, and what was made
    -- from v is made from w.
    moveTo w c =
        let as = linVar w `linPlus` linConstant c
            put l = substitute (\x -> if x == v then as else linVar x) l
            Range lo hi = Map.findWithDefault unknownRange v (fInts facts)
            wRange = intersectRange (Range (subtract c <$> lo) (subtract c <$> hi)) (Map.findWithDefault unknownRange w (fInts facts))
            moved = facts
                { fPointers = Map.map (\pt -> case ptBase pt of
                                          Size l | linMentions v l -> pt { ptBase = Size (put l) }
                                          _                        -> pt) (fPointers facts)
                , fInts = Map.delete v (fInts facts)
                , fDefs = without v (fDefs facts)
                , fLinear = Map.mapMaybeWithKey (\y (r, e) -> if y == v || y == w then Nothing
                                                               else if r == v then Just (w, e + c) else Just (r, e)) (fLinear facts)
                , fIneqs = Map.unionWith max untouched $ Map.fromListWith max
                    [ (g', negate c')
                    | (g, b) <- Map.toList touched
                    , let Lin g' c' = put (Lin g (negate b))
                    , not (Map.null g')
                    ]
                }
        in setRange w wRange moved
    (touched, untouched) = Map.partitionWithKey (\g _ -> Map.member v g) (fIneqs facts)

-- | Whether anything is known of an integer variable.
mentioned :: Text -> Facts -> Bool
mentioned _ Unreached = False
mentioned v facts =
    Map.member v (fInts facts) || Map.member v (fLinear facts) || any ((== v) . fst) (Map.elems (fLinear facts))
    || any (Map.member v) (Map.keys (fIneqs facts))
    || Map.member v (fDefs facts) || any (linMentions v) (Map.elems (fDefs facts))
    || any (\pt -> case ptBase pt of Size l -> linMentions v l; NullPointer -> False) (Map.elems (fPointers facts))

-- | Forgets an integer variable, with its bounds put in the sums it's in.
eliminateInt :: Text -> Facts -> Facts
eliminateInt _ Unreached = Unreached
eliminateInt v facts = facts
    { fPointers = Map.mapMaybe base (fPointers facts)
    , fInts = Map.delete v (fInts facts)
    , fLinear = Map.filter ((/= v) . fst) (Map.delete v (fLinear facts))
    , fDefs = without v (fDefs facts)
    , fIneqs = Map.unionWith max untouched $ Map.fromListWith max $
        [ (g', b')
        | (g, b) <- Map.toList touched
        , Just (Lin g' b') <- [eliminate (Lin g (negate b))]
        , not (Map.null g')
        ] ++
        -- x <= v and v <= y make x <= y.
        [ (g', b1 + b2)
        | (g1, b1) <- Map.toList touched, Map.lookup v g1 == Just 1
        , (g2, b2) <- Map.toList touched, Map.lookup v g2 == Just (-1)
        , let g' = Map.filter (/= 0) (Map.unionWith (+) (Map.delete v g1) (Map.delete v g2))
        , not (Map.null g'), Map.size g' <= 3
        ]
    }
  where
    (touched, untouched) = Map.partitionWithKey (\g _ -> Map.member v g) (fIneqs facts)
    Range lo hi = Map.findWithDefault unknownRange v (fInts facts)
    -- g >= b as g - b >= 0; with v at its worst, what's left still is.
    eliminate l = case Map.lookup v (linVars l) of
        Nothing -> Just (Lin (linVars l) (negate (linConst l)))
        Just k  -> do
            worst <- if k > 0 then hi else lo
            let Lin g c = l { linVars = Map.delete v (linVars l) } `linPlus` linConstant (k * worst)
            return (Lin g (negate c))
    base pt = case ptBase pt of
        Size l | linMentions v l -> do
            k <- Map.lookup v (linVars l)
            worst <- if k > 0 then lo else hi
            return pt { ptBase = Size (l { linVars = Map.delete v (linVars l) } `linPlus` linConstant (k * worst)) }
        _ -> Just pt

-- | Forgets a variable: a pointer's place, or an integer's value.
forgetVar :: Text -> Facts -> Facts
forgetVar v facts = case forgetInt (offsetVar v) (forgetInt v facts) of
    Unreached -> Unreached
    facts'    -> facts' { fPointers = Map.delete v (fPointers facts') }

setRange :: Text -> Range -> Facts -> Facts
setRange _ _ Unreached = Unreached
setRange v r facts
    -- A variable that can be no number at all: there's no way here.
    | isEmptyRange r = Unreached
    | r == unknownRange = facts { fInts = Map.delete v (fInts facts) }
    | otherwise         = facts { fInts = Map.insert v r (fInts facts) }

-- | Records that an integer variable is another one plus a constant.
setLinear :: Text -> Maybe (Text, Integer) -> Facts -> Facts
setLinear _ _ Unreached = Unreached
setLinear v rel facts = case rel of
    -- Made from the variable at the root, so a bound reaches it in 1 step.
    Just (w, c) | w /= v -> case Map.lookup w (fLinear facts) of
        Just (u, d) | u /= v -> facts { fLinear = Map.insert v (u, c + d) (fLinear facts) }
        _                    -> facts { fLinear = Map.insert v (w, c) (fLinear facts) }
    _ -> facts

-- | Records that a sum is at least a bound: a bound on a variable if it's
-- just one.
addIneq :: Lin -> Facts -> Facts
addIneq _ Unreached = Unreached
addIneq l facts = case Map.toList vars of
    []        -> facts
    [(v, 1)]  -> raise v (Just bound) Nothing
    [(v, -1)] -> raise v Nothing (Just (negate bound))
    _         -> facts { fIneqs = Map.insertWith max vars bound (fIneqs facts) }
  where
    -- l >= 0, so vars >= -const. Kept as written: when a variable in it
    -- moves, it moves with it.
    Lin vars c = l
    bound = negate c
    raise v newLo newHi =
        let Range lo hi = Map.findWithDefault unknownRange v (fInts facts)
        in setRange v (intersectRange (Range lo hi) (Range newLo newHi)) facts

-- | An integer variable found to be a number: each sum it's in holds
-- without it too, with the number put in.
settle :: Text -> Integer -> Facts -> Facts
settle _ _ Unreached = Unreached
settle v n facts = foldl' (flip addIneq) (setRange v (exactly n) facts)
    [ Lin (Map.delete v g) (c * n - b) | (g, b) <- Map.toList (fIneqs facts), Just c <- [Map.lookup v g], Map.size g > 1 ]

-- | Two integer variables found to be so far apart (v = w + d): each sum
-- one is in holds of the other too.
equate :: Text -> Text -> Integer -> Facts -> Facts
equate _ _ _ Unreached = Unreached
equate v w d facts = foldl' (flip addIneq) facts
    [ Lin (Map.insert to n (Map.delete from g)) (n * shift - b)
    | (from, to, shift) <- [(v, w, d), (w, v, negate d)]
    , (g, b) <- Map.toList (fIneqs facts)
    , Just n <- [Map.lookup from g]
    , Map.notMember to g
    ]

-- | An integer variable set to a sum: what's known of it, and how it
-- relates to the sum's variables.
setIntLin :: Text -> Lin -> Facts -> Facts
setIntLin _ _ Unreached = Unreached
setIntLin v l facts@Facts{} =
    let defs = without v (fDefs facts)
        facts' = setRange v (rangeOfLin facts l) facts { fDefs = defs }
    in case Map.toList (linVars l) of
        [(w, 1)] -> setLinear v (Just (w, linConst l)) facts'
        []       -> facts'
        _ | linMentions v l -> addIneq (l `linMinus` linVar v) (addIneq (linVar v `linMinus` l) facts')
          | otherwise -> case addIneq (l `linMinus` linVar v) (addIneq (linVar v `linMinus` l) facts') of
                Unreached     -> Unreached
                added@Facts{} -> added { fDefs = Map.insert v l (fDefs added) }

-- | The sums known of variables, less those a variable that changes is, or
-- is in.
without :: Text -> Map Text Lin -> Map Text Lin
without v = Map.filterWithKey (\u l -> u /= v && not (linMentions v l))

-- | Moves an integer variable by a sum that doesn't mention it (v += e).
-- What was known of the old value is known of the new one less e.
moveInt :: Text -> Lin -> Facts -> Facts
moveInt _ _ Unreached = Unreached
moveInt v e facts = case Map.findWithDefault unknownRange v (fInts facts) of
    -- From one value, it's that value plus e.
    Range (Just lo) (Just hi) | lo == hi, not (Map.null (linVars e)) ->
        let l = linConstant lo `linPlus` e
        in case Map.toList (linVars e) of
            [(w, 1)] -> setLinear v (Just (w, linConst l)) moved
            _        -> addIneq (l `linMinus` linVar v) (addIneq (linVar v `linMinus` l) moved)
    _ -> moved
  where
    moved = facts
        { fPointers = Map.map (\pt -> pt { ptBase = substSize (ptBase pt) }) (fPointers facts)
        , fDefs = without v (fDefs facts)
        , fInts = Map.adjust (\r -> rangeArith C.BopPlus r (rangeOfLin facts e)) v (fInts facts)
        , fLinear = case linVars e of
            vars | Map.null vars -> Map.mapWithKey (shiftLinear (linConst e)) (fLinear facts)
            _ -> Map.filter ((/= v) . fst) (Map.delete v (fLinear facts))
        , fIneqs = Map.fromListWith max
            [ (g', b + k * linConst e)
            | (g, b) <- Map.toList (fIneqs facts)
            , let k = Map.findWithDefault 0 v g
            , let Lin g' _ = Lin g 0 `linMinus` linScale k (Lin (linVars e) 0)
            , not (Map.null g')
            ]
        }
    -- v_old = v - e
    subst l = case Map.lookup v (linVars l) of
        Just k  -> l `linMinus` linScale k e
        Nothing -> l
    substSize (Size l)    = Size (subst l)
    substSize NullPointer = NullPointer
    -- u = v + c before is u = v - k + c after; v = w + c before is
    -- v = w + c + k after.
    shiftLinear k u (w, c)
        | w == v    = (w, c - k)
        | u == v    = (w, c + k)
        | otherwise = (w, c)

-- | Points a pointer variable into a buffer, at an offset from the origin.
setPointer :: Text -> Text -> Lin -> Size -> Facts -> Facts
setPointer _ _ _ _ Unreached = Unreached
setPointer p o off base facts
    -- Moved within the buffer it was in (p = p + k).
    | Just (Pointer o' _) <- Map.lookup p (fPointers facts), o' == o, linMentions var off =
        let rest = off `linMinus` linVar var
        in if linMentions var rest then forgetVar p facts else moveInt var rest facts
    | otherwise = case setIntLin var off (forgetVar p facts) of
        Unreached -> Unreached
        facts'    -> facts' { fPointers = Map.insert p (Pointer o base) (fPointers facts') }
  where
    var = offsetVar p

-- | Points a pointer variable at the start of a buffer it got here. The
-- origin is named after the place in the code, so a pointer still holding
-- that name from before (round a loop) is somewhere else: its origin
-- becomes one no other is compared with.
setNewPointer :: Text -> Text -> Size -> Facts -> Facts
setNewPointer _ _ _ Unreached = Unreached
setNewPointer p o base facts =
    let retired = facts { fPointers = Map.map retire (fPointers facts) }
    in setPointer p o (linConstant 0) base retired
  where
    retire pt
        | ptOrigin pt == o = pt { ptOrigin = o <> "!" }
        | otherwise        = pt

-- | Whether pointers into a buffer from this origin can be compared.
comparableOrigin :: Text -> Bool
comparableOrigin = not . ("!" `T.isSuffixOf`)
