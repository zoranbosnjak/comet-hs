{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ConstraintKinds #-}

{-# OPTIONS -Wall #-}

module Asterix
where

import           GHC.TypeLits
import           Control.Monad
import           Data.Bits
import           Data.Word
import           Data.Bool
import           Data.Proxy
import           Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BS8
import qualified Data.ByteString.Base16 as B16
import           Test.QuickCheck (Arbitrary, arbitrary)
import qualified Test.QuickCheck as QC

----------------------------------------
-- Types

data TSig
    = TSigned
    | TUnsigned

data TScale = TScale Nat Nat

type Frac = Nat

type Unit = Symbol

data TString
    = TStringAscii  -- 8 bits per character
    | TStringICAO   -- 6 bits per character
    | TStringOctal  -- 3 bits per character

data TBds
    = TBdsWithAddress       -- 64 bits with embedded address
    | TBdsAt (Maybe Nat)    -- 56 bits (address is maybe a-priori known)

data TContent
    = TContentRaw
    | TContentTable
    | TContentString TString
    | TContentInteger TSig
    | TContentQuantity TSig TScale Frac Unit
    | TContentBds TBds

data TFspec
    = FSpecFx           -- Fspec with FX bit extensions
    | FSpecFixed Nat    -- Predefined fix-size fspec

type TBitOffset = Nat

type TBitLength = Nat

type EndOffset o n = Mod (o + n) 8

type ItemName = Symbol

type UapName = Symbol

type RepLength = Nat

class KnownSize t where
    type BitSizeOf t :: TBitLength

class HasOffset t where
    type BitOffsetL t :: TBitOffset
    type BitOffsetR t :: TBitOffset

type Alignment t a b = (BitOffsetL t ~ a, BitOffsetR t ~ b)

type Aligned t1 t2 = (BitOffsetR t1 ~ BitOffsetL t2)

type StrictParsing = Bool

newtype BitOffset = BitOffset Int deriving (Eq, Show)

type ONat a = (KnownNat a, 0 <= a, a <= 7)

data BitString (a :: TBitOffset) (b :: TBitOffset) where
    BitString :: (ONat a, ONat b) => ByteString -> BitString a b

class HasOffset t => Parsing t where
    unparse :: t -> BitString (BitOffsetL t) (BitOffsetR t)
    parse   :: StrictParsing -> BitString (BitOffsetL t) b -> Either String (t, BitString (BitOffsetR t) b)

data GList (a :: TBitOffset) (b :: TBitOffset) (ts :: [TItem]) where
    GNil  :: GList a a '[]
    GCons :: Item t -> GList (BitOffsetR (Item t)) b ts -> GList (BitOffsetL (Item t)) b (t ': ts)

data EList (tss :: [[TItem]]) where
    ENil  :: EList tss
    ECons :: GList 0 7 ts -> EList tss -> EList (ts ': tss)

data CList (ts :: [Maybe TItem]) where
    CNil      :: CList '[]
    CConsNone :: CList ts -> CList ('Nothing ': ts)
    CConsItem ::
        ( Alignment (Item t) 0 0
        ) => Maybe (Item t) -> CList ts -> CList (('Just t) ': ts)

data ExplicitCont (t :: (Maybe TVariation)) where
    ExplicitRaw :: ByteString -> ExplicitCont 'Nothing
    ExplicitExpanded :: Variation t -> ExplicitCont ('Just t)

data TVariation
    = TElement TBitOffset TBitLength TContent
    | TGroup [TItem]
    | TExtended [TItem] [[TItem]]
    | TRepetitive RepLength TVariation
    | TExplicit (Maybe TVariation)
    | TCompound TFspec [Maybe TItem]

data TItem
    = TSpare TBitOffset TBitLength
    | TItem ItemName TVariation

data Variation (t :: TVariation) where
    Element     :: BitString a (EndOffset a n) -> Variation ('TElement a n t)
    Group       :: GList 0 0 ts -> Variation ('TGroup ts)
    Extended    :: GList 0 7 ts -> EList tss -> Variation ('TExtended ts tss)
    Repetitive  :: [Variation t] -> Variation ('TRepetitive n t)
    Explicit    :: ExplicitCont t -> Variation ('TExplicit t)
    Compound    :: CList ts -> Variation ('TCompound mn ts)

data Item (t :: TItem) where
    Spare :: Item ('TSpare o n)
    Item  :: forall name t. Variation t -> Item ('TItem name t)

newtype Record t = Record (Variation t)

----------------------------------------
-- BitString support

instance Semigroup (BitString 0 0) where
    BitString val1 <> BitString val2 = BitString (val1 <> val2)

instance Monoid (BitString 0 0) where
    mempty = BitString mempty

hexlify :: ByteString -> String
hexlify = BS8.unpack . B16.encode

packZipWith :: (Word8 -> Word8 -> Word8) -> ByteString -> ByteString -> ByteString
packZipWith f a b = BS.pack $ BS.zipWith f a b

mkBitOffset :: Int -> BitOffset
mkBitOffset = BitOffset . flip mod 8

instance Semigroup BitOffset where
    (BitOffset val1) <> (BitOffset val2) = BitOffset (mod (val1+val2) 8)

instance Monoid BitOffset where
    mempty = BitOffset 0

maskOf :: BitOffset -> Word8
maskOf (BitOffset i) = shiftR 0xff i

mask :: forall a b. BitString a b -> ByteString
mask (BitString s)
    | x == 0 = BS.empty
    | x == 1 = BS.singleton (m1 .&. m2)
    | otherwise =
        BS.singleton m1
     <> BS.replicate (x-2) 0xFF
     <> BS.singleton m2
  where
    x = BS.length s
    a = fromIntegral $ natVal (Proxy @a)
    b = fromIntegral $ natVal (Proxy @b)
    m1 = maskOf (BitOffset a)
    m2
        | b == 0 = 0xff
        | otherwise = complement $ maskOf (BitOffset b)

masked :: BitString a b -> ByteString
masked bs@(BitString s) = packZipWith (.&.) s (mask bs)

bitStringEmpty :: ONat a => BitString a a
bitStringEmpty = BitString BS.empty

bitStringIsEmpty :: BitString a b -> Bool
bitStringIsEmpty (BitString s) = s == BS.empty

bitStringSingleton :: ONat a => Word8 -> BitString a a
bitStringSingleton = BitString . BS.singleton

bitStringLength :: forall a b. BitString a b -> Int
bitStringLength (BitString s) = (BS.length s) * 8 - a - (mod (8-b) 8)
  where
    a = fromIntegral $ natVal (Proxy @a)
    b = fromIntegral $ natVal (Proxy @b)

bitStringIsZero :: BitString a b -> Bool
bitStringIsZero = BS.all (== 0) . masked

bitStringSplitAt :: forall n a b.
    ( KnownNat n
    , ONat (EndOffset a n)
    ) => Proxy n -> BitString a b
    -> Either String (BitString a (EndOffset a n), BitString (EndOffset a n) b)
bitStringSplitAt Proxy bs@(BitString s) = do
    when (ln < n) $ do
        Left $ "bitString length error, required: " <> show n <> ", actual: " <> show ln <> ", data: " <> show s
    let (s1, s2) = case divMod splitPoint 8 of
            (x, 0) -> (BS.take x s, BS.drop x s)
            (x, _) -> (BS.take (succ x) s, BS.drop x s)
    return (BitString s1, BitString s2)
  where
    ln = bitStringLength bs
    a = fromIntegral $ natVal (Proxy @a)
    n = fromIntegral $ natVal (Proxy @n)
    splitPoint = a + n

bitStringTake ::
    ( KnownNat n
    , ONat (EndOffset a n)
    ) => Proxy n -> BitString a b -> Either String (BitString a (EndOffset a n))
bitStringTake n s = fmap fst (bitStringSplitAt n s)

bitStringDrop ::
    ( KnownNat n
    , ONat (EndOffset a n)
    ) => Proxy n -> BitString a b -> Either String (BitString (EndOffset a n) b)
bitStringDrop n s = fmap snd (bitStringSplitAt n s)

bitStringToUInteger :: forall a b. KnownNat b => BitString a b -> Integer
bitStringToUInteger
    = flip div (2^leftShift)
    . BS.foldl (\acc x -> acc*256 + fromIntegral x) 0
    . masked
  where
    b = natVal (Proxy @b)
    leftShift = mod (8 - b) 8

uIntegerToBitString :: forall n a b.
    ( KnownNat n
    , ONat a
    , ONat b
    , EndOffset a n ~ b
    ) => Proxy a -> Proxy n -> Integer -> BitString a b
uIntegerToBitString Proxy Proxy
    = BitString
    . BS.reverse
    . fst
    . BS.unfoldrN requiredBytes f
    . (*) (2 ^ leftShift)
  where
    n = fromIntegral $ natVal (Proxy @n)
    a = fromIntegral $ natVal (Proxy @a)
    b = mod (a+n) 8
    leftShift = mod (8 - b) 8
    totalBits = a + n
    requiredBytes
        | y == 0 = x
        | otherwise = succ x
      where
        (x, y) = divMod totalBits 8
    f val = Just (fromIntegral y, x)
      where
        (x,y) = divMod val 256

(<+>) :: forall a b c. BitString a b -> BitString b c -> BitString a c
(<+>) (BitString val1) (BitString val2)
    | BS.null val1 = BitString val2
    | BS.null val2 = BitString val1
    | otherwise =
        let b = fromIntegral $ natVal (Proxy @b)
            s1 = BS.init val1
            s3 = BS.tail val2
            w1 = BS.last val1
            w2 = BS.head val2
            m = maskOf (mkBitOffset b)
            w =  (w1 .&. (complement m))
             .|. (w2 .&. m)
        in case b of
            0 -> BitString (val1 <> val2)
            _ -> BitString (s1 <> BS.singleton w <> s3)

instance Eq (BitString a b) where
    v1 == v2 = masked v1 == masked v2

instance Show (BitString a b) where
    show v = "0x" <> hexlify (masked v) where

----------------------------------------
-- Element support

instance Eq (Variation ('TElement o n t)) where
    Element val1 == Element val2 = val1 == val2

instance Show (Variation ('TElement o n t)) where
    show (Element val) = "Element (" <> show val <> ")"

instance (ONat o, ONat (EndOffset o n), KnownNat n) => Num (Variation ('TElement o n t)) where
    (Element val1) + (Element val2) = fromInteger (bitStringToUInteger val1 + bitStringToUInteger val2)
    (Element val1) - (Element val2) = fromInteger (bitStringToUInteger val1 - bitStringToUInteger val2)
    (Element val1) * (Element val2) = fromInteger (bitStringToUInteger val1 * bitStringToUInteger val2)
    abs (Element val) = fromInteger $ abs $ bitStringToUInteger val
    signum (Element val) = fromInteger $ signum $ bitStringToUInteger val
    fromInteger = Element . uIntegerToBitString (Proxy @o) (Proxy @n)

instance KnownSize (Variation ('TElement o n t)) where
    type BitSizeOf (Variation ('TElement o n t)) = n

instance HasOffset (Variation ('TElement o n t)) where
    type BitOffsetL (Variation ('TElement o n t)) = o
    type BitOffsetR (Variation ('TElement o n t)) = EndOffset o n

instance
    ( ONat o
    , ONat (EndOffset o n)
    , KnownNat n
    ) => Parsing (Variation ('TElement o n t))
  where
    unparse (Element bs) = bs
    parse _strict s = do
        (a, b) <- bitStringSplitAt (Proxy @n) s
        return (Element a, b)

instance
    ( ONat a
    , KnownNat n
    , ONat (EndOffset a n)
    ) => Arbitrary (Variation ('TElement a n t))
  where
    arbitrary = do
        QC.Positive i <- arbitrary
        return $ Element $ uIntegerToBitString (Proxy @a) (Proxy @n) i

----------------------------------------
-- Group support

infixr 5 &:
(&:) :: Item t
    -> GList (BitOffsetR (Item t)) b ts
    -> GList (BitOffsetL (Item t)) b (t : ts)
(&:) = GCons

instance Eq (GList a b '[]) where
    GNil == GNil = True

instance (Eq (Item t), Eq (GList (BitOffsetR (Item t)) b ts)) => Eq (GList c b (t ': ts)) where
    GCons a as == GCons b bs = a == b && as == bs

instance Show (GList a b '[]) where
    show GNil = "GNil"

instance (Show (Item t), Show (GList (BitOffsetR (Item t)) b ts)) => Show (GList c b (t ': ts)) where
    show (GCons x xs) = "GCons (" <> show x <> ") (" <> show xs <> ")"

instance KnownSize (GList a b '[]) where
    type BitSizeOf (GList a b '[]) = 0

instance KnownSize (GList c b (t ': ts)) where
    type BitSizeOf (GList c b (t ': ts)) = BitSizeOf (Item t) + BitSizeOf (GList c b ts)

instance HasOffset (GList a b ts) where
    type BitOffsetL (GList a b ts) = a
    type BitOffsetR (GList a b ts) = b

instance Num (GList a a '[]) where
    (+) = const
    (-) = const
    (*) = const
    abs = id
    signum = id
    fromInteger _ = GNil

instance
    ( KnownNat (BitSizeOf (GList a b ts))
    , Num (Item t)
    , Num (GList a b ts)
    , BitOffsetL (Item t) ~ c
    , BitOffsetR (Item t) ~ a
    ) => Num (GList c b (t ': ts))
  where
    GCons a as + GCons b bs = GCons (a+b) (as+bs)
    GCons a as - GCons b bs = GCons (a-b) (as-bs)
    GCons a as * GCons b bs = GCons (a*b) (as*bs)
    abs (GCons x xs) = GCons (abs x) (abs xs)
    signum (GCons x xs) = GCons (signum x) (signum xs)
    fromInteger val = case fromInteger @(GList a b ts) b of
        result -> GCons (fromInteger a) result
      where
        n = natVal (Proxy @(BitSizeOf (GList a b ts)))
        (a,b) = divMod val (2^n)

instance ONat a => Parsing (GList a a '[]) where
    unparse GNil = bitStringEmpty
    parse _strict s = return (GNil, s)

instance
    ( Parsing (Item t)
    , BitOffsetL (Item t) ~ c
    , BitOffsetR (Item t) ~ a
    , ONat a
    , ONat b
    , ONat c
    , Parsing (GList a b ts)
    , BitOffsetL (GList a b ts) ~ a
    , BitOffsetR (GList a b ts) ~ b
    ) => Parsing (GList c b (t ': ts)) where
    unparse (GCons item glist) = case unparse glist of
        BitString result -> unparse item <+> BitString result
    parse strict s = do
        (a, s') <- parse strict s
        (b, s'') <- parse strict s'
        return (GCons a b, s'')

instance Eq (GList 0 0 ts) => Eq (Variation ('TGroup ts)) where
    Group val1 == Group val2 = val1 == val2

instance Show (GList 0 0 ts) => Show (Variation ('TGroup ts)) where
    show (Group lst) = "Group (" <> show lst <> ")"

instance HasOffset (Variation ('TGroup ts)) where
    type BitOffsetL (Variation ('TGroup ts)) = BitOffsetL (GList 0 0 ts)
    type BitOffsetR (Variation ('TGroup ts)) = BitOffsetR (GList 0 0 ts)

instance Num (GList 0 0 ts) => Num (Variation ('TGroup ts)) where
    Group val1 + Group val2 = Group (val1+val2)
    Group val1 - Group val2 = Group (val1-val2)
    Group val1 * Group val2 = Group (val1*val2)
    abs (Group val) = Group (abs val)
    signum (Group val) = Group (signum val)
    fromInteger = Group . fromInteger

instance Parsing (GList 0 0 ts) => Parsing (Variation ('TGroup ts)) where
    unparse (Group glist) = unparse glist
    parse strict s = do
        (glist, s') <- parse strict s
        return (Group glist, s')

mkGroup :: GList 0 0 ts -> Variation ('TGroup ts)
mkGroup = Group

type family GListMatchName iName ts where
    GListMatchName iName (('TItem iName t) ': ts) = 'True
    GListMatchName iName (t2 ': ts) = 'False
    GListMatchName iName '[] = TypeError ('Text "Group subitem not defined")

type family GListT iName ts where
    GListT iName (('TItem iName t) ': ts) = t
    GListT iName (t2 ': ts) = GListT iName ts
    GListT iName '[] = TypeError ('Text "Group subitem not defined")

class IsGList' iName flag ts where
    setGListItem' :: Proxy flag -> Variation (GListT iName ts) -> GList a b ts -> GList a b ts
    getGListItem' :: Proxy flag -> GList a b ts -> Variation (GListT iName ts)

class IsGList iName ts where
    setGListItem :: Variation (GListT iName ts) -> GList a b ts -> GList a b ts
    getGListItem :: GList a b ts -> Variation (GListT iName ts)

instance
    ( IsGList iName ts
    , GListT iName (t2 : ts) ~ GListT iName ts
    ) => IsGList' iName 'False (t2 ': ts)
  where
    setGListItem' Proxy val (GCons x xs) = GCons x (setGListItem @iName val xs)
    getGListItem' Proxy (GCons _x xs) = getGListItem @iName xs

instance IsGList' iName 'True (('TItem iName t) ': ts) where
    setGListItem' Proxy y (GCons _x xs) = GCons (Item y) xs
    getGListItem' Proxy (GCons (Item x) _xs) = x

instance
    ( GListMatchName iName ts ~ flag
    , IsGList' iName flag ts
    ) => IsGList iName ts
  where
    setGListItem val glist = setGListItem' @iName (Proxy @flag) val glist
    getGListItem glist = getGListItem' @iName (Proxy @flag) glist

setGroupSubitem :: forall iName ts. IsGList iName ts =>
    Variation (GListT iName ts) -> Variation ('TGroup ts) -> Variation ('TGroup ts)
setGroupSubitem val (Group glist) = Group (setGListItem @iName val glist)

getGroupSubitem :: forall iName ts. IsGList iName ts =>
    Variation ('TGroup ts) -> Variation (GListT iName ts)
getGroupSubitem (Group glist) = getGListItem @iName glist

modifyGroupSubitem :: forall iName ts. IsGList iName ts
    => (Variation (GListT iName ts) -> Variation (GListT iName ts))
    -> Variation ('TGroup ts)
    -> Variation ('TGroup ts)
modifyGroupSubitem f grp = setGroupSubitem @iName (f (getGroupSubitem @iName grp)) grp

instance Arbitrary (GList a a '[]) where
    arbitrary = pure GNil

instance
    ( BitOffsetL (Item t) ~ a
    , Arbitrary (Item t)
    , Arbitrary (GList (BitOffsetR (Item t)) b ts)
    ) => Arbitrary (GList a b (t ': ts))
  where
    arbitrary = GCons <$> arbitrary <*> arbitrary

instance (Arbitrary (GList 0 0 ts)) => Arbitrary (Variation ('TGroup ts)) where
    arbitrary = Group <$> arbitrary

----------------------------------------
-- Extended support

infixr 5 &::
(&::) :: GList 0 7 ts -> EList tss -> EList (ts : tss)
(&::) = ECons

instance Eq (EList '[]) where
    ENil == ENil = True

instance (Eq (GList 0 7 ts), Eq (EList tss)) => Eq (EList (ts ': tss)) where
    ENil == ENil = True
    ECons _ _ == ENil = False
    ENil == ECons _ _ = False
    ECons a as == ECons b bs = a == b && as == bs

instance (Eq (GList 0 7 ts), Eq (EList tss)) => Eq (Variation ('TExtended ts tss)) where
    Extended p1 ext1 == Extended p2 ext2 = p1 == p2 && ext1 == ext2

instance Show (EList '[]) where
    show ENil = "ENil"

instance (Show (GList 0 7 ts), Show (EList tss)) => Show (EList (ts ': tss)) where
    show ENil = "ENil"
    show (ECons a as) = "ECons (" <> show a <> ") " <> show as

instance (Show (GList 0 7 ts), Show (EList tss)) => Show (Variation ('TExtended ts tss)) where
    show (Extended p ext) = "Extended (" <> show p <> ") (" <> show ext <> ")"

instance HasOffset (Variation ('TExtended ts tss)) where
    type BitOffsetL (Variation ('TExtended ts tss)) = 0
    type BitOffsetR (Variation ('TExtended ts tss)) = 0

instance HasOffset (EList tss) where
    type BitOffsetL (EList tss) = 7
    type BitOffsetR (EList tss) = 0

instance Parsing (EList '[]) where
    unparse ENil = uIntegerToBitString (Proxy @7) (Proxy @1) 0
    parse _strict s = do
        (a, b) <- bitStringSplitAt (Proxy @1) s
        unless (bitStringIsZero a) $ Left $ "expecting zero bitString: " <> show s
        return (ENil, b)

instance
    ( Parsing (GList 0 7 ts)
    , Parsing (EList tss)
    ) => Parsing (EList (ts ': tss)) where
    unparse ENil = uIntegerToBitString (Proxy @7) (Proxy @1) 0
    unparse (ECons a as)
        = uIntegerToBitString (Proxy @7) (Proxy @1) 1
      <+> unparse a
      <+> unparse as
    parse strict s = do
        (a, b1) <- bitStringSplitAt (Proxy @1) s
        case bitStringIsZero a of
            True -> return (ENil, b1)
            False -> do
                (glist, b2) <- parse strict b1
                (elist, b3) <- parse strict b2
                return (ECons glist elist, b3)

instance
    ( Parsing (GList 0 7 ts)
    , Parsing (EList tss)
    ) => Parsing (Variation ('TExtended ts tss)) where
    unparse (Extended glist elist) = unparse glist <+> unparse elist
    parse strict s = do
        (glist, b1) <- parse strict s
        (elist, b2) <- parse strict b1
        return (Extended glist elist, b2)

mkExtended :: GList 0 7 ts -> EList tss -> Variation ('TExtended ts tss)
mkExtended = Extended

type family ExtendedLookup iName ts tss where
    ExtendedLookup iName ('TItem iName t ': ts) tss = t
    ExtendedLookup iName (t2 ': ts) tss = ExtendedLookup iName ts tss
    ExtendedLookup iName '[] (ts ': tss) = ExtendedLookup iName ts tss
    ExtendedLookup iName '[] '[] = TypeError ('Text "Extended subitem not defined")

type family ExtendedT iName ext ts tss where
    ExtendedT iName 'False ('TItem iName t ': ts) tss = Variation t
    ExtendedT iName 'True  ('TItem iName t ': ts) tss = Maybe (Variation t)
    ExtendedT iName ext (t2 ': ts) tss = ExtendedT iName ext ts tss
    ExtendedT iName ext '[] (ts ': tss) = ExtendedT iName 'True ts tss
    ExtendedT iName ext '[] '[] = TypeError ('Text "Extended subitem not defined")

class IsExtended' iName ext match ts tss where
    getExtendedSubitem' :: Proxy ext -> Proxy match -> GList a b ts -> EList tss -> ExtendedT iName ext ts tss
    modifyExtendedSubitemIfPresent' :: Proxy ext -> Proxy match
        -> (Variation (ExtendedLookup iName ts tss) -> Variation (ExtendedLookup iName ts tss))
        -> GList a b ts -> EList tss -> (GList a b ts, EList tss)

instance IsExtended' iName 'False 'True (('TItem iName t) ': ts) tss
  where
    getExtendedSubitem' Proxy Proxy (GCons (Item x) _glist) _elist = x
    modifyExtendedSubitemIfPresent' Proxy Proxy f (GCons (Item x) glist) elist =
        (GCons (Item (f x)) glist, elist)

instance IsExtended' iName 'True 'True (('TItem iName t) ': ts) tss
  where
    getExtendedSubitem' Proxy Proxy (GCons (Item x) _glist) _elist = Just x
    modifyExtendedSubitemIfPresent' Proxy Proxy f (GCons (Item x) glist) elist =
        (GCons (Item (f x)) glist, elist)

instance
    ( ExtendedT iName ext ts tss ~ ExtendedT iName ext (t2 : ts) tss
    , ExtendedLookup iName (t2 : ts) tss ~ ExtendedLookup iName ts tss
    , IsExtended' iName ext (GListMatchName iName ts) ts tss
    ) => IsExtended' iName ext 'False (t2 ': ts) tss
  where
    getExtendedSubitem' Proxy Proxy (GCons _x glist) elist =
        getExtendedSubitem' @iName (Proxy @ext) (Proxy @(GListMatchName iName ts)) glist elist
    modifyExtendedSubitemIfPresent' Proxy Proxy f (GCons x glist) elist =
        let (glist', elist') = modifyExtendedSubitemIfPresent' @iName (Proxy @ext) (Proxy @(GListMatchName iName ts)) f glist elist
        in (GCons x glist', elist')

instance
    ( ExtendedT iName 'True ts tss ~ Maybe a
    , IsExtended' iName 'True (GListMatchName iName ts) ts tss
    ) => IsExtended' iName ext match '[] (ts ': tss)
  where
    getExtendedSubitem' Proxy Proxy GNil ENil = Nothing
    getExtendedSubitem' Proxy Proxy GNil (ECons glist elist) =
        getExtendedSubitem' @iName (Proxy @'True) (Proxy @(GListMatchName iName ts)) glist elist
    modifyExtendedSubitemIfPresent' Proxy Proxy _f GNil ENil = (GNil, ENil)
    modifyExtendedSubitemIfPresent' Proxy Proxy f GNil (ECons glist elist) =
        let (glist', elist') = modifyExtendedSubitemIfPresent' @iName (Proxy @'True) (Proxy @(GListMatchName iName ts)) f glist elist
        in (GNil, ECons glist' elist')

getExtendedSubitem :: forall iName ts tss.
    ( IsExtended' iName 'False (GListMatchName iName ts) ts tss
    ) => Variation ('TExtended ts tss) -> ExtendedT iName 'False ts tss
getExtendedSubitem (Extended glist elist) =
    getExtendedSubitem' @iName (Proxy @'False) (Proxy @(GListMatchName iName ts)) glist elist

modifyExtendedSubitemIfPresent :: forall (iName :: ItemName) ts tss.
    ( IsExtended' iName 'False (GListMatchName iName ts) ts tss
    ) => (Variation (ExtendedLookup iName ts tss) -> Variation (ExtendedLookup iName ts tss))
    -> Variation ('TExtended ts tss)
    -> Variation ('TExtended ts tss)
modifyExtendedSubitemIfPresent f (Extended glist elist) =
    let (glist', elist') = modifyExtendedSubitemIfPresent' @iName (Proxy @'False) (Proxy @(GListMatchName iName ts)) f glist elist
    in Extended glist' elist'

instance Arbitrary (EList '[]) where
    arbitrary = pure ENil

instance
    ( Arbitrary (GList 0 7 ts)
    , Arbitrary (EList tss)
    ) => Arbitrary (EList (ts ': tss))
  where
    arbitrary = arbitrary >>= \case
        False -> pure ENil
        True -> ECons <$> arbitrary <*> arbitrary

instance
    ( Arbitrary (GList 0 7 ts)
    , Arbitrary (EList tss)
    ) => Arbitrary (Variation ('TExtended ts tss))
  where
    arbitrary = Extended <$> arbitrary <*> arbitrary

----------------------------------------
-- Repetitive support

instance Eq (Variation t) => Eq (Variation ('TRepetitive n t)) where
    Repetitive lst1 == Repetitive lst2 = lst1 == lst2

instance Show (Variation t) => Show (Variation ('TRepetitive n t)) where
    show (Repetitive lst) = "Repetitive (" <> show lst <> ")"

instance HasOffset (Variation ('TRepetitive n t)) where
    type BitOffsetL (Variation ('TRepetitive n t)) = 0
    type BitOffsetR (Variation ('TRepetitive n t)) = 0

instance forall n t.
    ( Parsing (Variation t)
    , BitOffsetR (Variation t) ~ 0
    , BitOffsetL (Variation t) ~ 0
    , KnownNat n
    , Mod n 8 ~ 0
    ) => Parsing (Variation ('TRepetitive n t))
  where
    unparse (Repetitive lst) = n <+> go lst
      where
        n :: BitString 0 0
        n = uIntegerToBitString (Proxy @0) (Proxy @n) (fromIntegral $ length lst)
        go [] = bitStringEmpty
        go (x:xs) = unparse x <+> go xs
    parse strict s = do
        (a, b) <- bitStringSplitAt (Proxy @n) s
        let n = bitStringToUInteger a
            go cnt acc s1
                | cnt <= 0 = return (acc, s1)
                | otherwise = do
                    (el, s2) <- parse strict s1
                    go (pred cnt) (acc <> [el]) s2
        (lst, s') <- go n [] b
        return (Repetitive lst, s')

mkRepetitive :: [Variation t] -> Variation ('TRepetitive n t)
mkRepetitive = Repetitive

instance (KnownNat n, Arbitrary (Variation t)) => Arbitrary (Variation ('TRepetitive n t)) where
    arbitrary = do
        n <- QC.chooseInt (0, pred nMax)
        lst <- arbitrary
        return $ Repetitive $ take n lst
      where
        rep :: Int
        rep = fromIntegral $ natVal (Proxy @n)

        nMax :: Int
        nMax = 2 ^ rep

----------------------------------------
-- Explicit support

instance Eq (ExplicitCont 'Nothing) where
    ExplicitRaw val1 == ExplicitRaw val2 = val1 == val2

instance Eq (Variation vt) => Eq (ExplicitCont ('Just vt)) where
    ExplicitExpanded val1 == ExplicitExpanded val2 = val1 == val2

instance Eq (ExplicitCont t) => Eq (Variation ('TExplicit t)) where
    Explicit val1 == Explicit val2 = val1 == val2

instance Show (ExplicitCont 'Nothing) where
    show (ExplicitRaw val) = show val

instance Show (Variation t) => Show (ExplicitCont ('Just t)) where
    show (ExplicitExpanded val) = "Expanded (" <> show val <> ")"

instance Show (ExplicitCont mt) => Show (Variation ('TExplicit mt)) where
    show (Explicit val) = "Explicit (" <> show val <> ")"

instance HasOffset (Variation ('TExplicit mt)) where
    type BitOffsetL (Variation ('TExplicit mt)) = 0
    type BitOffsetR (Variation ('TExplicit mt)) = 0

instance Parsing (Variation ('TExplicit 'Nothing)) where
    unparse (Explicit (ExplicitRaw val))
        = bitStringSingleton (succ $ fromIntegral $ BS.length val)
      <+> BitString val
    parse _strict s = do
        (a, (BitString bs)) <- bitStringSplitAt (Proxy @8) s
        let x = pred $ fromIntegral $ bitStringToUInteger a
        unless (x >= 0) $ Left $ "Expecting positive value, got: " <> show x
        unless (BS.length bs >= x) $ do
            Left $ "ByteString length error, expecting >= " <> show x <> ", got: " <> show (BS.length bs)
        return (Explicit $ ExplicitRaw $ BS.take x bs, BitString $ BS.drop x bs)

instance
    ( Parsing (Variation t)
    , BitOffsetR (Variation t) ~ 0
    , BitOffsetL (Variation t) ~ 0
    ) => Parsing (Variation ('TExplicit ('Just t))) where
    unparse (Explicit (ExplicitExpanded val)) =
        let (BitString s) = unparse val
        in   bitStringSingleton (succ $ fromIntegral $ BS.length s)
         <+> (BitString s)
    parse strict s = do
        (a, (BitString bs)) <- bitStringSplitAt (Proxy @8) s
        let x = pred $ fromIntegral $ bitStringToUInteger a
        unless (x >= 0) $ Left $ "Expecting positive value, got: " <> show x
        unless (BS.length bs >= x) $ do
            Left $ "ByteString length error, expecting >= " <> show x <> ", got: " <> show (BS.length bs)
        (var, b) <- parse strict (BitString $ BS.take x bs)
        unless (bitStringIsEmpty (b :: BitString 0 0)) $ do
            Left $ "Expecting empty bitstring, got: " <> show b
        return (Explicit $ ExplicitExpanded var, BitString $ BS.drop x bs)

mkExplicitRaw :: ByteString -> Variation ('TExplicit 'Nothing)
mkExplicitRaw = Explicit . ExplicitRaw

mkExplicitExpanded :: Variation vt -> Variation ('TExplicit ('Just vt))
mkExplicitExpanded = Explicit . ExplicitExpanded

instance Arbitrary (Variation ('TExplicit 'Nothing)) where
    arbitrary = do
        n <- QC.chooseInt (1, 254)
        bs <- BS.pack . take n <$> arbitrary
        return $ Explicit $ ExplicitRaw bs

instance Arbitrary (Variation t) => Arbitrary (Variation ('TExplicit ('Just t))) where
    arbitrary = Explicit . ExplicitExpanded <$> arbitrary

----------------------------------------
-- Compound support

instance Eq (CList '[]) where
    CNil == CNil = True

instance Eq (CList ts) => Eq (CList ('Nothing ': ts)) where
    CConsNone val1 == CConsNone val2 = val1 == val2

instance (Eq (Item t), Eq (CList ts)) => Eq (CList ('Just t ': ts)) where
    CConsItem a as == CConsItem b bs = a == b && as == bs

instance Show (CList '[]) where
    show CNil = "CNil"

instance Show (CList ts) => Show (CList ('Nothing ': ts)) where
    show (CConsNone xs) = "CConsNone (" <> show xs <> ")"

instance (Show (Item t), Show (CList ts)) => Show (CList ('Just t ': ts)) where
    show (CConsItem mx xs) = "CConsItem (" <> x <> ") (" <> show xs <> ")"
      where
        x = case mx of
            Nothing -> "Nothing"
            Just val -> "Just (" <> show val <> ")"

instance Eq (CList ts) => Eq (Variation ('TCompound mn ts)) where
    Compound val1 == Compound val2 = val1 == val2

instance Show (CList ts) => Show (Variation ('TCompound mn ts)) where
    show (Compound clist) = "Compound (" <> show clist <> ")"

instance HasOffset (CList ts) where
    type BitOffsetL (CList ts) = 0
    type BitOffsetR (CList ts) = 0

class HasFSpec ts where
    unparseCList :: CList ts -> ([Bool], BitString 0 0)
    parseCList :: [Bool] -> StrictParsing -> BitString 0 b -> Either String (CList ts, BitString 0 b)

instance HasFSpec '[] where
    unparseCList CNil = ([], mempty)
    parseCList _ _ s = return (CNil, s)

instance HasFSpec ts => HasFSpec ('Nothing ': ts) where
    unparseCList (CConsNone rest) = ([False], mempty) <> unparseCList rest
    parseCList fspec strict s = do
        let (a,b) = case fspec of
                [] -> (False, [])
                _ -> (head fspec, tail fspec)
        unless (a == False) $ Left $ "Unparse CList failed, fspec: " <> show fspec <> ", bs: " <> show s
        (result, s1) <- parseCList b strict s
        return (CConsNone result, s1)

instance
    ( Parsing (Item t)
    , Alignment (Item t) 0 0
    , HasFSpec ts
    ) => HasFSpec (('Just t) ': ts)
  where
    unparseCList (CConsItem mi rest) = case mi of
        Nothing -> ([False], mempty) <> unparseCList rest
        Just i -> ([True], unparse i) <> unparseCList rest
    parseCList fspec strict s = do
        let (a,b) = case fspec of
                [] -> (False, [])
                _ -> (head fspec, tail fspec)
        case a of
            False -> do
                (result, s1) <- parseCList b strict s
                return (CConsItem Nothing result, s1)
            True -> do
                (i, s1) <- parse strict s
                (result, s2) <- parseCList b strict s1
                return (CConsItem (Just i) result, s2)

instance HasOffset (Variation ('TCompound mfs ts)) where
    type BitOffsetL (Variation ('TCompound mfs ts)) = 0
    type BitOffsetR (Variation ('TCompound mfs ts)) = 0

chunksOf :: Int -> [a] -> [[a]]
chunksOf i ls = map (take i) (build (splitter ls)) where
    build g = g (:) []
    splitter [] _ n = n
    splitter l c n  = l `c` splitter (drop i l) c n

boolsToWord8 :: [Bool] -> Word8
boolsToWord8
    = sum
    . zipWith (*) bits
    . fmap (bool 0 1)
    . \x -> x <> repeat False
  where
    bits = fmap (\x -> (2 ^ x)) [7,6..1::Int]

word8ToBools :: Word8 -> [Bool]
word8ToBools val = fmap (\n -> val .&. (2^n) /= 0) [7,6..0::Int]

instance HasFSpec ts => Parsing (Variation ('TCompound 'FSpecFx ts)) where
    unparse (Compound clist) = fspec <+> bs
      where
        fspec :: BitString 0 0
        fspec
            = BitString
            $ BS.pack
            $ \case
                [] -> []
                lst -> fmap (+1) (init lst) <> [last lst]
            $ reverse
            $ dropWhile (== 0)
            $ reverse
            $ fmap boolsToWord8
            $ chunksOf 7
            $ fspec'
        (fspec', bs) = unparseCList clist
    parse strict s = do
        (fspec, s1) <- getFSpec [] s
        (result, s2) <- parseCList fspec strict s1
        return (Compound result, s2)
      where
        getFSpec :: forall b. [Bool] -> BitString 0 b -> Either String ([Bool], BitString 0 b)
        getFSpec acc (BitString x) = case x of
            "" -> return ([], BitString x)
            _ -> do
                let a = word8ToBools $ BS.head x
                    b :: BitString 0 b
                    b = BitString $ BS.drop 1 x
                    acc2 = acc <> init a
                case last a of
                    False -> return (acc2, b)
                    True -> getFSpec acc2 b

instance (Mod n 8 ~ 0, KnownNat n, HasFSpec ts) => Parsing (Variation ('TCompound ('FSpecFixed n) ts)) where
    unparse (Compound clist) = fspec <+> bs
      where
        n = fromIntegral $ natVal (Proxy @n)
        fspec :: BitString 0 0
        fspec
            = BitString
            $ BS.pack
            $ fmap boolsToWord8
            $ chunksOf 8
            $ take n
            $ fspec' <> repeat False
        (fspec', bs) = unparseCList clist
    parse strict s = do
        (fspec, s1) <- getFSpec s
        (result, s2) <- parseCList fspec strict s1
        return (Compound result, s2)
      where
        numBytes :: Int
        numBytes = div (fromIntegral $ natVal (Proxy @n)) 8

        getFSpec :: forall b. BitString 0 b -> Either String ([Bool], BitString 0 b)
        getFSpec (BitString x) = do
            unless (BS.length x >= numBytes) $ do
                Left $ "ByteString too short: " <> show x
            let (a, b) = (BS.take numBytes x, BS.drop numBytes x)
                fspec = fmap word8ToBools (BS.unpack a)
            return (mconcat fspec, BitString b)

class EmptyCompound ts where
    emptyCompound :: Variation ('TCompound mn ts)

instance EmptyCompound '[] where
    emptyCompound = Compound CNil

instance EmptyCompound ts => EmptyCompound ('Nothing ': ts) where
    emptyCompound = Compound (CConsNone rest) where
        Compound rest = emptyCompound

instance
    ( BitOffsetL (Item t) ~ 0
    , BitOffsetR (Item t) ~ 0
    , EmptyCompound ts
    ) => EmptyCompound ('Just t ': ts) where
    emptyCompound = Compound (CConsItem Nothing rest) where
        Compound rest = emptyCompound

type family CListMatchName iName ts where
    CListMatchName iName ('Just ('TItem iName t) ': ts) = 'True
    CListMatchName iName (t2 ': ts) = 'False
    CListMatchName iName '[] = TypeError ('Text "Compound subitem not defined")

type family CListT iName ts where
    CListT iName ('Just ('TItem iName t) ': ts) = t
    CListT iName (t2 ': ts) = CListT iName ts
    CListT iName '[] = TypeError ('Text "Compound subitem not defined")

class IsCList' iName match ts where
    setCListSubitem' :: Proxy match -> Maybe (Variation (CListT iName ts)) -> CList ts -> CList ts
    getCListSubitem' :: Proxy match -> CList ts -> Maybe (Variation (CListT iName ts))

instance IsCList' iName 'True ('Just ('TItem iName t) ': ts) where
    setCListSubitem' Proxy val (CConsItem _mx x) = CConsItem (fmap Item val) x
    getCListSubitem' Proxy (CConsItem mItem _xs) = case mItem of
        Nothing -> Nothing
        Just (Item val) -> Just val

instance
    ( IsCList' iName (CListMatchName iName ts) ts
    ) => IsCList' iName match ('Nothing ': ts)
  where
    setCListSubitem' Proxy val (CConsNone xs) =
        CConsNone (setCListSubitem' @iName (Proxy @(CListMatchName iName ts)) val xs)
    getCListSubitem' Proxy (CConsNone xs) =
        getCListSubitem' @iName (Proxy @(CListMatchName iName ts)) xs

instance
    ( CListT iName ('Just t2 : ts) ~ CListT iName ts
    , IsCList' iName (CListMatchName iName ts) ts
    ) => IsCList' iName 'False ('Just t2 ': ts) where
    setCListSubitem' Proxy val (CConsItem mx xs) =
        CConsItem mx (setCListSubitem' @iName (Proxy @(CListMatchName iName ts)) val xs)
    getCListSubitem' Proxy (CConsItem _mx xs) =
        getCListSubitem' @iName (Proxy @(CListMatchName iName ts)) xs

class IsCompound iName ts where
    setCompoundSubitem :: Maybe (Variation (CListT iName ts)) -> Variation ('TCompound mn ts) -> Variation ('TCompound mn ts)
    getCompoundSubitem :: Variation ('TCompound mn ts) -> Maybe (Variation (CListT iName ts))

instance
    ( IsCList' iName (CListMatchName iName ts) ts
    ) => IsCompound iName ts
  where
    setCompoundSubitem val (Compound clist) =
        Compound (setCListSubitem' @iName (Proxy @(CListMatchName iName ts)) val clist)
    getCompoundSubitem (Compound clist) =
        getCListSubitem' @iName (Proxy @(CListMatchName iName ts)) clist

modifyCompoundSubitem ::
    forall iName mn ts. (IsCompound iName ts)
    => (Variation (CListT iName ts) -> Variation (CListT iName ts))
    -> Variation ('TCompound mn ts)
    -> Variation ('TCompound mn ts)
modifyCompoundSubitem f val = case getCompoundSubitem @iName val of
    Nothing -> val
    Just x -> setCompoundSubitem @iName (Just $ f x) val

class MkCompound as ts where
    mkCompound :: GList 0 0 as -> Variation ('TCompound mn ts)

instance EmptyCompound ts => MkCompound '[] ts where
    mkCompound GNil = emptyCompound

instance
    ( IsCompound name ts, MkCompound as ts
    , CListT name ts ~ t
    , BitOffsetR (Variation t) ~ 0
    ) => MkCompound (('TItem name t) ': as) ts
  where
    mkCompound (GCons (Item v) is) = setCompoundSubitem @name (Just v) (mkCompound is)

instance Arbitrary (CList '[]) where
    arbitrary = return CNil

instance Arbitrary (CList ts) => Arbitrary (CList ('Nothing ': ts)) where
    arbitrary = do
        xs <- arbitrary
        return (CConsNone xs)

instance
    ( Arbitrary (CList ts)
    , Arbitrary (Item t)
    , Alignment (Item t) 0 0
    ) => Arbitrary (CList (('Just t) ': ts))
  where
    arbitrary = do
        mx <- arbitrary
        xs <- arbitrary
        return (CConsItem mx xs)

instance Arbitrary (CList ts) => Arbitrary (Variation ('TCompound mn ts)) where
    arbitrary = Compound <$> arbitrary

----------------------------------------
-- Item support

spare :: Item ('TSpare o n)
spare = Spare

instance Eq (Item ('TSpare o n)) where
    Spare == Spare = True

instance Eq (Variation t) => Eq (Item ('TItem name t)) where
    Item var1 == Item var2 = var1 == var2

instance Show (Item ('TSpare o n)) where
    show Spare = "Spare"

instance (KnownSymbol name, Show (Variation t)) => Show (Item ('TItem name t)) where
    show (Item var) = "Item @\"" <> symbolVal (Proxy @name) <> "\" (" <> show var <> ")"

instance Num (Item ('TSpare o n)) where
    Spare + Spare = Spare
    Spare - Spare = Spare
    Spare * Spare = Spare
    abs Spare = Spare
    signum Spare = Spare
    fromInteger _ = Spare

instance Num (Variation t) => Num (Item ('TItem name t)) where
    Item a + Item b = Item (a+b)
    Item a - Item b = Item (a-b)
    Item a * Item b = Item (a*b)
    abs (Item a) = Item (abs a)
    signum (Item a) = Item (signum a)
    fromInteger = Item . fromInteger

instance KnownSize (Item ('TSpare o n)) where
    type BitSizeOf (Item ('TSpare o n)) = n

instance KnownSize (Item ('TItem name t)) where
    type BitSizeOf (Item ('TItem name t)) = BitSizeOf (Variation t)

instance HasOffset (Item ('TSpare o n)) where
    type BitOffsetL (Item ('TSpare o n)) = o
    type BitOffsetR (Item ('TSpare o n)) = EndOffset o n

instance HasOffset (Item ('TItem name t)) where
    type BitOffsetL (Item ('TItem name t)) = BitOffsetL (Variation t)
    type BitOffsetR (Item ('TItem name t)) = BitOffsetR (Variation t)

instance
    ( KnownNat n
    , ONat o
    , ONat (EndOffset o n)
    ) => Parsing (Item ('TSpare o n))
  where
    unparse Spare = uIntegerToBitString (Proxy @o) (Proxy @n) 0
    parse strict s = do
        (a, b) <- bitStringSplitAt (Proxy @n) s
        when strict $ do
             unless (bitStringIsZero a) $ do
                Left $ "Expecting zero bitstring, got: " <> show a
        return (Spare, b)

instance Parsing (Variation t) => Parsing (Item ('TItem name t)) where
    unparse (Item var) = unparse var
    parse strict s = do
        (x, s') <- parse strict s
        return (Item x, s')

instance Arbitrary (Item ('TSpare o n)) where
    arbitrary = pure Spare

instance Arbitrary (Variation t) => Arbitrary (Item ('TItem name t)) where
    arbitrary = Item <$> arbitrary

----------------------------------------
-- Record support

-- | Select Uap by name
type family Uap (name :: UapName) (lst :: [(UapName, TVariation)]) :: TVariation where
    Uap name '[] = TypeError ('Text "Uap not defined")
    Uap name ('(name,uap) ': rest) = uap
    Uap name ('(other,uap) ': rest) = Uap name rest

instance Eq (Variation t) => Eq (Record t) where
    Record val1 == Record val2 = val1 == val2

instance Show (Variation t) => Show (Record t) where
    show (Record variation) = "Record (" <> show variation <> ")"

instance HasOffset (Record t) where
    type BitOffsetL (Record t) = BitOffsetL (Variation t)
    type BitOffsetR (Record t) = BitOffsetR (Variation t)

instance Parsing (Variation t) => Parsing (Record t) where
    unparse (Record val) = unparse val
    parse strict s = do
        (x, s') <- parse strict s
        return (Record x, s')

instance Arbitrary (Variation t) => Arbitrary (Record t) where
    arbitrary = Record <$> arbitrary

emptyRecord :: EmptyCompound ts => Record ('TCompound mn ts)
emptyRecord = Record $ emptyCompound

mkRecord :: MkCompound as ts => GList 0 0 as -> Record ('TCompound mn ts)
mkRecord = Record . mkCompound

