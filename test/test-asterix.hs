{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE GADTs #-}

import Data.Proxy
import qualified Data.ByteString as BS
import Data.ByteString.Internal (c2w)

import Test.Tasty
import Test.Tasty.QuickCheck as QC
import Test.Tasty.HUnit

import Asterix

parseUnparse ::
    ( Eq t
    , Show t
    , Parsing t
    , ONat (BitOffsetR t)
    , ONat (BitOffsetL t)
    ) => t -> BitString (BitOffsetL t) (BitOffsetR t) -> IO ()
parseUnparse t s = do
    unparse t @?= s
    parse False s @?= Right (t, bitStringEmpty)
    parse True s @?= Right (t, bitStringEmpty)

----------------------------------------
-- BitString

bitStringTests :: TestTree
bitStringTests = testGroup "BitString"
    [ testCase "Mask unit test" $ do
        mask (BitString $ BS.pack [0x01] :: BitString 0 0) @?= BS.replicate 1 0xff
        mask (BitString $ BS.pack [0x01, 0x02] :: BitString 0 0) @?= BS.replicate 2 0xff
        mask (BitString $ BS.pack [0x01, 0x02, 0x03] :: BitString 0 0) @?= BS.replicate 3 0xff

    , testCase "isZero" $ do
        let x :: BitString 0 0
            x = BitString $ BS.pack [0xff,0x3e,0x00,0x7f]
            Right (s1, x1) = bitStringSplitAt (Proxy @8) x
            Right (z1, x2) = bitStringSplitAt (Proxy @2) x1
            Right (s2, x3) = bitStringSplitAt (Proxy @5) x2
            Right (z2, x4) = bitStringSplitAt (Proxy @10) x3
            Right (s3, x5) = bitStringSplitAt (Proxy @7) x4

        bitStringIsZero x @?= False
        bitStringIsZero s1 @?= False
        bitStringIsZero z1 @?= True
        bitStringIsZero s2 @?= False
        bitStringIsZero z2 @?= True
        bitStringIsZero s3 @?= False
        bitStringIsEmpty x5 @?= True

    , QC.testProperty "Mask aligned property" $ \lst ->
        let bs :: BitString 0 0
            bs = BitString $ BS.pack lst
        in mask bs == BS.replicate (length lst) 0xff

    , QC.testProperty "Equality" $ \lst ->
        let bs1 :: BitString 0 0
            bs1 = BitString $ BS.pack lst
            bs2 = BitString $ BS.pack lst
        in bs1 == bs2

    , testCase "Create" $ do
        let ref :: BitString 0 0
            ref = BitString $ BS.pack [0x01, 0x02]

        assertBool "should be the same" (ref == ref)
        assertBool "should not be the same" (ref /= BitString (BS.pack [0x01, 0x03]))

        mapM_ ((@=?) ref)
            [ uIntegerToBitString (Proxy @0) (Proxy @16) 0x0102
            , (bitStringSingleton (0x01) :: BitString 0 0) <+> (bitStringSingleton (0x02) :: BitString 0 0)
            ]

    , QC.testProperty "fromInteger/toInteger 0 8" $ do
        i <- chooseInteger (0, 0xff)
        let bs = uIntegerToBitString (Proxy @0) (Proxy @8) i
        return (bitStringToUInteger bs === i)

    , QC.testProperty "fromInteger/toInteger 0 16" $ do
        i <- chooseInteger (0, 0xffff)
        let bs = uIntegerToBitString (Proxy @0) (Proxy @16) i
        return (bitStringToUInteger bs === i)

    , testCase "fromInteger/toInteger 4 8" $ do
        let i = 0xff
            bs = uIntegerToBitString (Proxy @4) (Proxy @8) i
        assertEqual "not equal" i (bitStringToUInteger bs)

    , QC.testProperty "fromInteger/toInteger 0 32" $ do
        i <- chooseInteger (0, 2^((32-0)::Int)-1)
        let bs = uIntegerToBitString (Proxy @0) (Proxy @32) i
        return (bitStringToUInteger bs === i)

    , QC.testProperty "fromInteger/toInteger 1 32" $ do
        i <- chooseInteger (0, 2^((32-1)::Int)-1)
        let bs = uIntegerToBitString (Proxy @1) (Proxy @32) i
        return (bitStringToUInteger bs === i)

    , QC.testProperty "fromInteger/toInteger 7 32" $ do
        i <- chooseInteger (0, 2^((32-7)::Int)-1)
        let bs = uIntegerToBitString (Proxy @7) (Proxy @32) i
        return (bitStringToUInteger bs === i)
    ]

----------------------------------------
-- Element

type SchemaElement = 'TElement 0 8 ('TContentInteger 'TUnsigned)

elementTests :: TestTree
elementTests = testGroup "Element"
    [ testCase "parsing" $ do
        parseUnparse
            (1 :: Variation SchemaElement)
            (uIntegerToBitString (Proxy @0) (Proxy @8) 1)
    ]

----------------------------------------
-- Group

type SchemaGroup = 'TGroup
   '[ 'TItem "S1" ('TElement 0 8 ('TContentInteger 'TUnsigned))
    , 'TSpare 0 2
    , 'TItem "S2" ('TElement 2 5 ('TContentInteger 'TUnsigned))
    , 'TSpare 7 10
    , 'TItem "S3" ('TElement 1 7 ('TContentInteger 'TUnsigned))
    ]

groupTests :: TestTree
groupTests = testGroup "Group"
    [ testCase "create" $ do
        mapM_ ((@=?) ref) vGroup
    , testCase "parsing" $ do
        parseUnparse ref (BitString $ BS.pack [0x01,0x04,0x00,0x03])
    ]
  where
    zero :: Variation SchemaGroup
    zero = Group
        (GCons (Item @"S1" 0)
            (GCons Spare
                (GCons (Item @"S2" 0)
                    (GCons Spare
                        (GCons (Item @"S3" 0) GNil)))))

    ref :: Variation SchemaGroup
    ref = Group
        (GCons (Item @"S1" 1)
            (GCons Spare
                (GCons (Item @"S2" 2)
                    (GCons Spare
                        (GCons (Item @"S3" 3) GNil)))))

    vGroup :: [Variation SchemaGroup]
    vGroup =
        [ ref
        , Group (GCons (Item @"S1" 1)
            (GCons Spare
                (GCons (Item @"S2" 2)
                    (GCons Spare
                        (GCons (Item @"S3" 3) GNil)))))
        , mkGroup
            ( Item @"S1" 1
           &: Spare
           &: Item @"S2" 2
           &: Spare
           &: Item @"S3" 3
           &: GNil)
        , mkGroup
            ( Item 1
           &: Spare
           &: Item 2
           &: Spare
           &: Item 3
           &: GNil)
        , mkGroup
            ( 1
           &: Spare
           &: 2
           &: Spare
           &: 3
           &: GNil)
        , 0x01040003
        , setGroupSubitem @"S1" 1
            $ setGroupSubitem @"S2" 2
            $ setGroupSubitem @"S3" 3
            $ zero
        , setGroupSubitem @"S1" (getGroupSubitem @"S1" ref) ref
        , setGroupSubitem @"S2" (getGroupSubitem @"S2" ref) ref
        , modifyGroupSubitem @"S1" (+ 1)
            $ modifyGroupSubitem @"S2" (+ 2)
            $ modifyGroupSubitem @"S3" (+ 3)
            $ zero
        ]

----------------------------------------
-- Extended

type SchemaExtended = 'TExtended
   '[ 'TItem "S1" ('TElement 0 8 ('TContentInteger 'TUnsigned))
    , 'TItem "S2" ('TElement 0 7 ('TContentInteger 'TUnsigned))
    ]
   '[
       '[ 'TItem "S3" ('TElement 0 6 ('TContentInteger 'TUnsigned))
        , 'TSpare 6 2
        , 'TItem "S4" ('TElement 0 7 ('TContentInteger 'TUnsigned))
        ]
    ,  '[ 'TItem "S5" ('TElement 0 8 ('TContentInteger 'TUnsigned))
        , 'TItem "S6" ('TElement 0 8 ('TContentInteger 'TUnsigned))
        , 'TItem "S7" ('TElement 0 7 ('TContentInteger 'TUnsigned))
        ]
    ]

extendedTests :: TestTree
extendedTests = testGroup "Extended"
    [ testCase "create" $ do
        let prim =
                ( Item @"S1" 1
               &: 2
               &: GNil)
            ext1 =
                ( 3
               &: spare
               &: 4
               &: GNil)
        ref @=? mkExtended prim (ext1 &:: ENil)

    , testCase "getSubitem" $ do
        getExtendedSubitem @"S1" ref @?= 1
        getExtendedSubitem @"S2" ref @?= 2
        getExtendedSubitem @"S3" ref @?= (Just 3)
        getExtendedSubitem @"S4" ref @?= (Just 4)
        getExtendedSubitem @"S5" ref @?= Nothing
        getExtendedSubitem @"S6" ref @?= Nothing
        getExtendedSubitem @"S7" ref @?= Nothing

    , testCase "modifySubitem" $ do
        let aux = mkExtended
                (0 &: 0 &: GNil)
                ((0 &: spare &: 0 &: GNil) &:: ENil)
        ref @=?
            ( modifyExtendedSubitemIfPresent @"S1" (+ 1)
            $ modifyExtendedSubitemIfPresent @"S2" (+ 2)
            $ modifyExtendedSubitemIfPresent @"S3" (+ 3)
            $ modifyExtendedSubitemIfPresent @"S4" (+ 4)
            $ modifyExtendedSubitemIfPresent @"S5" (+ 5)
            $ modifyExtendedSubitemIfPresent @"S6" (+ 6)
            $ modifyExtendedSubitemIfPresent @"S7" (+ 7)
            $ aux)

    , testCase "parsing" $ do
        parseUnparse ref (BitString $ BS.pack [0x01, 0x05, 0x0c, 0x08])
    ]
  where
    ref :: Variation SchemaExtended
    ref = Extended
        (1 &: 2 &: GNil)
        (ECons (3 &: spare &: 4 &: GNil) ENil)

----------------------------------------
-- Repetitive

type SchemaRepetitive = 'TRepetitive 8 ('TElement 0 8 ('TContentInteger 'TUnsigned))

repetitiveTests :: TestTree
repetitiveTests = testGroup "Repetitive"
    [ testCase "create" $ do
        ref @=? mkRepetitive [1, 2]
    , testCase "parsing" $ do
        parseUnparse ref (BitString $ BS.pack [2,1,2])
    ]
  where
    ref :: Variation SchemaRepetitive
    ref = Repetitive [1, 2]

----------------------------------------
-- Explicit

type SchemaExplicitRaw = 'TExplicit 'Nothing

type SchemaExplicitExpanded = 'TExplicit
    ('Just ('TElement 0 8 ('TContentInteger 'TUnsigned)))

explicitTests :: TestTree
explicitTests = testGroup "Explicit"
    [ testGroup "Raw"
        [ testCase "create" $ do
            refRaw @=? mkExplicitRaw "test"
        , testCase "parsing" $ do
            parseUnparse refRaw (BitString $ BS.pack ([5] <> fmap c2w "test"))
        ]
    , testGroup "Expanded"
        [ testCase "create" $ do
            refExpanded @=? mkExplicitExpanded 1
        , testCase "parsing" $ do
            parseUnparse refExpanded (BitString $ BS.pack [2,1])
        ]
    ]
  where
    refRaw :: Variation SchemaExplicitRaw
    refRaw = Explicit $ ExplicitRaw "test"

    refExpanded :: Variation SchemaExplicitExpanded
    refExpanded = Explicit $ ExplicitExpanded 1

----------------------------------------
-- Compound

type CItems =
   '[ 'Just ('TItem "I1" ('TElement 0 8 ('TContentInteger 'TUnsigned)))
    , 'Nothing
    , 'Nothing
    , 'Nothing
    , 'Nothing
    , 'Nothing
    , 'Nothing
    , 'Nothing
    , 'Just ('TItem "I2" ('TElement 0 8 ('TContentInteger 'TUnsigned)))
    ]

-- | Compound with FX
type SchemaCompoundFx = 'TCompound 'FSpecFx CItems

-- | Compound fixed (without FX)
type SchemaCompoundFixed = 'TCompound ('FSpecFixed 16) CItems

compoundTestsFx :: TestTree
compoundTestsFx = testGroup "Compound Fx"
    [ testCase "create" $ do
        mapM_ ((@=?) refFx) vCompound
    , testCase "parsing1" $ do
        parseUnparse refFx (BitString $ BS.pack [0x80,1])
    , testCase "parsing2" $ do
        let val :: Variation SchemaCompoundFx
            val =
                setCompoundSubitem @"I1" (Just 1)
              $ setCompoundSubitem @"I2" (Just 2)
              $ emptyCompound
        parseUnparse val
            (BitString $ BS.pack [0x81, 0x40, 1, 2])
    , testCase "parsing3" $ do
        let val :: Variation SchemaCompoundFx
            val = emptyCompound
        parseUnparse val bitStringEmpty
    ]
  where
    refFx :: Variation SchemaCompoundFx
    refFx = Compound (CConsItem (Just (Item @"I1" 1))
        (CConsNone (CConsNone (CConsNone (CConsNone (CConsNone (CConsNone (CConsNone
            (CConsItem Nothing CNil)))))))))

    vCompound :: [Variation SchemaCompoundFx]
    vCompound =
        [ refFx
        , setCompoundSubitem @"I1" (Just 1)
          $ emptyCompound
        , setCompoundSubitem @"I1" (Just 1)
          $ setCompoundSubitem @"I2" Nothing
          $ emptyCompound
        , mkCompound (Item @"I1" 1 &: GNil)
        , setCompoundSubitem @"I1" (getCompoundSubitem @"I1" refFx) refFx
        , setCompoundSubitem @"I2" (getCompoundSubitem @"I2" refFx) refFx
        , modifyCompoundSubitem @"I1" (+1)
          $ setCompoundSubitem @"I1" (Just 0)
          $ emptyCompound
        , modifyCompoundSubitem @"I2" (+1) refFx
        ]

compoundTestsFixed :: TestTree
compoundTestsFixed = testGroup "Compound Fixed"
    [ testCase "parsing" $ do
        let val :: Variation SchemaCompoundFixed
            val =
                setCompoundSubitem @"I1" (Just 1)
              $ setCompoundSubitem @"I2" (Just 2)
              $ emptyCompound
        parseUnparse val
            (BitString $ BS.pack [0x80, 0x80, 1, 2])
    ]

compoundTests :: TestTree
compoundTests = testGroup "Compound"
    [ compoundTestsFx
    , compoundTestsFixed
    ]

----------------------------------------
-- Record

type Val = 'TElement 0 8 ('TContentInteger 'TUnsigned)

type SchemaRecordSingle = ('TCompound 'FSpecFx '[ 'Just ('TItem "I1" Val)])

type SchemaRecordMultiple =
   '[ '("uap1", ('TCompound 'FSpecFx '[ 'Just ('TItem "I1" Val)]))
    , '("uap2", ('TCompound 'FSpecFx '[ 'Just ('TItem "I2" Val)]))
    ]

type SchemaRecord = 'TCompound 'FSpecFx

   '[ 'Just ('TItem "I1" Val)           -- Item1

    , 'Just ('TItem "I2" ('TGroup       -- Item2
       '[ 'TItem "S1" Val                 -- Subitem
        , 'TItem "S2" Val                 -- Subitem
        ]))

    , 'Just ('TItem "I3" ('TExtended    -- Item3
       '[ 'TItem "S1" ('TElement 0 8 ('TContentInteger 'TUnsigned))
        , 'TItem "S2" ('TElement 0 7 ('TContentInteger 'TUnsigned))
        ]
       '[
           '[ 'TItem "S3" ('TElement 0 8 ('TContentInteger 'TUnsigned))
            , 'TItem "S4" ('TElement 0 7 ('TContentInteger 'TUnsigned))
            ]
        ,  '[ 'TItem "S5" ('TElement 0 8 ('TContentInteger 'TUnsigned))
            , 'TItem "S6" ('TElement 0 8 ('TContentInteger 'TUnsigned))
            , 'TItem "S7" ('TElement 0 7 ('TContentInteger 'TUnsigned))
            ]
        ]))

    , 'Just ('TItem "I4" ('TRepetitive 8    -- Item4
        ('TGroup
           '[ 'TItem "S1" Val
            , 'TItem "S2" Val
            ])))

    , 'Just ('TItem "I5a" ('TExplicit 'Nothing))    -- Item 5a

    , 'Just ('TItem "I5b" ('TExplicit ('Just Val))) -- Item 5b

    , 'Nothing                              -- empty slot

    , 'Just ('TItem "I6" ('TCompound 'FSpecFx -- Item6
       '[ 'Just ('TItem "S1" Val)
        , 'Nothing
        , 'Just ('TItem "S2" Val)
       ]))
    ]

recordTests :: TestTree
recordTests = testGroup "Record"
    [ testGroup "Single"
        [ testCase "create" $ do
            let ref :: Record SchemaRecordSingle
                ref = Record emptyCompound
            mapM_ ((@=?) ref)
                [ emptyRecord
                ]

        ]
    , testGroup "Multiple"
        [ testCase "create" $ do
            let ref :: Record (Uap "uap2" SchemaRecordMultiple)
                ref = Record emptyCompound
            mapM_ ((@=?) ref)
                [ emptyRecord
                ]
        ]
    , testGroup "Real"
        [ testCase "parsing" $ do
            let item2 = mkGroup
                   ( Item @"S1" 1
                   &: Item @"S2" 2
                   &: GNil)

                item3 = mkExtended
                    ( Item @"S1" 1  -- prim
                   &: Item @"S2" 2
                   &: GNil)
                    (               -- ext1
                        ( 3
                       &: 4
                       &: GNil)
                  &:: ENil)

                item4 = mkRepetitive
                    [ repItem
                    , repItem
                    , repItem
                    ]
                  where
                    repItem = mkGroup
                        ( Item @"S1" 1
                       &: Item @"S2" 2
                       &: GNil)

                item5a = mkExplicitRaw "test"

                item5b = mkExplicitExpanded 1

                item6 = mkCompound
                    ( Item @"S1" 1
                   &: Item @"S2" 2
                   &: GNil)

                ref :: Record SchemaRecord
                ref = mkRecord
                    ( Item @"I1" 1
                   &: Item @"I2" item2
                   &: Item @"I3" item3
                   &: Item @"I4" item4
                   &: Item @"I5a" item5a
                   &: Item @"I5b" item5b
                   &: Item @"I6" item6
                   &: GNil)

                s :: BitString 0 0
                s = BitString $ BS.pack
                    [ 0xfd, 0x80  -- FSpec
                    , 1         -- I1
                    , 1, 2      -- I2
                    , 1, 5, 3, 8 -- I3
                    , 3, 1, 2, 1, 2, 1, 2  -- I4
                    , 5, 0x74, 0x65, 0x73, 0x74 -- I5a
                    , 2, 0x01                   -- I5b
                    , 0xa0, 1, 2 -- I6
                    ]

            parseUnparse ref s
        ]
        , QC.testProperty "Arbitrary records" $ \rec strict ->
            let s = unparse (rec :: Record SchemaRecord)
                Right (rec', _) = parse strict s
            in rec' == rec
    ]

main :: IO ()
main = defaultMain $ testGroup "Asterix Tests"
    [ bitStringTests
    , elementTests
    , groupTests
    , extendedTests
    , repetitiveTests
    , explicitTests
    , compoundTests
    , recordTests
    ]

