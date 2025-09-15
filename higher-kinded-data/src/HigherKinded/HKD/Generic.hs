{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Based on 'HKD' from 'Data.Generic.HKD.Types from package 'higgledy'
--   by Tom Harding ((c) Tom Harding, 2019, MIT)

module HigherKinded.HKD.Generic
  ( module HigherKinded.HKD.Generic
  , OnFields
  , OnField
  , type (%~)
  ) where

import Data.Function (on)
import Data.Functor.Const
import Data.Functor.Contravariant (Contravariant (..), phantom)
import Data.Functor.Product (Product (..))
import Data.Kind
import Data.Proxy
import GHC.Generics hiding (from, to)
import GHC.Generics qualified as G
import GHC.TypeLits
import Generic.Data.Microsurgery

#ifdef VERSION_aeson
import Data.Aeson (FromJSON, ToJSON, FromJSONKey, ToJSONKey, GFromJSON, GToJSON', Value, Zero)
#endif

#ifdef VERSION_QuickCheck
import Test.QuickCheck.Arbitrary (Arbitrary (..), CoArbitrary (..))
import Test.QuickCheck.Function (Function (..), functionMap)
#endif

import HigherKinded.HKT
import HigherKinded.HKT.Base

import HigherKinded.HKD.Class



type HKD :: Type -> ((Type -> Type) -> Type -> Type) -> (Type -> Type) -> Type
newtype HKD structure hkt f = GHKD { unGHKD :: GHKD_ (Rep structure) hkt f () }


type HKD_ :: Type -> ((Type -> Type) -> Type -> Type) -> (Type -> Type) -> (Type -> Type)
type HKD_ structure hkt f = GHKD_ (Rep structure) hkt f

type GHKD_ :: (Type -> Type) -> ((Type -> Type) -> Type -> Type) -> (Type -> Type) -> (Type -> Type)
type family GHKD_ structureRep hkt f = (res :: Type -> Type) where
  GHKD_ (M1 index meta inner) hkt f = M1 index meta (GHKD_ inner hkt f)
  GHKD_ (left :*: right) hkt f = GHKD_ left hkt f :*: GHKD_ right hkt f
  GHKD_ (left :+: right) hkt f = GHKD_ left hkt f :+: GHKD_ right hkt f
  GHKD_ (K1 index (SubHKD subHKD)) hkt f = K1 index (HKD subHKD hkt f)
  GHKD_ (K1 index (t (SubHKD subHKD))) hkt f = K1 index (HKD (HKD subHKD Applied t) hkt f)
  GHKD_ (K1 index (Applied k t)) hkt f = K1 index (GHKD_ (Rep (k $~ t)) hkt f ())
  GHKD_ (K1 index value) hkt f = K1 index (UnHKT (hkt f value))

--------------------------------------------------------------------------------

newtype SubHKD t = SubHKD { unSubHKD :: t }
  deriving newtype (Eq, Ord, Show, Generic)

type WithMods :: Type -> [Type] -> Type
type WithMods t mods = Surgeries mods t

type (.~) :: Symbol -> Type -> Type
type (.~) field t = field %~ Applied (Const t)

#ifdef VERSION_aeson
deriving newtype instance ToJSON t => ToJSON (SubHKD t)
deriving newtype instance FromJSON t => FromJSON (SubHKD t)

deriving newtype instance ToJSONKey t => ToJSONKey (SubHKD t)
deriving newtype instance FromJSONKey t => FromJSONKey (SubHKD t)
#endif

#ifdef VERSION_QuickCheck
deriving newtype instance Arbitrary t => Arbitrary (SubHKD t)
deriving newtype instance CoArbitrary t => CoArbitrary (SubHKD t)
#endif

--------------------------------------------------------------------------------

type NewtypeHKD :: ((Type -> Type) -> Type) -> (Type -> Type) -> Type
type family NewtypeHKD hkd f
type instance NewtypeHKD (HKD structure hkt) f = GUnNewtypeHKD_ (Rep (HKD structure hkt f))

type family GUnNewtypeHKD_ rep where
  GUnNewtypeHKD_ (D1 d (C1 c (S1 s' (Rec0 x)))) = x

--------------------------------------------------------------------------------

instance GenericHKD_ structure hkt f => Generic (HKD structure hkt f) where
  type Rep (HKD structure hkt f) = HKD_ structure hkt f
  from = phantom . unGHKD
  to   = GHKD . phantom

class (Contravariant (HKD_ structure hkt f), Functor (HKD_ structure hkt f)) => GenericHKD_ structure hkt f
instance (Contravariant (HKD_ structure hkt f), Functor (HKD_ structure hkt f)) => GenericHKD_ structure hkt f

--------------------------------------------------------------------------------

instance (Eq tuple, Generic xs, Tuple xs hkt f tuple)
    => Eq (HKD xs hkt f) where
  (==) = (==) `on` toTuple

instance (Ord tuple, Generic xs, Tuple xs hkt f tuple)
    => Ord (HKD xs hkt f) where
  compare = compare `on` toTuple

instance (Semigroup tuple, Generic xs, Tuple xs hkt f tuple)
    => Semigroup (HKD xs hkt f) where
  x <> y = fromTuple (toTuple x <> toTuple y)

instance (Monoid tuple, Generic xs, Tuple xs hkt f tuple)
    => Monoid (HKD xs hkt f) where
  mempty = fromTuple mempty

--------------------------------------------------------------------------------

#ifdef VERSION_aeson
instance
  ( GenericHKD_ structure hkt f
  , GToJSON' Value Zero (GHKD_ (Rep structure) hkt f)
  ) => ToJSON (HKD structure hkt f)

instance
  ( GenericHKD_ structure hkt f
  , GFromJSON Zero (GHKD_ (Rep structure) hkt f)
  ) => FromJSON (HKD structure hkt f)
#endif

--------------------------------------------------------------------------------

#ifdef VERSION_QuickCheck
instance (Arbitrary tuple, GToTuple (HKD_ structure hkt f) tuple)
    => Arbitrary (HKD structure hkt f) where
  arbitrary = fmap (GHKD . gfromTuple) arbitrary

instance (CoArbitrary tuple, GToTuple (HKD_ structure hkt f) tuple)
    => CoArbitrary (HKD structure hkt f) where
  coarbitrary (GHKD x) = coarbitrary (gtoTuple x)

instance (Function tuple, Tuple structure hkt f tuple)
    => Function (HKD structure hkt f) where
  function = functionMap toTuple fromTuple
#endif

--------------------------------------------------------------------------------

class GShow (named :: Bool) (rep :: Type -> Type) where
  gshow :: rep p -> String

instance GShow named inner => GShow named (D1 meta inner) where
  gshow = gshow @named . unM1

instance (GShow 'True inner, KnownSymbol name)
    => GShow any (C1 ('MetaCons name fixity 'True) inner) where
  gshow (M1 x) = symbolVal (Proxy @name) <> " {" <> gshow @'True x <> "}"

instance (GShow 'False inner, KnownSymbol name)
    => GShow any (C1 ('MetaCons name fixity 'False) inner) where
  gshow (M1 x) = symbolVal (Proxy @name) <> " " <> gshow @'False x

instance (GShow 'True left, GShow 'True right)
    => GShow 'True (left :*: right) where
  gshow (left :*: right) = gshow @'True left <> ", " <> gshow @'True right

instance (GShow 'False left, GShow 'False right)
    => GShow 'False (left :*: right) where
  gshow (left :*: right) = gshow @'False left <> " " <> gshow @'False right

instance (GShow 'True inner, KnownSymbol field)
    => GShow 'True (S1 ('MetaSel ('Just field) i d c) inner) where
  gshow (M1 inner) = symbolVal (Proxy @field) <> " = " <> gshow @'True inner

instance GShow 'False inner => GShow 'False (S1 meta inner) where
  gshow (M1 inner) = gshow @'False inner

instance (Show inner) => GShow named (K1 R inner) where
  gshow (K1 x) = show x

instance (Generic structure, GShow 'True (HKD_ structure hkt f))
    => Show (HKD structure hkt f) where
  show (GHKD x) = gshow @'True x

--------------------------------------------------------------------------------

-- | Often, we can get instances by using an 'HKD' type's isomorphism with a
-- certain size of tuple. This class witnesses the isomorphism with a certain
-- tuple (specifically a nested tree of pairs) to allow us to derive "via"
-- these shapes.
class Tuple (structure :: Type) (hkt :: ((Type -> Type) -> Type -> Type)) (f :: Type -> Type) (tuple :: Type)
    | structure hkt f -> tuple where
  toTuple   :: HKD structure hkt f -> tuple
  fromTuple :: tuple -> HKD structure hkt f

class GToTuple (rep :: Type -> Type) (tuple :: Type)
    | rep -> tuple where
  gfromTuple :: tuple -> rep p
  gtoTuple   :: rep p -> tuple

instance GToTuple inner tuple
    => GToTuple (M1 index meta inner) tuple where
  gfromTuple = M1 . gfromTuple
  gtoTuple   = gtoTuple . unM1

instance (GToTuple left left', GToTuple right right')
    => GToTuple (left :*: right) (left', right') where
  gfromTuple (x, y) = gfromTuple x :*: gfromTuple y
  gtoTuple (x :*: y) = (gtoTuple x, gtoTuple y)

instance GToTuple (K1 index inner) inner where
  gfromTuple = K1
  gtoTuple = unK1

instance (GToTuple (HKD_ structure hkt f) tuple)
    => Tuple structure hkt f tuple where
  toTuple = gtoTuple . unGHKD
  fromTuple = GHKD . gfromTuple

--------------------------------------------------------------------------------

instance
    ( FunctorB (HKD structure hkt)
    , forall f g. TraversableHKD (HKD structure hkt) hkt f g
    )
  =>
    TraversableB (HKD structure hkt)
  where
    btraverse
      :: forall f g t.
         ( Applicative t
         )
      => (forall x. f x -> t (g x))
      -> HKD structure hkt f
      -> t (HKD structure hkt g)
    btraverse = traverseHKD @(HKD structure hkt) @hkt @f @g

--------------------------------------------------------------------------------

instance
    ( forall f g. FunctorHKD (HKD structure hkt) hkt f g
    )
  =>
    FunctorB (HKD structure hkt)
  where
    bmap
      :: forall f g.
         (forall x. f x -> g x)
      -> HKD structure hkt f
      -> HKD structure hkt g
    bmap = mapHKD @(HKD structure hkt) @hkt @f @g

--------------------------------------------------------------------------------

instance
    ( forall f g h. ZippableHKD (HKD structure hkt) hkt f g h
    , forall f g. FunctorHKD (HKD structure hkt) hkt f g
    )
  =>
    ApplicativeB (HKD structure hkt)
  where
    bpure
      :: forall f.
         (forall a. f a)
      -> (HKD structure hkt) f
    bpure zero = pureHKD @(HKD structure hkt) @hkt @f zero

    bprod
      :: forall f g.
         (HKD structure hkt) f
      -> (HKD structure hkt) g
      -> (HKD structure hkt) (f `Product` g)
    bprod x y = zipHKD @(HKD structure hkt) @hkt @f @g @(f `Product` g) Pair x y

--------------------------------------------------------------------------------

instance
    ( FunctorB (HKD structure hkt)
    , forall f g h. BiTraversableHKD (HKD structure hkt) hkt f g h
    )
  =>
    ConstraintsB (HKD structure hkt)
  where
    type AllB c (HKD structure hkt) = HKDFieldsHave c (HKD structure hkt)

    baddDicts
      :: forall c f.
         ( AllB c (HKD structure hkt)
         )
      => HKD structure hkt f
      -> HKD structure hkt (Dict c `Product` f)
    baddDicts = withConstrainedFieldsHKD @c @(HKD structure hkt) @hkt @f
