{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Based on 'HKD' from 'Data.Generic.HKD.Types from package 'higgledy'
--   by Tom Harding ((c) Tom Harding, 2019, MIT)

module HigherKinded.HKD.Types
  ( module HigherKinded.HKD.Types
  , module Barbies
  , Dict (..)
  ) where

import Barbies (ConstraintsB (..), FunctorB (..), ApplicativeB (..), TraversableB (..))
import Barbies.Constraints (Dict (..))
import Data.Function (on)
import Data.Functor.Contravariant (Contravariant (..), phantom)
import Data.Functor.Identity
import Data.Functor.Product (Product (..))
import Data.Kind
import Data.Proxy
import GHC.Generics hiding (from, to)
import GHC.Generics qualified as G
import GHC.TypeLits (KnownSymbol, symbolVal)
import Test.QuickCheck.Arbitrary (Arbitrary (..), CoArbitrary (..))
import Test.QuickCheck.Function (Function (..), functionMap)

import HigherKinded.HKT



type HKD :: Type -> ((Type -> Type) -> Type -> Type) -> (Type -> Type) -> Type
newtype HKD structure hkt f = GHKD { unGHKD :: GHKD_ (Rep structure) hkt f () }


type HKD_ :: Type -> ((Type -> Type) -> Type -> Type) -> (Type -> Type) -> (Type -> Type)
type HKD_ structure hkt f = GHKD_ (Rep structure) hkt f

type GHKD_ :: (Type -> Type) -> ((Type -> Type) -> Type -> Type) -> (Type -> Type) -> (Type -> Type)
type family GHKD_ structureRep hkt f = (res :: Type -> Type) where
  GHKD_ (M1 index meta inner) hkt f = M1 index meta (GHKD_ inner hkt f)
  GHKD_ (left :*: right) hkt f = GHKD_ left hkt f :*: GHKD_ right hkt f
  GHKD_ (left :+: right) hkt f = GHKD_ left hkt f :+: GHKD_ right hkt f
  GHKD_ (K1 index value) hkt f = K1 index (UnHKT (hkt f value))


type NewtypeHKD :: ((Type -> Type) -> Type) -> (Type -> Type) -> Type
type family NewtypeHKD hkd f
type instance NewtypeHKD (HKD structure hkt) f = GUnNewtypeHKD_ (Rep (HKD structure hkt f))

type family GUnNewtypeHKD_ rep where
  GUnNewtypeHKD_ (D1 d (C1 c (S1 s' (Rec0 x)))) = x

--------------------------------------------------------------------------------

type HKDWithDefault tag d = d $< tag

infixr 0 $<
type ($<) :: (k1 -> k2) -> k1 -> k3
type family ($<) d tag where
  ($<) d tag = d tag
  ($<) d tag = d

--------------------------------------------------------------------------------

instance GenericHKD' structure hkt f => Generic (HKD structure hkt f) where
  type Rep (HKD structure hkt f) = HKD_ structure hkt f
  from = phantom . unGHKD
  to   = GHKD . phantom

class (Contravariant (HKD_ structure hkt f), Functor (HKD_ structure hkt f)) => GenericHKD' structure hkt f
instance (Contravariant (HKD_ structure hkt f), Functor (HKD_ structure hkt f)) => GenericHKD' structure hkt f

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

instance (Arbitrary tuple, GToTuple (HKD_ structure hkt f) tuple)
    => Arbitrary (HKD structure hkt f) where
  arbitrary = fmap (GHKD . gfromTuple) arbitrary

instance (CoArbitrary tuple, GToTuple (HKD_ structure hkt f) tuple)
    => CoArbitrary (HKD structure hkt f) where
  coarbitrary (GHKD x) = coarbitrary (gtoTuple x)

instance (Function tuple, Tuple structure hkt f tuple)
    => Function (HKD structure hkt f) where
  function = functionMap toTuple fromTuple

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

class BiTraversableHKD (hkd :: (Type -> Type) -> Type) (hkt :: (Type -> Type) -> Type -> Type) (f :: Type -> Type) (g :: Type -> Type) (h :: Type -> Type) where
  bitraverseHKD
    :: Applicative t
    => (forall a. f a -> g a -> t (h a))
    -> hkd f
    -> hkd g
    -> t (hkd h)

  default bitraverseHKD
    :: ( Applicative t
       , Generic (hkd f)
       , Generic (hkd g)
       , Generic (hkd h)
       , GBiTraversableHKD hkt f g h (Rep (hkd Exposed)) (Rep (hkd f)) (Rep (hkd g)) (Rep (hkd h))
       )
    => (forall a. f a -> g a -> t (h a))
    -> hkd f
    -> hkd g
    -> t (hkd h)
  bitraverseHKD combine (hkd_f :: hkd f) (hkd_g :: hkd g) =
    G.to <$> gbitraverseHKD @hkt @f @g @h @(Rep (hkd Exposed)) @(Rep (hkd f)) @(Rep (hkd g)) @(Rep (hkd h)) combine (G.from hkd_f) (G.from hkd_g)



instance {-# OVERLAPPABLE #-}
    ( Generic (hkd f)
    , Generic (hkd g)
    , Generic (hkd h)
    , GBiTraversableHKD hkt f g h (Rep (hkd Exposed)) (Rep (hkd f)) (Rep (hkd g)) (Rep (hkd h))
    )
  => BiTraversableHKD hkd hkt f g h



instance BiTraversableHKD' structure hkt f g h => BiTraversableHKD (HKD structure hkt) hkt f g h

class
    ( Generic (HKD structure hkt f)
    , Generic (HKD structure hkt g)
    , Generic (HKD structure hkt h)
    , Generic (HKD structure hkt Exposed)
    , GenericHKD' structure hkt f
    , GenericHKD' structure hkt g
    , GenericHKD' structure hkt h
    , GenericHKD' structure hkt Exposed
    , GBiTraversableHKD hkt f g h
        (Rep (HKD structure hkt Exposed))
        (Rep (HKD structure hkt f))
        (Rep (HKD structure hkt g))
        (Rep (HKD structure hkt h))
    )
  => BiTraversableHKD' structure hkt f g h

instance
    ( Generic (HKD structure hkt f)
    , Generic (HKD structure hkt g)
    , Generic (HKD structure hkt h)
    , Generic (HKD structure hkt Exposed)
    , GenericHKD' structure hkt f
    , GenericHKD' structure hkt g
    , GenericHKD' structure hkt h
    , GenericHKD' structure hkt Exposed
    , GBiTraversableHKD hkt f g h
        (Rep (HKD structure hkt Exposed))
        (Rep (HKD structure hkt f))
        (Rep (HKD structure hkt g))
        (Rep (HKD structure hkt h))
    )
  => BiTraversableHKD' structure hkt f g h



class GBiTraversableHKD hkt f g h rep_exp rep_f rep_g rep_h where
  gbitraverseHKD
    :: Applicative t
    => (forall a. f a -> g a -> t (h a))
    -> rep_f p
    -> rep_g p
    -> t (rep_h p)

instance GBiTraversableHKD hkt f g h rep_exp rep_f rep_g rep_h => GBiTraversableHKD hkt f g h (M1 a b rep_exp) (M1 a b rep_f) (M1 a b rep_g) (M1 a b rep_h) where
  gbitraverseHKD combine ~(M1 rep_f) ~(M1 rep_g) = M1 <$> gbitraverseHKD @hkt @f @g @h @rep_exp @rep_f @rep_g @rep_h combine rep_f rep_g

instance (GBiTraversableHKD hkt f g h rep_exp rep_f rep_g rep_h, GBiTraversableHKD hkt f g h rep_exps rep_fs rep_gs rep_hs) => GBiTraversableHKD hkt f g h (rep_exp :*: rep_exps) (rep_f :*: rep_fs) (rep_g :*: rep_gs) (rep_h :*: rep_hs) where
  gbitraverseHKD combine ~(rep_f :*: rep_fs) ~(rep_g :*: rep_gs) =
    (:*:)
      <$> gbitraverseHKD @hkt @f @g @h @rep_exp @rep_f @rep_g @rep_h combine rep_f rep_g
      <*> gbitraverseHKD @hkt @f @g @h @rep_exps @rep_fs @rep_gs @rep_hs combine rep_fs rep_gs

instance GBiTraversableHKD hkt f g h U1 U1 U1 U1 where
  gbitraverseHKD _ ~U1 ~U1 = pure U1

instance
     ( f_a ~$ hkt f a
     , g_a ~$ hkt g a
     , h_a ~$ hkt h a
     )
  =>
    GBiTraversableHKD (hkt :: (Type -> Type) -> Type -> Type) f g h (K1 G.R (Exposed a)) (K1 G.R f_a) (K1 G.R g_a) (K1 G.R h_a)
  where
    gbitraverseHKD combine ~(K1 rep_f) ~(K1 rep_g) = K1 <$> (fmap (toHKT @hkt @h @a) $ combine (fromHKT @hkt @f @a rep_f) (fromHKT @hkt @g @a rep_g))

instance BiTraversableHKD hkd hkt f g h => GBiTraversableHKD hkt f g h (K1 G.R (hkd Exposed)) (K1 G.R (hkd f)) (K1 G.R (hkd g)) (K1 G.R (hkd h)) where
  gbitraverseHKD combine ~(K1 rep_f) ~(K1 rep_g) = K1 <$> bitraverseHKD @hkd @hkt @f @g @h combine rep_f rep_g

-- | newtype mainly used to inspect the tag structure of a particular higher-kinded data type.
--   Prevents overlapping instances in some case. Usually not used in end-user code.
--   (originally from 'beam-core' package)
data Exposed x

--------------------------------------------------------------------------------

class TraversableHKD hkd hkt f g where
  traverseHKD
    :: Applicative t
    => (forall a. f a -> t (g a))
    -> hkd f
    -> t (hkd g)

  default traverseHKD
    :: ( Applicative t
       , BiTraversableHKD hkd hkt f f g
       )
    => (forall a. f a -> t (g a))
    -> hkd f
    -> t (hkd g)
  traverseHKD f hkd = bitraverseHKD @hkd @hkt @f @f @g (\x _ -> f x) hkd hkd



instance {-# OVERLAPPABLE #-} BiTraversableHKD hkd hkt f f g => TraversableHKD hkd hkt f g



instance TraversableHKD' structure hkt f g => TraversableHKD (HKD structure hkt) hkt f g

class
    ( BiTraversableHKD (HKD structure hkt) hkt f f g
    , BiTraversableHKD' structure hkt f f g
    )
  => TraversableHKD' structure hkt f g

instance
    ( BiTraversableHKD (HKD structure hkt) hkt f f g
    , BiTraversableHKD' structure hkt f f g
    )
  => TraversableHKD' structure hkt f g



instance
    ( forall f g. TraversableHKD (HKD structure hkt) hkt f g
    , FunctorB (HKD structure hkt)
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

class FunctorHKD hkd hkt f g where
  mapHKD
    :: (forall a. f a -> g a)
    -> hkd f
    -> hkd g

  default mapHKD
    :: TraversableHKD hkd hkt f g
    => (forall a. f a -> g a)
    -> hkd f
    -> hkd g
  mapHKD f hkd = runIdentity $ traverseHKD @hkd @hkt @f @g (Identity . f) hkd



instance {-# OVERLAPPABLE #-} TraversableHKD hkd hkt f g => FunctorHKD hkd hkt f g



instance FunctorHKD' structure hkt f g => FunctorHKD (HKD structure hkt) hkt f g

class
    ( TraversableHKD (HKD structure hkt) hkt f g
    , TraversableHKD' structure hkt f g
    )
  => FunctorHKD' structure hkt f g

instance
    ( TraversableHKD (HKD structure hkt) hkt f g
    , TraversableHKD' structure hkt f g
    )
  => FunctorHKD' structure hkt f g



pureHKD
  :: forall hkd hkt f.
     ( FunctorHKD hkd hkt f f
     )
  => (forall a. f a)
  -> hkd f
pureHKD zero = mapHKD @hkd @hkt @f @f (const zero) undefined

transformHKD
  :: forall hkd hkt1 hkt2 f g f_hkd_f f_hkd_g g_hkd_g.
     ( Functor f
     , FunctorHKD hkd hkt2 f g
     , f_hkd_f ~$ hkt1 f (hkd f)
     , f_hkd_g ~$ hkt1 f (hkd g)
     , g_hkd_g ~$ hkt1 g (hkd g)
     )
  => (forall x. f x -> g x)
  -> f_hkd_f
  -> g_hkd_g
transformHKD f = hoistHKT @hkt1 @f @g @(hkd g) f . fmapHKT @hkt1 @f (mapHKD @hkd @hkt2 f) --fmapTransformT @hkt1 @f @g @(hkd f) @(hkd g) f (mapHKD @hkd @hkt2 f)



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

class ZippableHKD hkd hkt f g h where
  zipHKD
    :: (forall a. f a -> g a -> h a)
    -> hkd f
    -> hkd g
    -> hkd h

  default zipHKD
    :: ( BiTraversableHKD hkd hkt f g h
       )
    => (forall a. f a -> g a -> h a)
    -> hkd f
    -> hkd g
    -> hkd h
  zipHKD combine f g = runIdentity $ bitraverseHKD @hkd @hkt @f @g @h (\f' g' -> Identity $ combine f' g') f g



instance {-# OVERLAPPABLE #-} BiTraversableHKD hkd hkt f g h => ZippableHKD hkd hkt f g h



instance ZippableHKD' structure hkt f g h => ZippableHKD (HKD structure hkt) hkt f g h

class
    ( BiTraversableHKD (HKD structure hkt) hkt f g h
    , BiTraversableHKD' structure hkt f g h
    )
  => ZippableHKD' structure hkt f g h

instance
    ( BiTraversableHKD (HKD structure hkt) hkt f g h
    , BiTraversableHKD' structure hkt f g h
    )
  => ZippableHKD' structure hkt f g h



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

withConstrainedFieldsHKD
  :: forall c hkd hkt f.
     ( HKDFieldsHave c hkd
     , ZippableHKD hkd hkt (Dict c) f (Dict c `Product` f)
     )
  => hkd f -> hkd (Dict c `Product` f)
withConstrainedFieldsHKD = zipHKD @hkd @hkt (Pair) (withConstraintsHKD @c @hkd)

withConstraintsHKD :: forall c hkd. HKDFieldsHave c hkd => hkd (Dict c)
withConstraintsHKD = G.to $ gWithConstrainedFields (Proxy @c) (Proxy @(Rep (hkd Exposed)))



class
    ( Generic (t (Dict c)), Generic (t Identity), Generic (t Exposed)
    , GHKDFieldsHave c (Rep (t Exposed)) (Rep (t (Dict c)))
    )
  => HKDFieldsHave (c :: Type -> Constraint) t

instance
    ( Generic (t (Dict c)), Generic (t Identity), Generic (t Exposed)
    , GHKDFieldsHave c (Rep (t Exposed)) (Rep (t (Dict c)))
    )
  => HKDFieldsHave (c :: Type -> Constraint) t



class
    ( Generic (t (f (Dict c))), Generic (t (f Identity)), Generic (t (f Exposed))
    , GHKDFieldsHave c (Rep (t (f Exposed))) (Rep (t (f (Dict c))))
    )
  => HKDFieldsHaveF (c :: Type -> Constraint) t f

instance
    ( Generic (t (f (Dict c))), Generic (t (f Identity)), Generic (t (f Exposed))
    , GHKDFieldsHave c (Rep (t (f Exposed))) (Rep (t (f (Dict c))))
    )
  => HKDFieldsHaveF (c :: Type -> Constraint) t f



class GHKDFieldsHave (c :: Type -> Constraint) (exposed :: Type -> Type) withconstraint where
  gWithConstrainedFields :: Proxy c -> Proxy exposed -> withconstraint ()
instance GHKDFieldsHave c exposed withconstraint =>
    GHKDFieldsHave c (M1 s m exposed) (M1 s m withconstraint) where
  gWithConstrainedFields c _ = M1 (gWithConstrainedFields c (Proxy @exposed))
instance GHKDFieldsHave c U1 U1 where
  gWithConstrainedFields _ _ = U1
instance (GHKDFieldsHave c aExp aC, GHKDFieldsHave c bExp bC) =>
  GHKDFieldsHave c (aExp :*: bExp) (aC :*: bC) where
  gWithConstrainedFields be _ = gWithConstrainedFields be (Proxy @aExp) :*: gWithConstrainedFields be (Proxy @bExp)
instance (c x) => GHKDFieldsHave c (K1 G.R (Exposed x)) (K1 G.R (Dict c x)) where
  gWithConstrainedFields _ _ = K1 Dict
instance HKDFieldsHave c t =>
    GHKDFieldsHave c (K1 G.R (t Exposed)) (K1 G.R (t (Dict c))) where
  gWithConstrainedFields _ _ = K1 (G.to (gWithConstrainedFields (Proxy @c) (Proxy @(Rep (t Exposed)))))
instance HKDFieldsHaveF c t f =>
    GHKDFieldsHave c (K1 G.R (t (f Exposed))) (K1 G.R (t (f (Dict c)))) where
  gWithConstrainedFields _ _ = K1 (G.to (gWithConstrainedFields (Proxy @c) (Proxy @(Rep (t (f Exposed))))))



instance
    ( FunctorB (HKD structure hkt)
    , forall f' g' h'. BiTraversableHKD' structure hkt f' g' h'
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
