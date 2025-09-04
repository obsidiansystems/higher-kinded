{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module HigherKinded.HKD.Class
  ( module HigherKinded.HKD.Class
  , FunctorB (..)
  , ApplicativeB (..)
  , TraversableB (..)
  , ConstraintsB (..)
  , Dict (..)
  ) where

import Barbies (ConstraintsB (..), FunctorB (..), ApplicativeB (..), TraversableB (..))
import Barbies.Constraints (Dict (..))
import Data.Functor.Identity
import Data.Functor.Product (Product (..))
import Data.Kind
import Data.Proxy
import GHC.Generics hiding (from, to)
import GHC.Generics qualified as G

import HigherKinded.HKT

import HigherKinded.HKD.Internal.Exposed



class
    ( IsNormalHKD hkd hkt f
    , IsNormalHKD hkd hkt Exposed
    , forall
        (f' :: Type -> Type)
        (g' :: Type -> Type)
        (rep_exp :: Type -> Type)
        (rep_f' :: Type -> Type)
        (rep_g' :: Type -> Type)
        . ( IsNormalHKD hkd hkt f'
          , IsNormalHKD hkd hkt g'
          , rep_exp ~ NormalHKD hkd Exposed
          , rep_f' ~ NormalHKD hkd f'
          , rep_g' ~ NormalHKD hkd g'
          ) => GTraversableNormalHKDRep hkt f' g' rep_exp rep_f' rep_g'
    , forall
        (f' :: Type -> Type)
        (g' :: Type -> Type)
        (h' :: Type -> Type)
        (rep_exp :: Type -> Type)
        (rep_f' :: Type -> Type)
        (rep_g' :: Type -> Type)
        (rep_h' :: Type -> Type)
        . ( IsNormalHKD hkd hkt f'
          , IsNormalHKD hkd hkt g'
          , IsNormalHKD hkd hkt h'
          , rep_exp ~ NormalHKD hkd Exposed
          , rep_f' ~ NormalHKD hkd f'
          , rep_g' ~ NormalHKD hkd g'
          , rep_h' ~ NormalHKD hkd h'
          ) => GBiTraversableNormalHKDRep hkt f' g' h' rep_exp rep_f' rep_g' rep_h'
    )
  => IsHKD (hkd :: (Type -> Type) -> Type) (hkt :: (Type -> Type) -> Type -> Type) (f :: Type -> Type)

instance
    ( IsNormalHKD hkd hkt f
    , IsNormalHKD hkd hkt Exposed
    , forall
        (f' :: Type -> Type)
        (g' :: Type -> Type)
        (rep_exp :: Type -> Type)
        (rep_f' :: Type -> Type)
        (rep_g' :: Type -> Type)
        . ( IsNormalHKD hkd hkt f'
          , IsNormalHKD hkd hkt g'
          , rep_exp ~ NormalHKD hkd Exposed
          , rep_f' ~ NormalHKD hkd f'
          , rep_g' ~ NormalHKD hkd g'
          ) => GTraversableNormalHKDRep hkt f' g' rep_exp rep_f' rep_g'
    , forall
        (f' :: Type -> Type)
        (g' :: Type -> Type)
        (h' :: Type -> Type)
        (rep_exp :: Type -> Type)
        (rep_f' :: Type -> Type)
        (rep_g' :: Type -> Type)
        (rep_h' :: Type -> Type)
        . ( IsNormalHKD hkd hkt f'
          , IsNormalHKD hkd hkt g'
          , IsNormalHKD hkd hkt h'
          , rep_exp ~ NormalHKD hkd Exposed
          , rep_f' ~ NormalHKD hkd f'
          , rep_g' ~ NormalHKD hkd g'
          , rep_h' ~ NormalHKD hkd h'
          ) => GBiTraversableNormalHKDRep hkt f' g' h' rep_exp rep_f' rep_g' rep_h'
    )
  => IsHKD hkd hkt f

--------------------------------------------------------------------------------

type NormalHKD hkd f = NormalHKDRep f (Rep (hkd Exposed)) (Rep (hkd f))

class
    ( Generic (hkd f)
    , Generic (hkd Exposed)
    , GNormalHKDRep hkt f (Rep (hkd Exposed)) (Rep (hkd f))
    )
  =>
    IsNormalHKD hkd hkt f
  where
    toNormalHKD :: hkd f -> NormalHKD hkd f x
    fromNormalHKD :: NormalHKD hkd f x -> hkd f

instance
    ( Generic (hkd f)
    , Generic (hkd Exposed)
    , GNormalHKDRep hkt f (Rep (hkd Exposed)) (Rep (hkd f))
    )
  =>
    IsNormalHKD hkd hkt f
  where
    toNormalHKD hkd = gtoNormalHKDRep @hkt @f @(Rep (hkd Exposed)) @(Rep (hkd f)) $ G.from hkd
    fromNormalHKD hkd = G.to $ gfromNormalHKDRep @hkt @f @(Rep (hkd Exposed)) @(Rep (hkd f)) hkd



class GNormalHKDRep hkt f rep_exp rep where
  type NormalHKDRep f rep_exp rep :: Type -> Type

  gtoNormalHKDRep
    :: rep p
    -> NormalHKDRep f rep_exp rep p

  gfromNormalHKDRep
    :: NormalHKDRep f rep_exp rep p
    -> rep p

instance GNormalHKDRep hkt f V1 V1 where
  type NormalHKDRep f V1 V1 = V1

  gtoNormalHKDRep _ = undefined

  gfromNormalHKDRep _ = undefined

instance GNormalHKDRep hkt f U1 U1 where
  type NormalHKDRep f U1 U1 = U1

  gtoNormalHKDRep _ = U1

  gfromNormalHKDRep _ = U1

instance
    GNormalHKDRep hkt f rep_exp rep
  =>
    GNormalHKDRep hkt f (Rec1 rep_exp) (Rec1 rep)
  where
    type NormalHKDRep f (Rec1 rep_exp) (Rec1 rep) = Rec1 (NormalHKDRep f rep_exp rep)

    gtoNormalHKDRep ~(Rec1 rep) = Rec1 $ gtoNormalHKDRep @hkt @f @rep_exp @rep rep

    gfromNormalHKDRep ~(Rec1 rep) = Rec1 $ gfromNormalHKDRep @hkt @f @rep_exp @rep rep

instance
    GNormalHKDRep hkt f rep_exp rep
  =>
    GNormalHKDRep hkt f (M1 i c rep_exp) (M1 i c rep)
  where
    type NormalHKDRep f (M1 i c rep_exp) (M1 i c rep) = M1 i c (NormalHKDRep f rep_exp rep)

    gtoNormalHKDRep ~(M1 rep) = M1 $ gtoNormalHKDRep @hkt @f @rep_exp @rep rep

    gfromNormalHKDRep ~(M1 rep) = M1 $ gfromNormalHKDRep @hkt @f @rep_exp @rep rep

instance
    ( GNormalHKDRep hkt f rep_exp1 rep1
    , GNormalHKDRep hkt f rep_exp2 rep2
    )
  =>
    GNormalHKDRep hkt f (rep_exp1 :*: rep_exp2) (rep1 :*: rep2)
  where
    type NormalHKDRep f (rep_exp1 :*: rep_exp2) (rep1 :*: rep2) = NormalHKDRep f rep_exp1 rep1 :*: NormalHKDRep f rep_exp2 rep2

    gtoNormalHKDRep ~(rep1 :*: rep2) =
          gtoNormalHKDRep @hkt @f @rep_exp1 @rep1 rep1
      :*: gtoNormalHKDRep @hkt @f @rep_exp2 @rep2 rep2

    gfromNormalHKDRep ~(rep1 :*: rep2) =
          gfromNormalHKDRep @hkt @f @rep_exp1 @rep1 rep1
      :*: gfromNormalHKDRep @hkt @f @rep_exp2 @rep2 rep2

instance
    ( GNormalHKDRep hkt f rep_exp1 rep1
    , GNormalHKDRep hkt f rep_exp2 rep2
    )
  =>
    GNormalHKDRep hkt f (rep_exp1 :+: rep_exp2) (rep1 :+: rep2)
  where
    type NormalHKDRep f (rep_exp1 :+: rep_exp2) (rep1 :+: rep2) = NormalHKDRep f rep_exp1 rep1 :+: NormalHKDRep f rep_exp2 rep2

    gtoNormalHKDRep = \case
      L1 rep1 -> L1 $ gtoNormalHKDRep @hkt @f @rep_exp1 @rep1 rep1
      R1 rep2 -> R1 $ gtoNormalHKDRep @hkt @f @rep_exp2 @rep2 rep2

    gfromNormalHKDRep = \case
      L1 rep1 -> L1 $ gfromNormalHKDRep @hkt @f @rep_exp1 @rep1 rep1
      R1 rep2 -> R1 $ gfromNormalHKDRep @hkt @f @rep_exp2 @rep2 rep2

instance
    ( f_x ~$ hkt f x
    )
  =>
    GNormalHKDRep (hkt :: (Type -> Type) -> Type -> Type) f (K1 i (Exposed x)) (K1 i f_x)
  where
    type NormalHKDRep f (K1 i (Exposed x)) (K1 i f_x) = K1 i (f x)

    gtoNormalHKDRep ~(K1 f_x) = K1 $ fromHKT @hkt @f @x f_x

    gfromNormalHKDRep ~(K1 f_x) = K1 $ toHKT @hkt @f @x f_x

instance
    IsNormalHKD hkd hkt f
  =>
    GNormalHKDRep hkt f (K1 i (hkd Exposed)) (K1 i (hkd f))
  where
    type NormalHKDRep f (K1 i (hkd Exposed)) (K1 i (hkd f)) = K1 i (NormalHKD hkd f ())

    gtoNormalHKDRep ~(K1 hkd) = K1 $ toNormalHKD @hkd @hkt @f hkd

    gfromNormalHKDRep ~(K1 hkd) = K1 $ fromNormalHKD @hkd @hkt @f hkd

instance
    IsNormalHKD hkd hkt (t f)
  =>
    GNormalHKDRep hkt f (K1 i (hkd (t Exposed))) (K1 i (hkd (t f)))
  where
    type NormalHKDRep f (K1 i (hkd (t Exposed))) (K1 i (hkd (t f))) = K1 i (NormalHKD hkd (t f) ())

    gtoNormalHKDRep ~(K1 hkd) = K1 $ toNormalHKD @hkd @hkt @(t f) hkd

    gfromNormalHKDRep ~(K1 hkd) = K1 $ fromNormalHKD @hkd @hkt @(t f) hkd

--------------------------------------------------------------------------------

class
    IsoHKD
      (hkd1 :: (Type -> Type) -> Type)
      (hkd2 :: (Type -> Type) -> Type)
      (hkt1 :: (Type -> Type) -> Type -> Type)
      (hkt2 :: (Type -> Type) -> Type -> Type)
      (f :: Type -> Type)
  where
    isoHKD :: hkd1 f -> hkd2 f

    default isoHKD
      :: ( IsNormalHKD hkd1 hkt1 f
         , IsNormalHKD hkd2 hkt2 f
         , NormalHKD hkd1 f ~ NormalHKD hkd2 f
         )
      => hkd1 f -> hkd2 f
    isoHKD = fromNormalHKD @hkd2 @hkt2 @f @() . toNormalHKD @hkd1 @hkt1 @f @()

instance {-# OVERLAPPABLE #-}
    ( IsNormalHKD hkd1 hkt1 f
    , IsNormalHKD hkd2 hkt2 f
    , NormalHKD hkd1 f ~ NormalHKD hkd2 f
    )
  => IsoHKD hkd1 hkd2 hkt1 hkt2 f

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
       , GBiTraversableHKD hkd hkt f g h
       )
    => (forall a. f a -> g a -> t (h a))
    -> hkd f
    -> hkd g
    -> t (hkd h)
  bitraverseHKD combine (hkd_f :: hkd f) (hkd_g :: hkd g) =
    gbitraverseHKD @hkd @hkt @f @g @h combine hkd_f hkd_g

instance {-# OVERLAPPABLE #-} GBiTraversableHKD hkd hkt f g h => BiTraversableHKD hkd hkt f g h



class
    ( IsNormalHKD hkd hkt f
    , IsNormalHKD hkd hkt g
    , IsNormalHKD hkd hkt h
    , GBiTraversableNormalHKDRep hkt f g h (NormalHKD hkd Exposed) (NormalHKD hkd f) (NormalHKD hkd g) (NormalHKD hkd h)
    )
  =>
    GBiTraversableHKD hkd hkt f g h
  where
    gbitraverseHKD
      :: Applicative t
      => (forall a. f a -> g a -> t (h a))
      -> hkd f
      -> hkd g
      -> t (hkd h)

instance
    ( IsNormalHKD hkd hkt f
    , IsNormalHKD hkd hkt g
    , IsNormalHKD hkd hkt h
    , GBiTraversableNormalHKDRep hkt f g h (NormalHKD hkd Exposed) (NormalHKD hkd f) (NormalHKD hkd g) (NormalHKD hkd h)
    )
  =>
    GBiTraversableHKD hkd hkt f g h
  where
    gbitraverseHKD combine (hkd_f :: hkd f) (hkd_g :: hkd g) =
          fromNormalHKD @hkd @hkt @h @()
      <$> gbitraverseNormalHKDRep @hkt @f @g @h @(NormalHKD hkd Exposed) @(NormalHKD hkd f) @(NormalHKD hkd g) @(NormalHKD hkd h)
            combine
            (toNormalHKD @hkd @hkt @f @() hkd_f)
            (toNormalHKD @hkd @hkt @g @() hkd_g)



class GBiTraversableNormalHKDRep hkt f g h rep_exp rep_f rep_g rep_h where
  gbitraverseNormalHKDRep
    :: Applicative t
    => (forall a. f a -> g a -> t (h a))
    -> rep_f p
    -> rep_g p
    -> t (rep_h p)

instance GBiTraversableNormalHKDRep hkt f g h V1 V1 V1 V1 where
  gbitraverseNormalHKDRep _ _ _ = pure undefined

instance GBiTraversableNormalHKDRep hkt f g h U1 U1 U1 U1 where
  gbitraverseNormalHKDRep _ _ _ = pure U1

instance
    GBiTraversableNormalHKDRep hkt f g h rep_exp rep_f rep_g rep_h
  =>
    GBiTraversableNormalHKDRep hkt f g h (Rec1 rep_exp) (Rec1 rep_f) (Rec1 rep_g) (Rec1 rep_h)
  where
    gbitraverseNormalHKDRep combine ~(Rec1 rep_f) ~(Rec1 rep_g) = Rec1 <$> gbitraverseNormalHKDRep @hkt @f @g @h @rep_exp @rep_f @rep_g @rep_h combine rep_f rep_g

instance
    GBiTraversableNormalHKDRep hkt f g h rep_exp rep_f rep_g rep_h
  =>
    GBiTraversableNormalHKDRep hkt f g h (M1 i c rep_exp) (M1 i c rep_f) (M1 i c rep_g) (M1 i c rep_h)
  where
    gbitraverseNormalHKDRep combine ~(M1 rep_f) ~(M1 rep_g) = M1 <$> gbitraverseNormalHKDRep @hkt @f @g @h @rep_exp @rep_f @rep_g @rep_h combine rep_f rep_g

instance
    ( GBiTraversableNormalHKDRep hkt f g h rep_exp1 rep_f1 rep_g1 rep_h1
    , GBiTraversableNormalHKDRep hkt f g h rep_exp2 rep_f2 rep_g2 rep_h2
    )
  =>
    GBiTraversableNormalHKDRep hkt f g h (rep_exp1 :*: rep_exp2) (rep_f1 :*: rep_f2) (rep_g1 :*: rep_g2) (rep_h1 :*: rep_h2)
  where
    gbitraverseNormalHKDRep combine ~(rep_f1 :*: rep_f2) ~(rep_g1 :*: rep_g2) =
      (:*:)
        <$> gbitraverseNormalHKDRep @hkt @f @g @h @rep_exp1 @rep_f1 @rep_g1 @rep_h1 combine rep_f1 rep_g1
        <*> gbitraverseNormalHKDRep @hkt @f @g @h @rep_exp2 @rep_f2 @rep_g2 @rep_h2 combine rep_f2 rep_g2

instance
    GBiTraversableNormalHKDRep (hkt :: (Type -> Type) -> Type -> Type) f g h (K1 i (Exposed x)) (K1 i (f x)) (K1 i (g x)) (K1 i (h x))
  where
    gbitraverseNormalHKDRep combine ~(K1 f_x) ~(K1 g_x) = K1 <$> combine f_x g_x

instance
    GBiTraversableNormalHKDRep hkt f g h rep_exp rep_f rep_g rep_h
  =>
    GBiTraversableNormalHKDRep hkt f g h (K1 ki (M1 mi mc rep_exp ())) (K1 ki (M1 mi mc rep_f ())) (K1 ki (M1 mi mc rep_g ())) (K1 ki (M1 mi mc rep_h ()))
  where
    gbitraverseNormalHKDRep combine ~(K1 ~(M1 rep_f)) ~(K1 ~(M1 rep_g)) = K1 . M1 <$> gbitraverseNormalHKDRep @hkt @f @g @h @rep_exp @rep_f @rep_g @rep_h combine rep_f rep_g

--------------------------------------------------------------------------------

class TraversableHKD (hkd :: (Type -> Type) -> Type) (hkt :: (Type -> Type) -> Type -> Type) (f :: Type -> Type) (g :: Type -> Type) where
  traverseHKD
    :: Applicative t
    => (forall a. f a -> t (g a))
    -> hkd f
    -> t (hkd g)

  default traverseHKD
    :: ( Applicative t
       , GTraversableHKD hkd hkt f g
       )
    => (forall a. f a -> t (g a))
    -> hkd f
    -> t (hkd g)
  traverseHKD = gtraverseHKD @hkd @hkt @f @g

instance {-# OVERLAPPABLE #-} GTraversableHKD hkd hkt f g => TraversableHKD hkd hkt f g



class
    ( IsNormalHKD hkd hkt f
    , IsNormalHKD hkd hkt g
    , GTraversableNormalHKDRep hkt f g (NormalHKD hkd Exposed) (NormalHKD hkd f) (NormalHKD hkd g)
    )
  =>
    GTraversableHKD hkd hkt f g
  where
    gtraverseHKD
      :: Applicative t
      => (forall a. f a -> t (g a))
      -> hkd f
      -> t (hkd g)

instance
    ( IsNormalHKD hkd hkt f
    , IsNormalHKD hkd hkt g
    , GTraversableNormalHKDRep hkt f g (NormalHKD hkd Exposed) (NormalHKD hkd f) (NormalHKD hkd g)
    )
  =>
    GTraversableHKD hkd hkt f g
  where
    gtraverseHKD f (hkd_f :: hkd f) =
          fromNormalHKD @hkd @hkt @g @()
      <$> gtraverseNormalHKDRep @hkt @f @g @(NormalHKD hkd Exposed) @(NormalHKD hkd f) @(NormalHKD hkd g)
            f
            (toNormalHKD @hkd @hkt @f @() hkd_f)



class GTraversableNormalHKDRep hkt f g rep_exp rep_f rep_g where
  gtraverseNormalHKDRep
    :: Applicative t
    => (forall a. f a -> t (g a))
    -> rep_f p
    -> t (rep_g p)

instance GTraversableNormalHKDRep hkt f g V1 V1 V1 where
  gtraverseNormalHKDRep _ _ = pure undefined

instance GTraversableNormalHKDRep hkt f g U1 U1 U1 where
  gtraverseNormalHKDRep _ _ = pure U1

instance
    GTraversableNormalHKDRep hkt f g rep_exp rep_f rep_g
  =>
    GTraversableNormalHKDRep hkt f g (Rec1 rep_exp) (Rec1 rep_f) (Rec1 rep_g)
  where
    gtraverseNormalHKDRep f ~(Rec1 rep_f) = Rec1 <$> gtraverseNormalHKDRep @hkt @f @g @rep_exp @rep_f @rep_g f rep_f

instance
    GTraversableNormalHKDRep hkt f g rep_exp rep_f rep_g
  =>
    GTraversableNormalHKDRep hkt f g (M1 i c rep_exp) (M1 i c rep_f) (M1 i c rep_g)
  where
    gtraverseNormalHKDRep f ~(M1 rep_f) = M1 <$> gtraverseNormalHKDRep @hkt @f @g @rep_exp @rep_f @rep_g f rep_f

instance
    ( GTraversableNormalHKDRep hkt f g rep_exp1 rep_f1 rep_g1
    , GTraversableNormalHKDRep hkt f g rep_exp2 rep_f2 rep_g2
    )
  =>
    GTraversableNormalHKDRep hkt f g (rep_exp1 :*: rep_exp2) (rep_f1 :*: rep_f2) (rep_g1 :*: rep_g2)
  where
    gtraverseNormalHKDRep f ~(rep_f1 :*: rep_f2) =
      (:*:)
        <$> gtraverseNormalHKDRep @hkt @f @g @rep_exp1 @rep_f1 @rep_g1 f rep_f1
        <*> gtraverseNormalHKDRep @hkt @f @g @rep_exp2 @rep_f2 @rep_g2 f rep_f2

instance
    ( GTraversableNormalHKDRep hkt f g rep_exp1 rep_f1 rep_g1
    , GTraversableNormalHKDRep hkt f g rep_exp2 rep_f2 rep_g2
    )
  =>
    GTraversableNormalHKDRep hkt f g (rep_exp1 :+: rep_exp2) (rep_f1 :+: rep_f2) (rep_g1 :+: rep_g2)
  where
    gtraverseNormalHKDRep f = \case
      L1 rep_f -> L1 <$> gtraverseNormalHKDRep @hkt @f @g @rep_exp1 @rep_f1 @rep_g1 f rep_f
      R1 rep_f -> R1 <$> gtraverseNormalHKDRep @hkt @f @g @rep_exp2 @rep_f2 @rep_g2 f rep_f

instance
    GTraversableNormalHKDRep (hkt :: (Type -> Type) -> Type -> Type) f g (K1 i (Exposed x)) (K1 i (f x)) (K1 i (g x))
  where
    gtraverseNormalHKDRep f ~(K1 f_x) = K1 <$> f f_x

instance
    GTraversableNormalHKDRep hkt f g rep_exp rep_f rep_g
  =>
    GTraversableNormalHKDRep hkt f g (K1 ki (M1 mi mc rep_exp ())) (K1 ki (M1 mi mc rep_f ())) (K1 ki (M1 mi mc rep_g ()))
  where
    gtraverseNormalHKDRep f ~(K1 ~(M1 rep_f)) = K1 . M1 <$> gtraverseNormalHKDRep @hkt @f @g @rep_exp @rep_f @rep_g f rep_f

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
transformHKD f = hoistHKT @hkt1 @f @g @(hkd g) f . fmapHKT @hkt1 @f (mapHKD @hkd @hkt2 f)

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
instance (c x) => GHKDFieldsHave c (K1 i (Exposed x)) (K1 i (Dict c x)) where
  gWithConstrainedFields _ _ = K1 Dict
instance HKDFieldsHave c t =>
    GHKDFieldsHave c (K1 i (t Exposed)) (K1 i (t (Dict c))) where
  gWithConstrainedFields _ _ = K1 (G.to (gWithConstrainedFields (Proxy @c) (Proxy @(Rep (t Exposed)))))
instance HKDFieldsHaveF c t f =>
    GHKDFieldsHave c (K1 i (t (f Exposed))) (K1 i (t (f (Dict c)))) where
  gWithConstrainedFields _ _ = K1 (G.to (gWithConstrainedFields (Proxy @c) (Proxy @(Rep (t (f Exposed))))))
