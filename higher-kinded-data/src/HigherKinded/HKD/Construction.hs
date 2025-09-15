{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

-- | Based on 'Data.Generic.HKD.Construction from package 'higgledy'
--   by Tom Harding ((c) Tom Harding, 2019, MIT)

module HigherKinded.HKD.Construction where

import Control.Lens (view)
import Data.Kind
import GHC.Generics

import HigherKinded.HKT
import HigherKinded.HKT.Base

import HigherKinded.HKD.Generic



class ConstructHKD (hkd :: (Type -> Type) -> Type) (structure :: Type) (hkt :: (Type -> Type) -> Type -> Type) (f :: Type -> Type) where
  fromHKD :: hkd f -> f structure
  toHKD :: f structure -> hkd f

instance {-# OVERLAPPABLE #-} GConstructHKD hkd structure hkt f => ConstructHKD hkd structure hkt f where
  fromHKD = fmap to . gFromHKD @(Rep structure) @hkt @f . from
  toHKD = to . gToHKD @(Rep structure) @hkt @f . fmap from

class
    ( Applicative f
    , Generic structure
    , GConstructHKDRep (Rep structure) hkt f
    , Generic (hkd f)
    , Rep (hkd f) ~ GHKD_ (Rep structure) hkt f
    )
  => GConstructHKD hkd structure hkt f

instance
    ( Applicative f
    , Generic structure
    , GConstructHKDRep (Rep structure) hkt f
    , Generic (hkd f)
    , Rep (hkd f) ~ GHKD_ (Rep structure) hkt f
    )
  => GConstructHKD hkd structure hkt f

pattern HKD
  :: forall hkd structure hkt f.
     ConstructHKD hkd structure hkt f
  => f structure
  -> hkd f
pattern HKD unHKD <- (fromHKD @hkd @structure @hkt @f -> unHKD) where
  HKD x = toHKD @hkd @structure @hkt @f x



instance GConstructHKD (HKD structure hkt) structure hkt f => ConstructHKD (HKD structure hkt) structure hkt f where
  fromHKD = fmap to . gFromHKD @(Rep structure) @hkt @f . unGHKD
  toHKD = GHKD . gToHKD @(Rep structure) @hkt @f . fmap from



class GConstructHKDRep (rep :: Type -> Type) (hkt :: ((Type -> Type) -> Type -> Type)) (f :: Type -> Type) where
  gFromHKD :: GHKD_ rep hkt f () -> f (rep ())
  gToHKD :: f (rep ()) -> GHKD_ rep hkt f ()

instance (Functor f, GConstructHKDRep inner hkt f)
    => GConstructHKDRep (M1 index meta inner) hkt f where
  gFromHKD = fmap M1 . gFromHKD @inner @hkt @f . unM1
  gToHKD = M1 . gToHKD @inner @hkt @f . fmap unM1

instance (Applicative f, GConstructHKDRep left hkt f, GConstructHKDRep right hkt f)
    => GConstructHKDRep (left :*: right) hkt f where
  gFromHKD (l :*: r) = (:*:) <$> gFromHKD @left @hkt @f l <*> gFromHKD @right @hkt @f r
  gToHKD lr = gToHKD @left @hkt @f ((\(l :*: _) -> l) <$> lr) :*: gToHKD @right @hkt @f ((\(_ :*: r) -> r) <$> lr)

instance
    ( Functor f
    , ConstructHKD (HKD subHKD hkt) subHKD hkt f
    , GHKD_ (K1 index (SubHKD subHKD)) hkt f ~ K1 index (HKD subHKD hkt f)
    )
  =>
    GConstructHKDRep (K1 index (SubHKD subHKD)) hkt f
  where
    gFromHKD = fmap (K1 . SubHKD) . fromHKD @(HKD subHKD hkt) @subHKD @hkt @f . unK1
    gToHKD = K1 . toHKD @(HKD subHKD hkt) @subHKD @hkt @f . fmap (unSubHKD . unK1)

instance
    ( Functor f
    , subHKD' ~ HKD subHKD Applied t
    , ConstructHKD (HKD subHKD Applied) subHKD Applied t
    , ConstructHKD (HKD subHKD' hkt) subHKD' hkt f
    , GHKD_ (K1 index (SubHKD (t subHKD))) hkt f ~ K1 index (HKD subHKD' hkt f)
    )
  =>
    GConstructHKDRep (K1 index (SubHKD (t subHKD))) hkt f
  where
    gFromHKD =
        fmap (K1 . SubHKD . fromHKD @(HKD subHKD Applied) @subHKD @Applied @t)
      . fromHKD @(HKD subHKD' hkt) @subHKD' @hkt @f
      . unK1
    gToHKD =
        K1
      . toHKD @(HKD subHKD' hkt) @subHKD' @hkt @f
      . fmap (toHKD @(HKD subHKD Applied) @subHKD @Applied @t . unSubHKD . unK1)

instance
    ( Functor f
    , Functor t
    , subHKD' ~ HKD subHKD Applied t
    , ConstructHKD (HKD subHKD Applied) subHKD Applied t
    , ConstructHKD (HKD subHKD' hkt) subHKD' hkt f
    , GHKD_ (K1 index (t (SubHKD subHKD))) hkt f ~ K1 index (HKD subHKD' hkt f)
    )
  =>
    GConstructHKDRep (K1 index (t (SubHKD subHKD))) hkt f
  where
    gFromHKD =
        fmap (K1 . fmap SubHKD)
      . fmap (fromHKD @(HKD subHKD Applied) @subHKD @Applied @t)
      . fromHKD @(HKD subHKD' hkt) @subHKD' @hkt @f
      . unK1
    gToHKD =
        K1
      . toHKD @(HKD subHKD' hkt) @subHKD' @hkt @f
      . fmap (toHKD @(HKD subHKD Applied) @subHKD @Applied @t)
      . fmap (fmap unSubHKD . unK1)

instance {-# OVERLAPPABLE #-}
    ( Applicative f
    , FromHKT hkt f inner
    , ToHKT hkt f inner
    , Generic (hkt f inner)
    , GHKD_ (K1 index inner) hkt f ~ K1 index (UnHKT (hkt f inner))
    , Rep (hkt f inner) ~ (D1 d (C1 c (S1 s' (Rec0 x))))
    )
  =>
    GConstructHKDRep (K1 index inner) hkt f
  where
    gFromHKD = fmap K1 . fromHKT' @hkt @f @inner . view _UnHKT' . unK1
    gToHKD = K1 . (view _HKT' . toHKT' @hkt @f @inner) . fmap unK1
