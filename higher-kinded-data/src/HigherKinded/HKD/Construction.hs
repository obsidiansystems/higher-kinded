{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Based on 'Data.Generic.HKD.Construction from package 'higgledy'
--   by Tom Harding ((c) Tom Harding, 2019, MIT)

module HigherKinded.HKD.Construction
  ( Construct (..)
  ) where

import Control.Lens (view)
import Data.Kind
import GHC.Generics

import HigherKinded.HKD.Types
import HigherKinded.HKT



-- | When working with the HKD representation, it is useful to have a way to
-- convert to and from our original type. To do this, we can:
--
-- * @construct@ the original type from our HKD representation, and
--
-- * @deconstruct@ the original type /into/ our HKD representation.
--
-- As an example, we can try (unsuccessfully) to construct an @(Int, Bool)@
-- tuple from an unpopulated partial structure.
--
-- >>> :set -XTypeApplications
-- >>> import Data.Monoid (Last)
--
-- >>> construct (mempty @(HKD (Int, Bool) Last))
-- Last {getLast = Nothing}
--
-- We can also /deconstruct/ a tuple into a partial structure:
--
-- >>> deconstruct @[] ("Hello", True)
-- (,) ["Hello"] [True]
--
-- These two methods also satisfy the round-tripping property:
--
-- prop> construct (deconstruct x) == [ x :: (Int, Bool, String) ]
class Construct (hkd :: (Type -> Type) -> Type) (structure :: Type) (f :: Type -> Type) where
  fromHKD :: hkd f -> f structure
  toHKD :: structure -> hkd f

instance
    ( Applicative f
    , Generic structure
    , GConstruct (Rep structure) hkt f
    )
    => Construct (HKD structure hkt) structure f where
  fromHKD = fmap to . gFromHKD @(Rep structure) @hkt @f . unGHKD
  toHKD = GHKD . gToHKD @(Rep structure) @hkt @f . from



class GConstruct (rep :: Type -> Type) (hkt :: ((Type -> Type) -> Type -> Type)) (f :: Type -> Type) where
  gFromHKD :: GHKD_ rep hkt f () -> f (rep ())
  gToHKD :: rep () -> GHKD_ rep hkt f ()

instance (Functor f, GConstruct inner hkt f)
    => GConstruct (M1 index meta inner) hkt f where
  gFromHKD = fmap M1 . gFromHKD @inner @hkt @f . unM1
  gToHKD = M1 . gToHKD @inner @hkt @f . unM1

instance (Applicative f, GConstruct left hkt f, GConstruct right hkt f)
    => GConstruct (left :*: right) hkt f where
  gFromHKD (l :*: r) = (:*:) <$> gFromHKD @left @hkt @f l <*> gFromHKD @right @hkt @f r
  gToHKD (l :*: r) = gToHKD @left @hkt @f l :*: gToHKD @right @hkt @f r

instance
    ( Applicative f
    , HKT hkt f
    , Generic (hkt f inner)
    , UnHKT (hkt f inner) ~ GUnHKT (Rep (hkt f inner))
    , Rep (hkt f inner) ~ (D1 d (C1 c (S1 s' (Rec0 x))))
    )
  =>
    GConstruct (K1 index inner) hkt f
  where
    gFromHKD (K1 x) = fmap K1 $ fromHKT' @hkt @f @inner $ view _UnHKT' x
    gToHKD (K1 x) = K1 (view _HKT' $ toHKT' @hkt @f @inner $ pure @f x)
