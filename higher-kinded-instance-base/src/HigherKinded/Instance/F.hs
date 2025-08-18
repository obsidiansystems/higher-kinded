{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

module HigherKinded.Instance.F where

import Data.Functor.Compose
import Data.Functor.Const
import Data.Functor.Contravariant
import Data.Functor.Identity
import Data.Kind
import GHC.Generics (Generic)

import HigherKinded.HKT
import HigherKinded.HKD



type F f x = f $~ x

infixr 0 $~
type ($~) :: (k1 -> k2) -> k1 -> k3
type family ($~) f x where
  ($~) Identity x = x
  ($~) (Compose f g) x = f $~ (g $~ x)
  ($~) (Const x) _ = x
  ($~) (Op x) y = y -> x
  ($~) f x = f x



newtype F' f x = F' { unF' :: f $~ x }
  deriving stock (Generic)


instance FromHKT F' Identity x where
  fromHKT' (F' x) = Identity x

instance (Functor f, FromHKT F' f (g $~ x), FromHKT F' g x) => FromHKT F' (Compose (f :: Type -> Type) (g :: Type -> Type)) x where
  fromHKT' (F' x) = Compose $ fmap (fromHKT' . F') $ (fromHKT' . F') $ x

instance FromHKT F' (Const x) a where
  fromHKT' (F' x) = Const x

instance FromHKT F' (Op x) y where
  fromHKT' (F' x) = Op x

instance {-# OVERLAPPABLE #-} ((f $~ x) ~ (f x)) => FromHKT F' f x where
  fromHKT' (F' x) = x


instance ToHKT F' Identity x where
  toHKT' (Identity x) = F' x

instance (Functor f, ToHKT F' f (g $~ x), ToHKT F' g x) => ToHKT F' (Compose (f :: Type -> Type) (g :: Type -> Type)) x where
  toHKT' (Compose x) = F' $ unF' . toHKT' $ fmap (unF' . toHKT') x

instance ToHKT F' (Const x) a where
  toHKT' (Const x) = F' x

instance ToHKT F' (Op x) y where
  toHKT' (Op x) = F' x

instance {-# OVERLAPPABLE #-} ((f $~ x) ~ (f x)) => ToHKT F' f x where
  toHKT' = F'


instance
    ( Functor f
    , HKT F' f
    )
  =>
    Functor (F' f)
  where
    fmap f = toHKT' . fmap f . fromHKT' @_ @f



pattern F
  :: forall (f :: Type -> Type) x f_x.
     ( f_x ~$ F' f x
     )
  => f x
  -> f_x
pattern F f_x <- (fromF @f @x -> f_x) where
  F f_x = toF @f @x f_x

fromF
  :: forall (f :: Type -> Type) x f_x.
     ( f_x ~$ F' f x
     )
  => f_x
  -> f x
fromF = fromHKT @F' @f @x

toF
  :: forall (f :: Type -> Type) x f_x.
     ( f_x ~$ F' f x
     )
  => f x
  -> f_x
toF = toHKT @F' @f @x


fmapF
  :: forall x y f f_x f_y.
     ( Functor f
     , f_x ~$ F' f x
     , f_y ~$ F' f y
     )
  => (x -> y)
  -> f_x
  -> f_y
fmapF = fmapHKT @F' @f @x @y

hoistF
  :: forall
       x
       (f :: Type -> Type)
       (g :: Type -> Type)
       f_x g_x.
     ( f_x ~$ F' f x
     , g_x ~$ F' g x
     )
  => (forall a. f a -> g a)
  -> f_x
  -> g_x
hoistF = hoistHKT @F' @f @g @x

transformF
  :: forall
       x y
       (f :: Type -> Type)
       (g :: Type -> Type)
       f_x g_y.
     ( f_x ~$ F' f x
     , g_y ~$ F' g y
     )
  => (f x -> g y)
  -> f_x
  -> g_y
transformF = transformHKT @F' @f @g @x @y


traverseF
  :: forall hkd f g t.
     ( Applicative t
     , TraversableHKD hkd F' f g
     )
  => (forall x. f x -> t (g x))
  -> hkd f
  -> t (hkd g)
traverseF = traverseHKD @hkd @F' @f @g

mapF
  :: forall hkd f g.
     ( FunctorHKD hkd F' f g
     )
  => (forall x. f x -> g x)
  -> hkd f
  -> hkd g
mapF = mapHKD @hkd @F' @f @g


transformHKD_F
  :: forall hkd f g f_hkd_f f_hkd_g g_hkd_g.
     ( Functor f
     , FunctorHKD hkd F' f g
     , f_hkd_f ~$ F' f (hkd f)
     , f_hkd_g ~$ F' f (hkd g)
     , g_hkd_g ~$ F' g (hkd g)
     )
  => (forall x. f x -> g x)
  -> f_hkd_f
  -> g_hkd_g
transformHKD_F = transformHKD @hkd @F' @F' @f @g @f_hkd_f @f_hkd_g @g_hkd_g
