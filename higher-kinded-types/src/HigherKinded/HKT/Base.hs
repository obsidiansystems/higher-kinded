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

module HigherKinded.HKT.Base where

import Data.Functor.Compose
import Data.Functor.Const
import Data.Functor.Contravariant
import Data.Functor.Identity
import Data.Kind
import Data.Monoid (Ap(..))
import GHC.Generics (Generic)

import HigherKinded.HKT



infixr 0 $~
type ($~) :: (k1 -> k2) -> k1 -> k3
type family ($~) f x where
  ($~) Identity x = x
  ($~) (Ap f) x = f $~ x
  ($~) (Compose f g) x = f $~ (g $~ x)
  ($~) (Const x) _ = x
  ($~) (Op x) y = y -> x
  ($~) f x = f x

type Apply f x = f $~ x



newtype Applied f x = Applied { unApplied :: f $~ x }
  deriving stock (Generic)

type (:$~) = Applied


instance FromHKT Applied Identity x where
  fromHKT' (Applied x) = Identity x

instance (FromHKT Applied f x) => FromHKT Applied (Ap f) x where
  fromHKT' (Applied x) = Ap $ (fromHKT' @Applied @f @x . Applied) $ x

instance (Functor f, FromHKT Applied f (g $~ x), FromHKT Applied g x) => FromHKT Applied (Compose (f :: Type -> Type) (g :: Type -> Type)) x where
  fromHKT' (Applied x) = Compose $ fmap (fromHKT' . Applied) $ (fromHKT' . Applied) $ x

instance FromHKT Applied (Const x) a where
  fromHKT' (Applied x) = Const x

instance FromHKT Applied (Op x) y where
  fromHKT' (Applied x) = Op x

instance {-# OVERLAPPABLE #-} ((f $~ x) ~ (f x)) => FromHKT Applied f x where
  fromHKT' (Applied x) = x


instance ToHKT Applied Identity x where
  toHKT' (Identity x) = Applied x

instance (ToHKT Applied f x) => ToHKT Applied (Ap f) x where
  toHKT' (Ap f_x) = Applied $ (unApplied . toHKT' @Applied @f @x) $ f_x

instance (Functor f, ToHKT Applied f (g $~ x), ToHKT Applied g x) => ToHKT Applied (Compose (f :: Type -> Type) (g :: Type -> Type)) x where
  toHKT' (Compose x) = Applied $ unApplied . toHKT' $ fmap (unApplied . toHKT') x

instance ToHKT Applied (Const x) a where
  toHKT' (Const x) = Applied x

instance ToHKT Applied (Op x) y where
  toHKT' (Op x) = Applied x

instance {-# OVERLAPPABLE #-} ((f $~ x) ~ (f x)) => ToHKT Applied f x where
  toHKT' = Applied


instance
    ( Functor f
    , HKT Applied f
    )
  =>
    Functor (Applied f)
  where
    fmap f = toHKT' . fmap f . fromHKT' @_ @f



pattern App
  :: forall (f :: Type -> Type) x f_x.
     ( f_x ~$ (f :$~ x)
     )
  => f x
  -> f_x
pattern App { unApp } <- (fromApp @f @x -> unApp) where
  App f_x = toApp @f @x f_x

fromApp
  :: forall (f :: Type -> Type) x f_x.
     ( f_x ~$ (f :$~ x)
     )
  => f_x
  -> f x
fromApp = fromHKT @Applied @f @x

toApp
  :: forall (f :: Type -> Type) x f_x.
     ( f_x ~$ (f :$~ x)
     )
  => f x
  -> f_x
toApp = toHKT @Applied @f @x



fmapApp
  :: forall x y f f_x f_y.
     ( Functor f
     , f_x ~$ (f :$~ x)
     , f_y ~$ (f :$~ y)
     )
  => (x -> y)
  -> f_x
  -> f_y
fmapApp = fmapHKT @Applied @f @x @y

hoistApp
  :: forall
       x
       (f :: Type -> Type)
       (g :: Type -> Type)
       f_x g_x.
     ( f_x ~$ (f :$~ x)
     , g_x ~$ (g :$~ x)
     )
  => (forall a. f a -> g a)
  -> f_x
  -> g_x
hoistApp = hoistHKT @Applied @f @g @x

transformApp
  :: forall
       x y
       (f :: Type -> Type)
       (g :: Type -> Type)
       f_x g_y.
     ( f_x ~$ (f :$~ x)
     , g_y ~$ (g :$~ y)
     )
  => (f x -> g y)
  -> f_x
  -> g_y
transformApp = transformHKT @Applied @f @g @x @y
