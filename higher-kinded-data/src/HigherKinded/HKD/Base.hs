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

module HigherKinded.HKD.Base where

import Data.Functor.Compose
import Data.Functor.Const
import Data.Functor.Contravariant
import Data.Functor.Identity
import Data.Kind
import GHC.Generics (Generic)

import HigherKinded.HKD.Class
import HigherKinded.HKD.Construction
import HigherKinded.HKD.Generic
import HigherKinded.HKT



type (|>) structure = HKD structure Applied

type F structure = (|>) structure

pattern F
  :: forall structure f.
     ConstructHKD (F structure) structure Applied f
  => f structure
  -> F structure f
pattern F { unF } <- (fromHKD @(F structure) @structure @Applied @f -> unF) where
  F x = toHKD @(F structure) @structure @Applied @f x



bitraverseF
  :: forall structure f g h t.
     ( Applicative t
     , BiTraversableHKD (F structure) Applied f g h
     )
  => (forall x. f x -> g x -> t (h x))
  -> structure |> f
  -> structure |> g
  -> t (structure |> h)
bitraverseF = bitraverseApp @(F structure) @f @g @h

zipF
  :: forall structure f g h.
     ( ZippableHKD (F structure) Applied f g h
     )
  => (forall a. f a -> g a -> h a)
  -> structure |> f
  -> structure |> g
  -> structure |> h
zipF = zipApp @(F structure) @f @g @h

traverseF
  :: forall structure f g t.
     ( Applicative t
     , TraversableHKD (F structure) Applied f g
     )
  => (forall x. f x -> t (g x))
  -> structure |> f
  -> t (structure |> g)
traverseF = traverseApp @(F structure) @f @g

mapF
  :: forall structure f g.
     ( FunctorHKD (F structure) Applied f g
     )
  => (forall x. f x -> g x)
  -> structure |> f
  -> structure |> g
mapF = mapApp @(F structure) @f @g

pureF
  :: forall structure f.
     ( FunctorHKD (F structure) Applied f f
     )
  => (forall a. f a)
  -> structure |> f
pureF = pureApp @(F structure) @f



infixr 0 $~
type ($~) :: (k1 -> k2) -> k1 -> k3
type family ($~) f x where
  ($~) Identity x = x
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



bitraverseApp
  :: forall hkd f g h t.
     ( Applicative t
     , BiTraversableHKD hkd Applied f g h
     )
  => (forall x. f x -> g x -> t (h x))
  -> hkd f
  -> hkd g
  -> t (hkd h)
bitraverseApp = bitraverseHKD @hkd @Applied @f @g @h

zipApp
  :: forall hkd f g h.
     ( ZippableHKD hkd Applied f g h
     )
  => (forall a. f a -> g a -> h a)
  -> hkd f
  -> hkd g
  -> hkd h
zipApp = zipHKD @hkd @Applied @f @g @h

traverseApp
  :: forall hkd f g t.
     ( Applicative t
     , TraversableHKD hkd Applied f g
     )
  => (forall x. f x -> t (g x))
  -> hkd f
  -> t (hkd g)
traverseApp = traverseHKD @hkd @Applied @f @g

mapApp
  :: forall hkd f g.
     ( FunctorHKD hkd Applied f g
     )
  => (forall x. f x -> g x)
  -> hkd f
  -> hkd g
mapApp = mapHKD @hkd @Applied @f @g

pureApp
  :: forall hkd f.
     ( FunctorHKD hkd Applied f f
     )
  => (forall a. f a)
  -> hkd f
pureApp = pureHKD @hkd @Applied @f



transformApplied
  :: forall hkd f g f_hkd_f f_hkd_g g_hkd_g.
     ( Functor f
     , FunctorHKD hkd Applied f g
     , f_hkd_f ~$ Applied f (hkd f)
     , f_hkd_g ~$ Applied f (hkd g)
     , g_hkd_g ~$ Applied g (hkd g)
     )
  => (forall x. f x -> g x)
  -> f_hkd_f
  -> g_hkd_g
transformApplied = transformHKD @hkd @Applied @Applied @f @g @f_hkd_f @f_hkd_g @g_hkd_g
