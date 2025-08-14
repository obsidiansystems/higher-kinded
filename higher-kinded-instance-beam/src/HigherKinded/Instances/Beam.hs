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
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module HigherKinded.Instances.Beam
  ( module HigherKinded.Instances.Beam
  , Columnar
  , Columnar'
  ) where


import Data.Functor.Identity
import Data.Kind
import Data.Some
import Database.Beam.Schema.Tables
import GHC.Generics (Generic)

import HigherKinded.HKT
import HigherKinded.HKD



deriving stock instance (Generic (Columnar' f a))

unColumnar' :: Columnar' f a -> Columnar f a
unColumnar' (Columnar' x) = x


instance FromHKT Columnar' Identity a where
  fromHKT' (Columnar' a) = Identity a

instance {-# OVERLAPPABLE #-} (Columnar f a ~ f a) => FromHKT Columnar' f a where
  fromHKT' (Columnar' a) = a


instance ToHKT Columnar' Identity a where
  toHKT' (Identity a) = Columnar' a

instance {-# OVERLAPPABLE #-} (Columnar f a ~ f a) => ToHKT Columnar' f a where
  toHKT' = Columnar'


instance
    ( Functor f
    , HKT Columnar' f
    )
  =>
    Functor (Columnar' f)
  where
    fmap f = toHKT' . fmap f . fromHKT' @_ @f


instance {-# OVERLAPPING #-} (Beamable hkd, HKT Columnar' f, HKT Columnar' g, HKT Columnar' h) => BiTraversableHKD hkd Columnar' f g h where
  bitraverseHKD combine f g =
    zipBeamFieldsM
      (\(f' :: Columnar' f a)
        (g' :: Columnar' g a)
      -> fmap (toHKT' @Columnar' @h @a) $ combine (fromHKT' @Columnar' @f @a f') (fromHKT' @Columnar' @g @a g')
      ) f g



pattern Columnar
  :: forall f a f_a.
     ( f_a ~$ Columnar' f a
     )
  => f a
  -> f_a
pattern Columnar f_a <- (fromColumnar @f @a -> f_a) where
  Columnar f_a = toColumnar @f @a f_a

fromColumnar
  :: forall f a f_a.
     ( f_a ~$ Columnar' f a
     )
  => f_a
  -> f a
fromColumnar = fromHKT @Columnar' @f @a

toColumnar
  :: forall f a f_a.
     ( f_a ~$ Columnar' f a
     )
  => f a
  -> f_a
toColumnar = toHKT @Columnar' @f @a


fmapColumnar
  :: forall a b f f_a f_b.
     ( Functor f
     , f_a ~$ Columnar' f a
     , f_b ~$ Columnar' f b
     )
  => (a -> b)
  -> f_a
  -> f_b
fmapColumnar = fmapHKT @Columnar' @f @a @b

hoistColumnar
  :: forall a f g f_a g_a.
     ( f_a ~$ Columnar' f a
     , g_a ~$ Columnar' g a
     )
  => (forall x. f x -> g x)
  -> f_a
  -> g_a
hoistColumnar = hoistHKT @Columnar' @f @g @a

transformColumnar
  :: forall a b f g f_a g_b.
     ( f_a ~$ Columnar' f a
     , g_b ~$ Columnar' g b
     )
  => (f a -> g b)
  -> f_a
  -> g_b
transformColumnar = transformHKT @Columnar' @f @g @a @b


traverseColumnars
  :: forall hkd f g t.
     ( Applicative t
     , TraversableHKD hkd Columnar' f g
     )
  => (forall x. f x -> t (g x))
  -> hkd f
  -> t (hkd g)
traverseColumnars = traverseHKD @hkd @Columnar' @f @g

mapColumnars
  :: forall hkd f g.
     ( FunctorHKD hkd Columnar' f g
     )
  => (forall x. f x -> g x)
  -> hkd f
  -> hkd g
mapColumnars = mapHKD @hkd @Columnar' @f @g


transformColumnars
  :: forall hkd f g f_hkd_f f_hkd_g g_hkd_g.
     ( Functor f
     , FunctorHKD hkd Columnar' f g
     , f_hkd_f ~$ Columnar' f (hkd f)
     , f_hkd_g ~$ Columnar' f (hkd g)
     , g_hkd_g ~$ Columnar' g (hkd g)
     )
  => (forall x. f x -> g x)
  -> f_hkd_f
  -> g_hkd_g
transformColumnars = transformHKD @hkd @Columnar' @Columnar' @f @g @f_hkd_f @f_hkd_g @g_hkd_g



type Beamed :: (Type -> Type) -> Type -> Type
type family Beamed f a where
  Beamed f (Some t) = t f
  Beamed f a = Columnar f a


newtype Beamed' f a = Beamed' { unBeamed' :: Beamed f a }
  deriving stock (Generic)

instance {-# OVERLAPPABLE #-} (Beamed f a ~ f a) => FromHKT Beamed' f a where
  fromHKT' (Beamed' a) = a

instance {-# OVERLAPPABLE #-} (Beamed f a ~ f a) => ToHKT Beamed' f a where
  toHKT' = Beamed'



pattern Beamed
  :: forall f a f_a.
     ( f_a ~$ Beamed' f a
     )
  => f a
  -> f_a
pattern Beamed f_a <- (fromBeamed @f @a -> f_a) where
  Beamed f_a = toBeamed @f @a f_a

fromBeamed
  :: forall f a f_a.
     ( f_a ~$ Beamed' f a
     )
  => f_a
  -> f a
fromBeamed = fromHKT @Beamed' @f @a

toBeamed
  :: forall f a f_a.
     ( f_a ~$ Beamed' f a
     )
  => f a
  -> f_a
toBeamed = toHKT @Beamed' @f @a


fmapBeamed
  :: forall a b f f_a f_b.
     ( Functor f
     , f_a ~$ Beamed' f a
     , f_b ~$ Beamed' f b
     )
  => (a -> b)
  -> f_a
  -> f_b
fmapBeamed = fmapHKT @Beamed' @f @a @b

hoistBeamed
  :: forall a f g f_a g_a.
     ( f_a ~$ Beamed' f a
     , g_a ~$ Beamed' g a
     )
  => (forall x. f x -> g x)
  -> f_a
  -> g_a
hoistBeamed = hoistHKT @Beamed' @f @g @a

transformBeamed
  :: forall a b f g f_a g_b.
     ( f_a ~$ Beamed' f a
     , g_b ~$ Beamed' g b
     )
  => (f a -> g b)
  -> f_a
  -> g_b
transformBeamed = transformHKT @Beamed' @f @g @a @b


traverseBeamed
  :: forall hkd f g t.
     ( Applicative t
     , TraversableHKD hkd Beamed' f g
     )
  => (forall x. f x -> t (g x))
  -> hkd f
  -> t (hkd g)
traverseBeamed = traverseHKD @hkd @Beamed' @f @g

mapBeamed
  :: forall hkd f g.
     ( FunctorHKD hkd Beamed' f g
     )
  => (forall x. f x -> g x)
  -> hkd f
  -> hkd g
mapBeamed = mapHKD @hkd @Beamed' @f @g


transformHKD_Beamed
  :: forall hkd f g f_hkd_f f_hkd_g g_hkd_g.
     ( Functor f
     , FunctorHKD hkd Beamed' f g
     , f_hkd_f ~$ Beamed' f (hkd f)
     , f_hkd_g ~$ Beamed' f (hkd g)
     , g_hkd_g ~$ Beamed' g (hkd g)
     )
  => (forall x. f x -> g x)
  -> f_hkd_f
  -> g_hkd_g
transformHKD_Beamed = transformHKD @hkd @Beamed' @Beamed' @f @g @f_hkd_f @f_hkd_g @g_hkd_g
