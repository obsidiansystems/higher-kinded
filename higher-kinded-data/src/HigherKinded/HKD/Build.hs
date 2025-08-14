{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Based on 'Data.Generic.HKD.Named from package 'higgledy'
--   by Tom Harding ((c) Tom Harding, 2019, MIT)

module HigherKinded.HKD.Build
  ( Build (..)
  , Arg (..)
  , Name (..)
  ) where

import Data.Functor.Contravariant (Contravariant (..))
import Data.Generics.Product.Internal.Subtype (GUpcast (..))
import Data.Kind
import GHC.Generics
import GHC.OverloadedLabels
import GHC.TypeLits

import HigherKinded.HKD.Types (HKD, HKD_)



-- | With many HKD applications, we're working with types like 'Maybe' where it
-- makes sense for us to start with 'mempty' and add values in as we go.
--
-- This isn't always the case, however: if all the component parts of our type
-- are gathered using some 'IO' action, we'd like to construct something like
-- @HKD MyType IO@, and @IO a@ isn't a 'Monoid' for all types @a@. When this
-- happens, we need to pass in our parameters /when/ we build our structure.
--
-- The 'build' function lets us construct our type by passing explicit values
-- for each parameter:
--
-- >>> :set -XDeriveGeneric -XTypeApplications
--
-- >>> :{
-- data User
--   = User { name :: String, age :: Int, likesDogs :: Bool }
--   deriving Generic
-- :}
--
-- >>> :{
-- test :: _
-- test = build @User
-- :}
-- ...
-- ... Found type wildcard ...
-- ... standing for ...f [Char] -> f Int -> f Bool -> HKD User f...
-- ...
--
-- Once we call the 'build' function, and indicate the type we want to build,
-- we are free to pick whichever @f@ we like and get to work!
class Build (hkd :: Type) (k :: Type) | hkd -> k, k -> hkd where
  build :: k

instance
    ( Contravariant (HKD_ structure hkt f)
    , Functor (HKD_ structure hkt f)
    --
    , list ~ Rearrange (HKD_ structure hkt f)
    , GUpcast list (HKD_ structure hkt f)
    , GBuild list structure hkt f k
    )
  =>
    Build (HKD structure hkt f) k
  where
    build = gbuild @_ @structure @hkt @f (to . gupcast @list @(HKD_ structure hkt f))


class GBuild (rep :: Type -> Type) (structure :: Type) (hkt :: ((Type -> Type) -> Type -> Type)) (f :: Type -> Type) (k :: Type)
    | rep structure hkt f -> k, k -> structure hkt f where
  gbuild :: (forall p. rep p -> HKD structure hkt f) -> k

instance
    GBuild inner structure hkt f k
  =>
    GBuild (D1 meta inner) structure hkt f k
  where
    gbuild rebuild = gbuild (rebuild . M1)

instance
    GBuild inner structure hkt f k
  =>
    GBuild (C1 meta inner) structure hkt f k
  where
    gbuild rebuild = gbuild (rebuild . M1)

instance
    ( rec0 ~ (Rec0 inner)
    , k ~ (Arg name inner -> HKD structure hkt f)
    , meta ~ 'MetaSel ('Just name) i d c
    )
  =>
    GBuild (S1 meta rec0) structure hkt f k
  where
    gbuild fill = \case
      (Arg inner) -> fill (M1 (K1 inner))
      ((Name :: Name name) :! inner) -> fill (M1 (K1 inner))

instance
    ( GBuild right structure hkt f k'
    , rec0 ~ Rec0 x
    , left ~ S1 ('MetaSel ('Just name) i d c) rec0
    , k ~ (Arg name x -> k')
    )
  =>
    GBuild (left :*: right) structure hkt f k
  where
    gbuild fill = \case
      (Arg left) -> gbuild \right -> fill (M1 (K1 left) :*: right)
      ((Name :: Name name) :! left) -> gbuild \right -> fill (M1 (K1 left) :*: right)



data Arg name a where
  (:!) :: Name name -> a -> Arg name a
  Arg :: a -> Arg name a

data Name (name :: Symbol) = Name

instance name ~ name' => IsLabel name' (Name name) where
  fromLabel = Name



type family Rearrange (i :: Type -> Type) :: Type -> Type where
  Rearrange (S1       m inner) = S1       m (Rearrange inner)
  Rearrange (M1 index m inner) = M1 index m (Rearrange inner)
  Rearrange (left :*: right)   = Append (Rearrange left) (Rearrange right)
  Rearrange (Rec0 inner)       = Rec0 inner

type family Append (xs :: Type -> Type) (ys :: Type -> Type) :: Type -> Type where
  Append (S1 meta head) tail    = S1 meta head :*: tail
  Append (left :*: right) other = left :*: Append right other

