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

-- | Based on 'Data.Generic.HKD.Named' from package 'higgledy'
--   by Tom Harding ((c) Tom Harding, 2019, MIT)

module HigherKinded.HKD.Build
  ( Build (..)
  , Arg (..)
  , Name (..)
  ) where

import Data.Generics.Product.Internal.Subtype (GUpcast (..))
import Data.Kind
import GHC.Generics
import GHC.OverloadedLabels
import GHC.TypeLits

import HigherKinded.HKD.Base



class Build (hkd :: Type) (k :: Type) | hkd -> k, k -> hkd where
  build :: k



instance
    ( BuildHKD_ structure hkt f k
    , list ~ Rearrange (HKD_ structure hkt f)
    )
  =>
    Build (HKD structure hkt f) k
  where
    build = gbuild @_ @structure @hkt @f (to . gupcast @list @(HKD_ structure hkt f))

class
    ( GenericHKD_ structure hkt f
    --
    , GUpcast (Rearrange (HKD_ structure hkt f)) (HKD_ structure hkt f)
    , GBuild (Rearrange (HKD_ structure hkt f)) structure hkt f k
    )
  => BuildHKD_ structure hkt f k

instance
    ( GenericHKD_ structure hkt f
    --
    , GUpcast (Rearrange (HKD_ structure hkt f)) (HKD_ structure hkt f)
    , GBuild (Rearrange (HKD_ structure hkt f)) structure hkt f k
    )
  => BuildHKD_ structure hkt f k



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

