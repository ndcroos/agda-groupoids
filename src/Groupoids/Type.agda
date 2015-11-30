{-# OPTIONS --without-K #-}

module Groupoids.Type where

open import Agda.Primitive
open import Groupoids.Ambient.Type.Base public
import Groupoids.Ambient.Type.Discrete
import Groupoids.Ambient.Type.Map
import Groupoids.Ambient.Type.Initial
import Groupoids.Ambient.Type.Op
import Groupoids.Ambient.Type.Tensor
import Groupoids.Ambient.Type.Terminal

module ≡ where
  open import Groupoids.Ambient.Type.Discrete public
    renaming (t to _t_)
module 𝟘 where
  open import Groupoids.Ambient.Type.Initial public
module 𝟙 where
  open import Groupoids.Ambient.Type.Terminal public
module Op where
  open import Groupoids.Ambient.Type.Op public
module Map where
  open import Groupoids.Ambient.Type.Map public
  open import Groupoids.Ambient.Type.Map.Boot public
module Ten where
  open import Groupoids.Ambient.Type.Tensor public
  open import Groupoids.Ambient.Type.Tensor.Boot public

open Groupoids.Ambient.Type.Tensor public
  using (_,_)
open Groupoids.Ambient.Type.Terminal public
  using (*)
