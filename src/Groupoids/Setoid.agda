{-# OPTIONS --without-K #-}

module Groupoids.Setoid where

open import Agda.Primitive
open import Groupoids.Ambient.Setoid.Base public
import Groupoids.Ambient.Setoid.Discrete
import Groupoids.Ambient.Setoid.Initial
import Groupoids.Ambient.Setoid.Map
import Groupoids.Ambient.Setoid.Op
import Groupoids.Ambient.Setoid.Tensor
import Groupoids.Ambient.Setoid.Terminal

module ≡ where
  open import Groupoids.Ambient.Setoid.Discrete public
module 𝟘 where
  open import Groupoids.Ambient.Setoid.Initial public
module 𝟙 where
  open import Groupoids.Ambient.Setoid.Terminal public
module Op where
  open import Groupoids.Ambient.Setoid.Op public
module Map where
  open import Groupoids.Ambient.Setoid.Map public
  open import Groupoids.Ambient.Setoid.Map.Boot public
module Ten where
  open import Groupoids.Ambient.Setoid.Tensor public
  open import Groupoids.Ambient.Setoid.Tensor.Boot public
