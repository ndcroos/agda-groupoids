{-# OPTIONS --without-K #-}

module Groupoids.Groupoid where

open import Agda.Primitive
open import Groupoids.Ambient.Groupoid.Base public
import Groupoids.Ambient.Groupoid.Discrete
import Groupoids.Ambient.Groupoid.Map
import Groupoids.Ambient.Groupoid.Initial
import Groupoids.Ambient.Groupoid.Op
import Groupoids.Ambient.Groupoid.Tensor
import Groupoids.Ambient.Groupoid.Terminal
import Groupoids.Type as T

module ≡ where
  open import Groupoids.Ambient.Groupoid.Discrete public
module 𝟘 where
  open import Groupoids.Ambient.Groupoid.Initial public
module 𝟙 where
  open import Groupoids.Ambient.Groupoid.Terminal public
module Op where
  open import Groupoids.Ambient.Groupoid.Op public
module Map where
  open import Groupoids.Ambient.Groupoid.Map public
  open import Groupoids.Ambient.Groupoid.Map.Boot public
module Ten where
  open import Groupoids.Ambient.Groupoid.Tensor public
  open import Groupoids.Ambient.Groupoid.Tensor.Boot public

-
  : ∀ {d} ..{ℓᵒ ℓˢᵒ ℓˢʰ}
  → {A : t d ℓᵒ ℓˢᵒ ℓˢʰ}
  → A Map.⇒₀ᵗ A
- = Map.idn₀ᵗ T.𝟙.*
