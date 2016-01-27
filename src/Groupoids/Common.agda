{-# OPTIONS --without-K #-}

module Groupoids.Common where

open import Globular.Common public
  hiding (_▸_)
open import Globular public

infix 0 ⊢_
infix 1 _↝_
infixr 3 _⊙_

pattern ⊢_ x = x
pattern 1+ n =     su (ℕ∞.ι n)
pattern 2+ n = 1+ (su (ℕ∞.ι n))

record Display : Set where
  no-eta-equality

_↝_ : Display
_↝_ = record {}

_⊙_ : Display
_⊙_ = record {}

module _ where
  open 𝔊
  open Gph
  {-# DISPLAY ● A = ⊢ A #-}
  {-# DISPLAY ⇇ A a b = a ↝ b #-}

module _ where
  open 𝔊
  open Map
  {-# DISPLAY ap* F = * F #-}
