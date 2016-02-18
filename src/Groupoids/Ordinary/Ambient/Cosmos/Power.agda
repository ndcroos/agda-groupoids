{-# OPTIONS --without-K #-}

module Groupoids.Ordinary.Ambient.Cosmos.Power where

open import Groupoids.Basis
open import Groupoids.Ordinary.Ambient.Cosmos.Tensor.Product.Indexed
open import Groupoids.Ordinary.Ambient.Universe.Boot

module ⋔ where
  _⋔_
    : ∀ {r}..{ℓ₀ ℓ₁}
    → (I : Set ℓ₀)
    → (A : 𝔘 r ℓ₁)
    → 𝔘 r _
  I ⋔ A = Π.[ I ∋ _ ] A

open ⋔ public
  using (_⋔_)
