{-# OPTIONS --without-K #-}

module Groupoids.Ordinary.Ambient.Cosmos.Copower where

open import Groupoids.Basis
  hiding (_⊛_)
open import Groupoids.Ordinary.Ambient.Cosmos.Tensor.Coproduct.Indexed
open import Groupoids.Ordinary.Ambient.Universe.Boot

module ⊛ where
  _⊛_
    : ∀ {r}..{ℓ₀ ℓ₁}
    → (I : Set ℓ₀)
    → (A : 𝔘 r ℓ₁)
    → 𝔘 r _
  I ⊛ A = Σ.[ I ∋ _ ] A

open ⊛ public
  using (_⊛_)
