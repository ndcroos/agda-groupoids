{-# OPTIONS --without-K #-}

module Groupoids.Ordinary.Construction.Opposite where

open import Groupoids.Common
open import Groupoids.Ordinary.Homomorphism.Boot
open import Groupoids.Ordinary.Universe.Boot

module Opposite where

  Op
    : ∀ {n r}..{ℓ}
    → (A : 𝔘 n r ℓ)
    → 𝔘 n r ℓ
  ● [ Op A ] = ● [ A ]
  ⇇ [ Op A ] a b = ⇇ [ A ] b a
  ↻ [ Op A ] = ↻ [ A ]
  seq₀ (Op A) = cmp₀ A
  inv₀ (Op A) = inv₀ A
  seq₀* (Op A) = cmp₀* A
  inv₀* (Op A) = inv₀* A
  ⊢idn₀-λ (Op A) = ⊢idn₀-ρ A
  ⊢idn₀-ρ (Op A) = ⊢idn₀-λ A
  ⊢seq₀-α (Op A) = ⊢cmp₀-α A
  ⊢inv₀-λ (Op A) = ⊢inv₀-ρ A
  ⊢inv₀-ρ (Op A) = ⊢inv₀-λ A
  idn₁ (Op A) = idn₁ A
  seq₁ (Op A) = seq₁ A
  inv₁ (Op A) = inv₁ A

open Opposite public
  using (Op)
