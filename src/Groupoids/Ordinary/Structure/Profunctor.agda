{-# OPTIONS --without-K #-}

module Groupoids.Ordinary.Structure.Profunctor where

open import Groupoids.Basis
open import Groupoids.Ordinary.Groupoid.Opposite
open import Groupoids.Ordinary.Ambient.Cosmos.Tensor.Product
open import Groupoids.Ordinary.Ambient.Morphism.Hom
open import Groupoids.Ordinary.Ambient.Universe

module ⇏₀ where
  ¬Hom₀[_]
    : ∀ {n r}..{ℓ₀ ℓ₁ ℓ₂}
    → (V : 𝔘 n r ℓ₀)
    → (A : 𝔘 n r ℓ₁)
    → (B : 𝔘 n r ℓ₂)
    → Set _
  ¬Hom₀[ V ] A B = Hom₀ (Op[ B ] ⊗ A) V

  -- ¬Hom₀
  --   : ∀ ..{ℓ}{r}..{ℓ₀ ℓ₁}
  --   → (A : 𝔘 1 ℓ₀)
  --   → (B : 𝔘 1 ℓ₁)
  --   → Set _
  -- ¬Hom₀ {ℓ}{r} = ¬Hom₀[ «Std» r ℓ ]

open ⇏₀ public
  using (¬Hom₀[_])
  -- using (¬Hom₀)
