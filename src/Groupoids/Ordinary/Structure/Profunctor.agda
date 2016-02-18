{-# OPTIONS --without-K #-}

module Groupoids.Ordinary.Structure.Profunctor where

open import Groupoids.Basis
open import Groupoids.Ordinary.Groupoid.Opposite
open import Groupoids.Ordinary.Ambient.Cosmos.Tensor.Product
open import Groupoids.Ordinary.Ambient.Morphism.Hom
open import Groupoids.Ordinary.Ambient.Universe

GPro
  : ∀ {r}..{ℓ₀ ℓ₁ ℓ₂}
  → (V : 𝔘 r ℓ₀)
  → (A : 𝔘 r ℓ₁)
  → (B : 𝔘 r ℓ₂)
  → Set _
GPro V A B = Hom₀ (Op[ B ] ⊗ A) V

Pro
  : ∀ ..{ℓ}{r}..{ℓ₀ ℓ₁}
  → (A : 𝔘 1 ℓ₀)
  → (B : 𝔘 1 ℓ₁)
  → Set _
Pro {ℓ}{r} = GPro («Std» r ℓ)
