{-# OPTIONS --without-K #-}

module Groupoids.Ordinary.Structure.Wedge where

open import Groupoids.Basis
open import Groupoids.Ordinary.Ambient.Cosmos.Diagonal
open import Groupoids.Ordinary.Ambient.Universe.Boot
open import Groupoids.Ordinary.Structure.Dinatural
open import Groupoids.Ordinary.Structure.Profunctor

¬Δ
  : ∀ {r}..{ℓ₀ ℓ₁}
  → {A : 𝔘 r ℓ₀}
  → {V : 𝔘 r ℓ₁}
  → (F : ¬Hom₀[ V ] A A)
  → (v : V ▸)
  → Set _
¬Δ F v = ¬Hom₁ Δ.ʲ[ v ] F

¬∇
  : ∀ {r}..{ℓ₀ ℓ₁}
  → {A : 𝔘 r ℓ₀}
  → {V : 𝔘 r ℓ₁}
  → (F : ¬Hom₀[ V ] A A)
  → (v : V ▸)
  → Set _
¬∇ F v = ¬Hom₁ F Δ.ʲ[ v ]
