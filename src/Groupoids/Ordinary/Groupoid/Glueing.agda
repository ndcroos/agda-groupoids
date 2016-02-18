{-# OPTIONS --without-K #-}

module Groupoids.Ordinary.Groupoid.Glueing where

open import Groupoids.Basis
open import Groupoids.Ordinary.Ambient.Cosmos.Diagonal
open import Groupoids.Ordinary.Ambient.Cosmos.Unit.Terminal
open import Groupoids.Ordinary.Ambient.Morphism.Hom.Boot
open import Groupoids.Ordinary.Ambient.Universe
open import Groupoids.Ordinary.Groupoid.Comma

module Glueing where
  Glue
    : ∀ {r}..{ℓ₀ ℓ₁}
    → {A : 𝔘 r ℓ₀}
    → {V : 𝔘 r ℓ₁}
    → (Ψ : Hom₀ A V)
    → 𝔘 r _
  Glue {V = V} Ψ = ⇒₀.idn {A = V} ↓ Ψ
