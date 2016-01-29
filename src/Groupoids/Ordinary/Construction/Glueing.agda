{-# OPTIONS --without-K #-}

module Groupoids.Ordinary.Construction.Glueing where

open import Groupoids.Common
open import Groupoids.Ordinary.Construction.Comma
open import Groupoids.Ordinary.Homomorphism.Boot
open import Groupoids.Ordinary.Monoidal.Diagonal
open import Groupoids.Ordinary.Monoidal.Unit.Terminal
open import Groupoids.Ordinary.Universe

module Glueing where
  Glue
    : ∀ {n r}..{ℓ₀ ℓ₁}
    → {A : 𝔘 n r ℓ₀}
    → {V : 𝔘 n r ℓ₁}
    → (Ψ : Fun₀ A V)
    → 𝔘 n r _
  Glue {V = V} Ψ = ⇒₀.idn {A = V} ↓ Ψ
