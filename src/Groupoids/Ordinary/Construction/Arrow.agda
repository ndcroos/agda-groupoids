{-# OPTIONS --without-K #-}

module Groupoids.Ordinary.Construction.Arrow where

open import Groupoids.Common
open import Groupoids.Ordinary.Construction.Comma
open import Groupoids.Ordinary.Homomorphism.Boot
open import Groupoids.Ordinary.Universe.Boot

module Arrow where
  _⃗²
    : ∀ {n r}..{ℓ}
    → (A : 𝔘 n r ℓ)
    → 𝔘 n r _
  A ⃗² = ⇒₀.idn {A = A} ↓ ⇒₀.idn {A = A}
