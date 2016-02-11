{-# OPTIONS --without-K #-}

module Groupoids.Ordinary.Construction.Arrow where

open import Groupoids.Common
open import Groupoids.Ordinary.Construction.Comma
open import Groupoids.Ordinary.Homomorphism.Boot
open import Groupoids.Ordinary.Universe.Boot

module Arrow where
  _↗²
    : ∀ {r}..{ℓ}
    → (A : 𝔘 r ℓ)
    → 𝔘 r _
  A ↗² = ⇒₀.idn {A = A} ↓ ⇒₀.idn {A = A}
