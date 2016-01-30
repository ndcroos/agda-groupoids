{-# OPTIONS --without-K #-}

module Groupoids.Ordinary.Construction.Slice where

open import Groupoids.Common
open import Groupoids.Ordinary.Construction.Comma
open import Groupoids.Ordinary.Homomorphism.Boot
open import Groupoids.Ordinary.Monoidal.Diagonal
open import Groupoids.Ordinary.Monoidal.Unit.Terminal
open import Groupoids.Ordinary.Universe.Boot

module Slice where
  Slice
    : ∀ {n r}..{ℓ}
    → (A : 𝔘 n r ℓ)
    → (a : A ▸)
    → 𝔘 n r _
  Slice A a = ⇒₀.idn {A = A} ↓ Δ.ʲ[ 𝟙 ↦ a ]

  syntax Slice A a = A ↙ a
