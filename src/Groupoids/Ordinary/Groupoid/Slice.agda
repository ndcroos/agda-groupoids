{-# OPTIONS --without-K #-}

module Groupoids.Ordinary.Groupoid.Slice where

open import Groupoids.Basis
open import Groupoids.Ordinary.Ambient.Cosmos.Diagonal
open import Groupoids.Ordinary.Ambient.Cosmos.Unit.Terminal
open import Groupoids.Ordinary.Ambient.Morphism.Hom.Boot
open import Groupoids.Ordinary.Ambient.Universe.Boot
open import Groupoids.Ordinary.Groupoid.Comma

module Slice where
  Slice
    : ∀ {n r}..{ℓ}
    → (A : 𝔘 n r ℓ)
    → (a : A ▸)
    → 𝔘 n r _
  Slice A a = ⇒₀.idn {A = A} ↓ Δ.ʲ[ 𝟙 ↦ a ]

  syntax Slice A a = A ↙ a
