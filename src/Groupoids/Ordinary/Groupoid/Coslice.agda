{-# OPTIONS --without-K #-}

module Groupoids.Ordinary.Groupoid.Coslice where

open import Groupoids.Basis
open import Groupoids.Ordinary.Ambient.Cosmos.Diagonal
open import Groupoids.Ordinary.Ambient.Cosmos.Unit.Terminal
open import Groupoids.Ordinary.Ambient.Morphism.Hom.Boot
open import Groupoids.Ordinary.Ambient.Universe.Boot
open import Groupoids.Ordinary.Groupoid.Comma

module Coslice where
  Coslice
    : ∀ {n r}..{ℓ}
    → (A : 𝔘 n r ℓ)
    → (a : A ▸)
    → 𝔘 n r _
  Coslice A a = Δ.ʲ[ 𝟙 ↦ a ] ↓ ⇒₀.idn {A = A}

  syntax Coslice A a = a ↘ A
