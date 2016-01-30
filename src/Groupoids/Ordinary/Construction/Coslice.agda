{-# OPTIONS --without-K #-}

module Groupoids.Ordinary.Construction.Coslice where

open import Groupoids.Common
open import Groupoids.Ordinary.Construction.Comma
open import Groupoids.Ordinary.Homomorphism.Boot
open import Groupoids.Ordinary.Monoidal.Diagonal
open import Groupoids.Ordinary.Monoidal.Unit.Terminal
open import Groupoids.Ordinary.Universe.Boot

module Coslice where
  Coslice
    : ∀ {n r}..{ℓ}
    → (A : 𝔘 n r ℓ)
    → (a : A ▸)
    → 𝔘 n r _
  Coslice A a = Δ.ʲ[ 𝟙 ↦ a ] ↓ ⇒₀.idn {A = A}

  syntax Coslice A a = a ↘ A
