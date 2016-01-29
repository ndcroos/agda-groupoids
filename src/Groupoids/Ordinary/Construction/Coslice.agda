{-# OPTIONS --without-K #-}

module Groupoids.Ordinary.Construction.Coslice where

open import Groupoids.Common
open import Groupoids.Ordinary.Construction.Comma
open import Groupoids.Ordinary.Homomorphism.Boot
open import Groupoids.Ordinary.Monoidal.Diagonal
open import Groupoids.Ordinary.Monoidal.Unit.Terminal
open import Groupoids.Ordinary.Universe.Boot

module Coslice where
  coslice
    : ∀ {n r}..{ℓ}
    → (A : 𝔘 n r ℓ)
    → (a : A ▸)
    → 𝔘 n r _
  coslice A a = Δ.ʲ[ 𝟙 ↦ a ] ↓ ⇒₀.idn {A = A}
