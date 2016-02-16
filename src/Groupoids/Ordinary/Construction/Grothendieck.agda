{-# OPTIONS --without-K #-}

module Groupoids.Ordinary.Construction.Grothendieck where

open import Groupoids.Common
open import Groupoids.Ordinary.Construction.Comma
open import Groupoids.Ordinary.Morphism.Hom.Boot
open import Groupoids.Ordinary.Monoidal.Diagonal
open import Groupoids.Ordinary.Monoidal.Unit.Terminal
open import Groupoids.Ordinary.Universe

module Grothendieck where
  ∮
    : ∀ ..{ℓ₀ ℓ₁}
    → {I : Cat ℓ₀}
    → (Ψ : Fun₀ I («Cat» 1 ℓ₁))
    → Cat (ℓ₀ ⊔ lsuc ℓ₁)
  ∮ {I = I} Ψ = Δ.ʲ[ 𝟙 ↦ 𝟙↑ ] ↓ Ψ
