{-# OPTIONS --without-K #-}

module Groupoids.Ordinary.Groupoid.Grothendieck where

open import Groupoids.Basis
open import Groupoids.Ordinary.Ambient.Cosmos.Diagonal
open import Groupoids.Ordinary.Ambient.Cosmos.Unit.Terminal
open import Groupoids.Ordinary.Ambient.Morphism.Hom.Boot
open import Groupoids.Ordinary.Ambient.Universe
open import Groupoids.Ordinary.Groupoid.Comma

module Grothendieck where
  ∮
    : ∀ ..{ℓ₀ ℓ₁}
    → {I : Cat ℓ₀}
    → (Ψ : Hom₀ I («Cat» 1 ℓ₁))
    → Cat (ℓ₀ ⊔ lsuc ℓ₁)
  ∮ {I = I} Ψ = Δ.ʲ[ 𝟙 ↦ 𝟙↑ ] ↓ Ψ
