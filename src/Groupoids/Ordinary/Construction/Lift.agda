{-# OPTIONS --without-K #-}

module Groupoids.Ordinary.Construction.Lift where

open import Groupoids.Common
open import Groupoids.Ordinary.Universe.Boot

module ⊔↑ where
  ⊔↑
    : ∀ {r}..{ℓ₀ ℓ₁}
    → (A : 𝔘 r ℓ₀)
    → 𝔘 r (ℓ₀ ⊔ ℓ₁)
  [ ⊔↑ {ℓ₁ = ℓ₁} A ] =
    𝔊.⊔↑ {ℓ₁ = ℓ₁} [ A ]
  idn₀ (⊔↑ A) {ι a} =
    ι (idn₀ A)
  seq₀ (⊔↑ A) (ι f) (ι g) =
    ι (seq₀ A f g)
  inv₀ (⊔↑ A) (ι f) {≜} =
    ι (inv₀ A f {≜ = ≜})
  seq₀* (⊔↑ A) (ι α)(ι β) =
    ι (seq₀* A α β)
  inv₀* (⊔↑ A) (ι α) {≜} =
    ι (inv₀* A α {≜})
  ⊢idn₀-λ (⊔↑ A) =
    ι (⊢idn₀-λ A)
  ⊢idn₀-ρ (⊔↑ A) =
    ι (⊢idn₀-ρ A)
  ⊢seq₀-α (⊔↑ A) =
    ι (⊢seq₀-α A)
  ⊢inv₀-λ (⊔↑ A) {≜ = ≜} =
    ι (⊢inv₀-λ A {≜ = ≜})
  ⊢inv₀-ρ (⊔↑ A) {≜ = ≜} =
    ι (⊢inv₀-ρ A {≜ = ≜})
  idn₁ (⊔↑ A) =
    ι (idn₁ A)
  seq₁ (⊔↑ A) (ι α) (ι β) =
    ι (seq₁ A α β)
  inv₁ (⊔↑ A) (ι α) =
    ι (inv₁ A α)

open ⊔↑ public
  using (⊔↑)
