{-# OPTIONS --without-K #-}

module Groupoids.Core.Groupoid.Ordinary.Homomorphism where

import Groupoids.Core.Groupoid.Ordinary.Homomorphism.Boot
open import Groupoids.Common
open import Groupoids.Core.Groupoid.Ordinary.Construction.Core
open import Groupoids.Core.Groupoid.Ordinary.Universe.Boot

module ⇒₀ where
  open Groupoids.Core.Groupoid.Ordinary.Homomorphism.Boot.⇒₀ public
  open Groupoids.Core.Groupoid.Ordinary.Homomorphism.Boot public
    hiding (module ⇒₀)

  infix 1 _⇒₀_
  infix 1 _⇔₀_

  _⇒₀_
    : ∀ {n r}..{ℓ₀ ℓ₁}
    → (A : 𝔘 n r ℓ₀)
    → (B : 𝔘 n r ℓ₁)
    → 𝔘 1 r _
  ● [ A ⇒₀ B ] = Fun₀ A B
  ● (⇇ [ A ⇒₀ B ] F G) = Fun₁ F G
  ● (⇇ (⇇ [ A ⇒₀ B ] F G) α β) = T.⊔⇑ _ ((a : A ▸) → B ▸ 2 ⊢ ap₁₀ α a ↝ ap₁₀ β a)
  ⇇ (⇇ (⇇ [ A ⇒₀ B ] _ _) _ _) _ _ = 𝔊.𝟙↑
  ↻ (⇇ (⇇ [ A ⇒₀ B ] _ _) _ _) = *
  ↻ (⇇ [ A ⇒₀ B ] F G) {α} = ι λ a → ↻ (B ▸ 1 ⊩ ap₀₀ F a ↝ ap₀₀ G a)
  ↻ [ A ⇒₀ B ] = ⇒₁.idn
  idn₀ (A ⇒₀ B) = ⇒₁.idn
  seq₀ (A ⇒₀ B) = ⇒₁.seq
  inv₀ (A ⇒₀ B) α {≜} = ⇒₁.inv α {≜}
  seq₀* (A ⇒₀ B) (ι φ) (ι ψ) = ι λ a → seq₀* B (φ a) (ψ a)
  inv₀* (A ⇒₀ B) (ι ψ) {≜ = T.≡.idn} = ι λ a → inv₀* B (ψ a)
  ⊢λ₀ (A ⇒₀ B) = ι λ a → ⊢λ₀ B
  ⊢ρ₀ (A ⇒₀ B) = ι λ a → ⊢ρ₀ B
  ⊢α₀ (A ⇒₀ B) = ι λ a → ⊢α₀ B
  ⊢λ₀⁻¹ (A ⇒₀ B) {≜ = T.≡.idn} = ι λ a → ⊢λ₀⁻¹ B
  ⊢ρ₀⁻¹ (A ⇒₀ B) {≜ = T.≡.idn} = ι λ a → ⊢ρ₀⁻¹ B
  idn₁ (A ⇒₀ B) = ι λ a → idn₁ B
  seq₁ (A ⇒₀ B) (ι φ) (ι ψ) = ι λ a → seq₁ B (φ a) (ψ a)
  inv₁ (A ⇒₀ B) (ι φ) = ι λ a → inv₁ B (φ a)

  _⇔₀_
    : ∀ {n r}..{ℓ₀ ℓ₁}
    → (A : 𝔘 n r ℓ₀)
    → (B : 𝔘 n r ℓ₁)
    → 𝔘 1 0 _
  A ⇔₀ B = [ A ⇒₀ B ]/≅
open ⇒₀ public
  using (Fun₀)
  using (ap₀₀)
  using (ap₀₁)
  using (ap₀₂)

module ⇒₁ where
  open Groupoids.Core.Groupoid.Ordinary.Homomorphism.Boot.⇒₁ public
  open Groupoids.Core.Groupoid.Ordinary.Homomorphism.Boot public
    hiding (module ⇒₁)
open ⇒₁ public
  using (Fun₁)
  using (ap₁₀)
  using (ap₁₁)
