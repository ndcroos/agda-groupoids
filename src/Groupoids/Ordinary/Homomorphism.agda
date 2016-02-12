{-# OPTIONS --without-K #-}

module Groupoids.Ordinary.Homomorphism where

import Groupoids.Ordinary.Homomorphism.Boot
open import Groupoids.Common
open import Groupoids.Ordinary.Construction.Core
open import Groupoids.Ordinary.Universe.Boot

module ⇒₀ where
  open Groupoids.Ordinary.Homomorphism.Boot.⇒₀ public
  open Groupoids.Ordinary.Homomorphism.Boot public
    hiding (module ⇒₀)

  infix 1 _⇒₀_
  infix 1 _⇔₀_

  _⇒₀_
    : ∀ {r}..{ℓ₀ ℓ₁}
    → (A : 𝔘 r ℓ₀)
    → (B : 𝔘 r ℓ₁)
    → 𝔘 r _
  ● [ A ⇒₀ B ] = Fun₀ A B
  ● (⇇ [ A ⇒₀ B ] F G) = Fun₁ F G
  ● (⇇ (⇇ [ A ⇒₀ B ] F G) α β) = T.⊔⇑ _ ((a : A ▸) → B ▸ 2 ⊢ ap₁₀ α a ↝ ap₁₀ β a)
  ⇇ (⇇ (⇇ [ A ⇒₀ B ] _ _) _ _) _ _ = 𝔊.𝟙↑
  ↻ (⇇ (⇇ [ A ⇒₀ B ] _ _) _ _) = *
  ↻ (⇇ [ A ⇒₀ B ] F G) {α} = ι λ a → ↻ (B ▸ 1 ⊩ ap₀₀ F a ↝ ap₀₀ G a)
  ↻ [ A ⇒₀ B ] = ⇒₁.idn
  seq₀ (A ⇒₀ B) = ⇒₁.seq
  inv₀ (A ⇒₀ B) α {≜} = ⇒₁.inv α {≜}
  seq₀* (A ⇒₀ B) (ι φ) (ι ψ) = ι λ a → seq₀* B (φ a) (ψ a)
  inv₀* (A ⇒₀ B) (ι ψ) {≜ = T.≡.idn} = ι λ a → inv₀* B (ψ a)
  ⊢idn₀-λ (A ⇒₀ B) = ι λ a → ⊢idn₀-λ B
  ⊢idn₀-ρ (A ⇒₀ B) = ι λ a → ⊢idn₀-ρ B
  ⊢seq₀-α (A ⇒₀ B) = ι λ a → ⊢seq₀-α B
  ⊢inv₀-λ (A ⇒₀ B) {≜ = T.≡.idn} = ι λ a → ⊢inv₀-λ B
  ⊢inv₀-ρ (A ⇒₀ B) {≜ = T.≡.idn} = ι λ a → ⊢inv₀-ρ B
  idn₁ (A ⇒₀ B) = ι λ a → idn₁ B
  seq₁ (A ⇒₀ B) (ι φ) (ι ψ) = ι λ a → seq₁ B (φ a) (ψ a)
  inv₁ (A ⇒₀ B) (ι φ) = ι λ a → inv₁ B (φ a)

  _⇔₀_
    : ∀ {r}..{ℓ₀ ℓ₁}
    → (A : 𝔘 r ℓ₀)
    → (B : 𝔘 r ℓ₁)
    → 𝔘 0 _
  A ⇔₀ B = [ A ⇒₀ B ]/≅
open ⇒₀ public
  using (Fun₀)
  using (_⇒₀_)
  using (ap₀₀)
  using (ap₀₁)
  using (ap₀₂)

module ⇒₁ where
  open Groupoids.Ordinary.Homomorphism.Boot.⇒₁ public
  open Groupoids.Ordinary.Homomorphism.Boot public
    hiding (module ⇒₁)
open ⇒₁ public
  using (Fun₁)
  using (ap₁₀)
  using (ap₁₁)
