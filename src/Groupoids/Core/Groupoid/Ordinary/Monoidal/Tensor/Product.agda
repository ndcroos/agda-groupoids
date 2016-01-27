{-# OPTIONS --without-K #-}

module Groupoids.Core.Groupoid.Ordinary.Monoidal.Tensor.Product where

open import Groupoids.Common
open import Groupoids.Core.Groupoid.Ordinary.Universe.Boot

module ⊗ where
  infix 0 _⊗_

  _⊗_
    : ∀ {n r}..{ℓ₀ ℓ₁}
    → (A : 𝔘 n r ℓ₀)
    → (B : 𝔘 n r ℓ₁)
    → 𝔘 n r _
  [ A ⊗ B ] = [ A ] 𝔊.⊗ [ B ]
  idn₀ (A ⊗ B) {a , b} = idn₀ A , idn₀ B
  seq₀ (A ⊗ B) (f₀ , g₀) (f₁ , g₁) = seq₀ A f₀ f₁ , seq₀ B g₀ g₁
  inv₀ (A ⊗ B) (f , g) {≜} = inv₀ A f {≜} , inv₀ B g {≜}
  seq₀* (A ⊗ B) (α₀ , β₀)(α₁ , β₁) = seq₀* A α₀ α₁ , seq₀* B β₀ β₁
  inv₀* (A ⊗ B) (α , β) {≜} = inv₀* A α {≜} , inv₀* B β {≜}
  ⊢λ₀ (A ⊗ B) = ⊢λ₀ A , ⊢λ₀ B
  ⊢ρ₀ (A ⊗ B) = ⊢ρ₀ A , ⊢ρ₀ B
  ⊢α₀ (A ⊗ B) = ⊢α₀ A , ⊢α₀ B
  ⊢λ₀⁻¹ (A ⊗ B) {≜ = ≜} = ⊢λ₀⁻¹ A {≜ = ≜} , ⊢λ₀⁻¹ B {≜ = ≜}
  ⊢ρ₀⁻¹ (A ⊗ B) {≜ = ≜} = ⊢ρ₀⁻¹ A {≜ = ≜} , ⊢ρ₀⁻¹ B {≜ = ≜}
  idn₁ (A ⊗ B) = idn₁ A , idn₁ B
  seq₁ (A ⊗ B) (α₀ , β₀)(α₁ , β₁) = seq₁ A α₀ α₁ , seq₁ B β₀ β₁
  inv₁ (A ⊗ B) (α , β) = inv₁ A α , inv₁ B β

open ⊗ public
  using (_⊗_)
