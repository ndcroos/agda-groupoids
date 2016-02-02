{-# OPTIONS --without-K #-}

module Groupoids.Ordinary.Monoidal.Tensor.Product where

open import Groupoids.Common
open import Groupoids.Ordinary.Universe.Boot

module ⊗ where
  infix 0 _⊗_

  _⊗_
    : ∀ {r}..{ℓ₀ ℓ₁}
    → (A : 𝔘 r ℓ₀)
    → (B : 𝔘 r ℓ₁)
    → 𝔘 r _
  [ A ⊗ B ] = [ A ] 𝔊.⊗ [ B ]
  seq₀ (A ⊗ B) (f₀ , g₀) (f₁ , g₁) = seq₀ A f₀ f₁ , seq₀ B g₀ g₁
  inv₀ (A ⊗ B) (f , g) {≜} = inv₀ A f {≜} , inv₀ B g {≜}
  seq₀* (A ⊗ B) (α₀ , β₀)(α₁ , β₁) = seq₀* A α₀ α₁ , seq₀* B β₀ β₁
  inv₀* (A ⊗ B) (α , β) {≜} = inv₀* A α {≜} , inv₀* B β {≜}
  ⊢idn₀-λ (A ⊗ B) = ⊢idn₀-λ A , ⊢idn₀-λ B
  ⊢idn₀-ρ (A ⊗ B) = ⊢idn₀-ρ A , ⊢idn₀-ρ B
  ⊢seq₀-α (A ⊗ B) = ⊢seq₀-α A , ⊢seq₀-α B
  ⊢inv₀-λ (A ⊗ B) {≜ = ≜} = ⊢inv₀-λ A {≜ = ≜} , ⊢inv₀-λ B {≜ = ≜}
  ⊢inv₀-ρ (A ⊗ B) {≜ = ≜} = ⊢inv₀-ρ A {≜ = ≜} , ⊢inv₀-ρ B {≜ = ≜}
  idn₁ (A ⊗ B) = idn₁ A , idn₁ B
  seq₁ (A ⊗ B) (α₀ , β₀)(α₁ , β₁) = seq₁ A α₀ α₁ , seq₁ B β₀ β₁
  inv₁ (A ⊗ B) (α , β) = inv₁ A α , inv₁ B β

open ⊗ public
  using (_⊗_)
