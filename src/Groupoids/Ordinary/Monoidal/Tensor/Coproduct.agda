{-# OPTIONS --without-K #-}

module Groupoids.Ordinary.Monoidal.Tensor.Coproduct where

open import Groupoids.Common
open import Groupoids.Ordinary.Universe.Boot

module ⊕ where
  infix 0 _⊕_

  _⊕_
    : ∀ {n r}..{ℓ₀ ℓ₁}
    → (A : 𝔘 n r ℓ₀)
    → (B : 𝔘 n r ℓ₁)
    → 𝔘 n r _
  [ A ⊕ B ] = [ A ] 𝔊.⊕ [ B ]
  seq₀ (A ⊕ B) {T.⊕.inl a₀}{T.⊕.inl a₁}{T.⊕.inl a₂} (ι f) (ι g) =
    ι (seq₀ A f g)
  seq₀ (A ⊕ B) {T.⊕.inl a₀}{T.⊕.inl a₁}{T.⊕.inr b₂} f  ()
  seq₀ (A ⊕ B) {T.⊕.inl a₀}{T.⊕.inr b₁}{T.⊕.inl a₂} () ()
  seq₀ (A ⊕ B) {T.⊕.inl a₀}{T.⊕.inr b₁}{T.⊕.inr b₂} () g
  seq₀ (A ⊕ B) {T.⊕.inr b₀}{T.⊕.inl a₁}{T.⊕.inl a₂} () g
  seq₀ (A ⊕ B) {T.⊕.inr b₀}{T.⊕.inl a₁}{T.⊕.inr b₂} () ()
  seq₀ (A ⊕ B) {T.⊕.inr b₀}{T.⊕.inr b₁}{T.⊕.inl a₂} f  ()
  seq₀ (A ⊕ B) {T.⊕.inr b₀}{T.⊕.inr b₁}{T.⊕.inr b₂} (ι f) (ι g) =
    ι (seq₀ B f g)
  inv₀ (A ⊕ B) {T.⊕.inl a₀}{T.⊕.inl a₁} (ι f) {≜} =
    ι (inv₀ A f {≜})
  inv₀ (A ⊕ B) {T.⊕.inl a₀}{T.⊕.inr b₁} ()
  inv₀ (A ⊕ B) {T.⊕.inr b₀}{T.⊕.inl a₁} ()
  inv₀ (A ⊕ B) {T.⊕.inr b₀}{T.⊕.inr b₁} (ι f) {≜} =
    ι (inv₀ B f {≜})
  seq₀* (A ⊕ B) {T.⊕.inl a₀}{T.⊕.inl a₁}{T.⊕.inl a₂}{f₀}{f₁}{g₀}{g₁} (ι α₀) (ι α₁) =
    ι (seq₀* A α₀ α₁)
  seq₀* (A ⊕ B) {T.⊕.inl a₀}{T.⊕.inl a₁}{T.⊕.inr b₂}{f₀}{f₁}{()}{()}
  seq₀* (A ⊕ B) {T.⊕.inl a₀}{T.⊕.inr b₁}{T.⊕.inl a₂}{()}{()}{()}{()}
  seq₀* (A ⊕ B) {T.⊕.inl a₀}{T.⊕.inr b₁}{T.⊕.inr b₂}{()}{()}{g₀}{g₁}
  seq₀* (A ⊕ B) {T.⊕.inr b₀}{T.⊕.inl a₁}{T.⊕.inl a₂}{()}{()}{g₀}{g₁}
  seq₀* (A ⊕ B) {T.⊕.inr b₀}{T.⊕.inl a₁}{T.⊕.inr b₂}{()}{()}{()}{()}
  seq₀* (A ⊕ B) {T.⊕.inr b₀}{T.⊕.inr b₁}{T.⊕.inl a₂}{f₀}{f₁}{()}{()}
  seq₀* (A ⊕ B) {T.⊕.inr b₀}{T.⊕.inr b₁}{T.⊕.inr b₂}{f₀}{f₁}{g₀}{g₁} (ι β₀) (ι β₁) =
    ι (seq₀* B β₀ β₁)
  inv₀* (A ⊕ B) {T.⊕.inl a₀}{T.⊕.inl a₁} (ι α) {≜} =
    ι (inv₀* A α {≜})
  inv₀* (A ⊕ B) {T.⊕.inl a₀}{T.⊕.inr b₁}{()}{()}
  inv₀* (A ⊕ B) {T.⊕.inr b₀}{T.⊕.inl a₁}{()}{()}
  inv₀* (A ⊕ B) {T.⊕.inr b₀}{T.⊕.inr b₁} (ι β) {≜} =
    ι (inv₀* B β {≜})
  ⊢λ₀ (A ⊕ B) {T.⊕.inl a₀}{T.⊕.inl a₁} =
    ι (⊢λ₀ A)
  ⊢λ₀ (A ⊕ B) {T.⊕.inl a₀}{T.⊕.inr b₁}{()}
  ⊢λ₀ (A ⊕ B) {T.⊕.inr b₀}{T.⊕.inl a₁}{()}
  ⊢λ₀ (A ⊕ B) {T.⊕.inr b₀}{T.⊕.inr b₁} =
    ι (⊢λ₀ B)
  ⊢ρ₀ (A ⊕ B) {T.⊕.inl a₀}{T.⊕.inl a₁} =
    ι (⊢ρ₀ A)
  ⊢ρ₀ (A ⊕ B) {T.⊕.inl a₀}{T.⊕.inr b₁}{()}
  ⊢ρ₀ (A ⊕ B) {T.⊕.inr b₀}{T.⊕.inl a₁}{()}
  ⊢ρ₀ (A ⊕ B) {T.⊕.inr b₀}{T.⊕.inr b₁} =
    ι (⊢ρ₀ B)
  ⊢α₀ (A ⊕ B) {T.⊕.inl a₀}{T.⊕.inl a₁}{T.⊕.inl a₂}{T.⊕.inl a₃}{f}{g}{h} =
    ι (⊢α₀ A)
  ⊢α₀ (A ⊕ B) {T.⊕.inl a₀}{T.⊕.inl a₁}{T.⊕.inl a₂}{T.⊕.inr b₃}{f}{g}{()}
  ⊢α₀ (A ⊕ B) {T.⊕.inl a₀}{T.⊕.inl a₁}{T.⊕.inr b₂}{T.⊕.inl a₃}{f}{()}{()}
  ⊢α₀ (A ⊕ B) {T.⊕.inl a₀}{T.⊕.inl a₁}{T.⊕.inr b₂}{T.⊕.inr b₃}{f}{()}{h}
  ⊢α₀ (A ⊕ B) {T.⊕.inl a₀}{T.⊕.inr b₁}{T.⊕.inl a₂}{T.⊕.inl a₃}{()}{()}{h}
  ⊢α₀ (A ⊕ B) {T.⊕.inl a₀}{T.⊕.inr b₁}{T.⊕.inl a₂}{T.⊕.inr b₃}{()}{()}{()}
  ⊢α₀ (A ⊕ B) {T.⊕.inl a₀}{T.⊕.inr b₁}{T.⊕.inr b₂}{T.⊕.inl a₃}{()}{g}{()}
  ⊢α₀ (A ⊕ B) {T.⊕.inl a₀}{T.⊕.inr b₁}{T.⊕.inr b₂}{T.⊕.inr b₃}{()}{g}{h}
  ⊢α₀ (A ⊕ B) {T.⊕.inr b₀}{T.⊕.inl a₁}{T.⊕.inl a₂}{T.⊕.inl a₃}{()}{g}{h}
  ⊢α₀ (A ⊕ B) {T.⊕.inr b₀}{T.⊕.inl a₁}{T.⊕.inl a₂}{T.⊕.inr b₃}{()}{g}{()}
  ⊢α₀ (A ⊕ B) {T.⊕.inr b₀}{T.⊕.inl a₁}{T.⊕.inr b₂}{T.⊕.inl a₃}{()}{()}{()}
  ⊢α₀ (A ⊕ B) {T.⊕.inr b₀}{T.⊕.inl a₁}{T.⊕.inr b₂}{T.⊕.inr b₃}{()}{()}{h}
  ⊢α₀ (A ⊕ B) {T.⊕.inr b₀}{T.⊕.inr b₁}{T.⊕.inl a₂}{T.⊕.inl a₃}{f}{()}{h}
  ⊢α₀ (A ⊕ B) {T.⊕.inr b₀}{T.⊕.inr b₁}{T.⊕.inl a₂}{T.⊕.inr b₃}{f}{()}{()}
  ⊢α₀ (A ⊕ B) {T.⊕.inr b₀}{T.⊕.inr b₁}{T.⊕.inr b₂}{T.⊕.inl a₃}{f}{g}{()}
  ⊢α₀ (A ⊕ B) {T.⊕.inr b₀}{T.⊕.inr b₁}{T.⊕.inr b₂}{T.⊕.inr b₃}{f}{g}{h} =
    ι (⊢α₀ B)
  ⊢λ₀⁻¹ (A ⊕ B) {T.⊕.inl a₀}{T.⊕.inl a₁}{≜ = ≜} =
    ι (⊢λ₀⁻¹ A)
  ⊢λ₀⁻¹ (A ⊕ B) {T.⊕.inl a₀}{T.⊕.inr b₁}{()}
  ⊢λ₀⁻¹ (A ⊕ B) {T.⊕.inr b₀}{T.⊕.inl a₁}{()}
  ⊢λ₀⁻¹ (A ⊕ B) {T.⊕.inr b₀}{T.⊕.inr b₁}{≜ = ≜} =
    ι (⊢λ₀⁻¹ B)
  ⊢ρ₀⁻¹ (A ⊕ B) {T.⊕.inl a₀}{T.⊕.inl a₁}{≜ = ≜} =
    ι (⊢ρ₀⁻¹ A)
  ⊢ρ₀⁻¹ (A ⊕ B) {T.⊕.inl a₀}{T.⊕.inr b₁}{()}
  ⊢ρ₀⁻¹ (A ⊕ B) {T.⊕.inr b₀}{T.⊕.inl a₁}{()}
  ⊢ρ₀⁻¹ (A ⊕ B) {T.⊕.inr b₀}{T.⊕.inr b₁}{≜ = ≜} =
    ι (⊢ρ₀⁻¹ B)
  idn₁ (A ⊕ B) {T.⊕.inl a₀}{T.⊕.inl a₁} =
    ι (idn₁ A)
  idn₁ (A ⊕ B) {T.⊕.inl a₀}{T.⊕.inr b₁}{()}
  idn₁ (A ⊕ B) {T.⊕.inr b₀}{T.⊕.inl a₁}{()}
  idn₁ (A ⊕ B) {T.⊕.inr b₀}{T.⊕.inr b₁} =
    ι (idn₁ B)
  seq₁ (A ⊕ B) {T.⊕.inl a₀}{T.⊕.inl a₁} (ι α₀) (ι α₁) =
    ι (seq₁ A α₀ α₁)
  seq₁ (A ⊕ B) {T.⊕.inl a₀}{T.⊕.inr b₁}{()}{()}{()}
  seq₁ (A ⊕ B) {T.⊕.inr b₀}{T.⊕.inl a₁}{()}{()}{()}
  seq₁ (A ⊕ B) {T.⊕.inr b₀}{T.⊕.inr b₁} (ι β₀) (ι β₁) =
    ι (seq₁ B β₀ β₁)
  inv₁ (A ⊕ B) {T.⊕.inl a₀}{T.⊕.inl a₁} (ι α) =
    ι (inv₁ A α)
  inv₁ (A ⊕ B) {T.⊕.inl a₀}{T.⊕.inr b₁}{()}{()}
  inv₁ (A ⊕ B) {T.⊕.inr b₀}{T.⊕.inl a₁}{()}{()}
  inv₁ (A ⊕ B) {T.⊕.inr b₀}{T.⊕.inr b₁} (ι β) =
    ι (inv₁ B β)

open ⊕ public
  using (_⊕_)
