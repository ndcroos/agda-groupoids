{-# OPTIONS --without-K #-}

module Groupoids.Ambient.Type.Tensor.Boot where

open import Agda.Primitive

infixr 0 _,_
infixr 1 _⊗_

record ∐ ..{ℓ₀ ℓ₁} (A : Set ℓ₀) (B : A → Set ℓ₁) : Set (ℓ₀ ⊔ ℓ₁) where
  constructor _,_
  field
    π₀ : A
    π₁ : B π₀
open ∐ public

_⊗_
  : ∀ ..{ℓ₀ ℓ₁}
  → (A : Set ℓ₀)
  → (B : Set ℓ₁)
  → Set (ℓ₀ ⊔ ℓ₁)
A ⊗ B = ∐ A λ _ → B
