{-# OPTIONS --without-K #-}

module Setoid.Tensor.Boot where

open import Agda.Primitive
import Setoid.Base as S
open import Type as T
  using (_,_)

infixr 3 _⊗_

_⊗_
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ}
  → (A : S.t d ℓ₀ᵒ ℓ₀ʰ)
  → (B : S.t d ℓ₁ᵒ ℓ₁ʰ)
  → S.t d _ _
S.obj (A ⊗ B) =
  S.t.obj A T.∐.⊗ S.t.obj B
S.homᵗ (A ⊗ B) =
  λ {((a₀ , b₀) , (a₁ , b₁)) →
    S.homᵗ A (a₀ , a₁) T.∐.⊗ S.homᵗ B (b₀ , b₁)
  }
S.idnᵗᵐ (A ⊗ B) =
  T.∐.⟨ S.idnᵗᵐ A , S.idnᵗᵐ B ⟩
S.cmpᵗᵐ (A ⊗ B) =
  T.∐.⟨ S.cmpᵗᵐ A T.Π.∘ T.∐.⟨ T.∐.π₀ ⊗ T.∐.π₀ ⟩
      , S.cmpᵗᵐ B T.Π.∘ T.∐.⟨ T.∐.π₁ ⊗ T.∐.π₁ ⟩ ⟩
S.invᵗᵐ (_⊗_ {S.Dir.≤} A B) = _
S.invᵗᵐ (_⊗_ {S.Dir.≈} A B) = T.∐.⟨ S.invᵗᵐ A ⊗ S.invᵗᵐ B ⟩
