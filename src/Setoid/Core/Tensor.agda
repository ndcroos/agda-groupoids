{-# OPTIONS --without-K #-}

module Setoid.Core.Tensor where

open import Agda.Primitive
import Setoid.Core.Base as S
open import Setoid.Core.Hom as Π
import Setoid.Core.Homotopy as TF
open import Setoid.Core.Tensor.Boot public
open import Type as T
  using (_,_)

π₀
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ}
  → {A : S.t d ℓ₀ᵒ ℓ₀ʰ}
  → {B : S.t d ℓ₁ᵒ ℓ₁ʰ}
  → (A ⊗ B) Π.⇒₀ᵗ A
_$₀_ π₀ = T.∐.π₀
_$₁_ π₀ = T.∐.π₀

π₁
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ}
  → {A : S.t d ℓ₀ᵒ ℓ₀ʰ}
  → {B : S.t d ℓ₁ᵒ ℓ₁ʰ}
  → (A ⊗ B) Π.⇒₀ᵗ B
_$₀_ π₁ = T.∐.π₁
_$₁_ π₁ = T.∐.π₁

⟨-,-⟩
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ ℓ₂ᵒ ℓ₂ʰ}
  → {X : S.t d ℓ₀ᵒ ℓ₀ʰ}
  → {A : S.t d ℓ₁ᵒ ℓ₁ʰ}
  → {B : S.t d ℓ₂ᵒ ℓ₂ʰ}
  → ((X Π.⇒₀ˢ A) ⊗ (X Π.⇒₀ˢ B)) Π.⇒₀ᵗ (X Π.⇒₀ˢ A ⊗ B)
_$₀_ (_$₀_ ⟨-,-⟩ FG) =
  T.∐.⟨ T.∐.π₀ FG $₀_ , T.∐.π₁ FG $₀_ ⟩
_$₁_ (_$₀_ ⟨-,-⟩ FG) =
  T.∐.⟨ T.∐.π₀ FG $₁_ , T.∐.π₁ FG $₁_ ⟩
TF.com₁ (_$₁_ ⟨-,-⟩ x) =
  T.∐.⟨ TF.com₁ᵗ′ ⊗ TF.com₁ᵗ′ ⟩ x

⟨-⊗-⟩
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ ℓ₂ᵒ ℓ₂ʰ ℓ₃ᵒ ℓ₃ʰ}
  → {X₀ : S.t d ℓ₀ᵒ ℓ₀ʰ}
  → {X₁ : S.t d ℓ₁ᵒ ℓ₁ʰ}
  → {A : S.t d ℓ₂ᵒ ℓ₂ʰ}
  → {B : S.t d ℓ₃ᵒ ℓ₃ʰ}
  → ((X₀ Π.⇒₀ˢ A) ⊗ (X₁ Π.⇒₀ˢ B)) Π.⇒₀ᵗ ((X₀ ⊗ X₁) Π.⇒₀ˢ (A ⊗ B))
_$₀_ (_$₀_ ⟨-⊗-⟩ FG) =
  T.∐.⟨ T.∐.π₀ FG $₀_ ⊗ T.∐.π₁ FG $₀_ ⟩
_$₁_ (_$₀_ ⟨-⊗-⟩ FG) =
  T.∐.⟨ T.∐.π₀ FG $₁_ ⊗ T.∐.π₁ FG $₁_ ⟩
TF.com₁ (_$₁_ ⟨-⊗-⟩ x) =
  T.∐.⟨ TF.com₁ᵗ′ ⊗ TF.com₁ᵗ′ ⟩ x