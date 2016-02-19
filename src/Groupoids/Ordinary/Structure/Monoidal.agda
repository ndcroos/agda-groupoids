{-# OPTIONS --without-K #-}

module Groupoids.Ordinary.Structure.Monoidal where

open import Groupoids.Basis
open import Groupoids.Ordinary.Ambient.Cosmos.Diagonal
open import Groupoids.Ordinary.Ambient.Cosmos.Tensor.Product
open import Groupoids.Ordinary.Ambient.Morphism.Hom
open import Groupoids.Ordinary.Ambient.Morphism.Iso
open import Groupoids.Ordinary.Ambient.Universe.Boot

module Monoidal where
  open Iso
  open ⊗
    using (⟨_,_⟩)
    using (⟨_⊗_⟩)

  record Mon {r}..{ℓ} (A : 𝔘 r ℓ) : Set (lsuc ℓ) where
    no-eta-equality
    field
      «⊗»
        : Hom₀ (A ⊗ A) A
      «𝟙»
        : A ▸

    𝟙₀ = «𝟙»

    _⊗₀_
      : (x y : A ▸)
      → A ▸
    _⊗₀_ x y = ap₀₀ «⊗» (x , y)

    _⊗₁_
      : {x₀ x₁ y₀ y₁ : A ▸}
      → (f : A ▸ 1 ⊢ x₀ ↝ x₁)
      → (g : A ▸ 1 ⊢ y₀ ↝ y₁)
      → A ▸ 1 ⊢ x₀ ⊗₀ y₀ ↝ x₁ ⊗₀ y₁
    _⊗₁_ f g = ap₀₁ «⊗» (f , g)

    _⊗₂_
      : {x₀ x₁ y₀ y₁ : A ▸}
      → {f₀ f₁ : A ▸ 1 ⊢ x₀ ↝ x₁}
      → {g₀ g₁ : A ▸ 1 ⊢ y₀ ↝ y₁}
      → (α : A ▸ 2 ⊢ f₀ ↝ f₁)
      → (β : A ▸ 2 ⊢ g₀ ↝ g₁)
      → A ▸ 2 ⊢ f₀ ⊗₁ g₀ ↝ f₁ ⊗₁ g₁
    _⊗₂_ α β = ap₀₂ «⊗» (α , β)

    field
      ≅λ
        : A ⇒₀ A
        ⊢ ⟨ Δ.ʲ[ 𝟙₀ ] , ↻₀ ⟩ ⟓₀ «⊗»
        ≅ ↻₀
      ≅ρ
        : A ⇒₀ A
        ⊢ ⟨ ↻₀ , Δ.ʲ[ 𝟙₀ ] ⟩ ⟓₀ «⊗»
        ≅ ↻₀
      ≅α
        : A ⊗ (A ⊗ A) ⇒₀ A
        ⊢ ⟨ ↻₀ ⊗ «⊗» ⟩ ⟓₀ «⊗»
        ≅ ⟨ «⊗» ⊗ ↻₀ ⟩ ⟓₀ «⊗» ⟔₀ ⊗.⊢.α⇐

    λ₀ : {x : A ▸} → _
    λ₀ {x} = ap₁₀ (» ≅λ) x

    ρ₀ : {x : A ▸} → _
    ρ₀ {x} = ap₁₀ (» ≅ρ) x

    α₀ : {x y z : A ▸} → _
    α₀ {x}{y}{z} = ap₁₀ (» ≅α) (x , y , z)

    field
      ⊢tri
        : {x y : A ▸} →
        ● (⇇ (⇇ [ A ] (x ⊗₀ (𝟙₀ ⊗₀ y)) (x ⊗₀ y))
          (seq₀ A α₀ (ρ₀ ⊗₁ idn₀ A))
          (idn₀ A ⊗₁ λ₀))
      ⊢pnt
        : {w x y z : A ▸} →
        ● (⇇ (⇇ [ A ] (w ⊗₀ (x ⊗₀ (y ⊗₀ z))) (((w ⊗₀ x) ⊗₀ y) ⊗₀ z))
          (seq₀ A α₀ α₀)
          (seq₀ A
            (idn₀ A ⊗₁ α₀)
            (seq₀ A α₀ (α₀ ⊗₁ idn₀ A))))

open Monoidal public
  using (Mon)
