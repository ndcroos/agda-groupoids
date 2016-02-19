{-# OPTIONS --without-K #-}

module Groupoids.Ordinary.Structure.Monoidal where

open import Groupoids.Basis
open import Groupoids.Ordinary.Ambient.Cosmos.Diagonal
open import Groupoids.Ordinary.Ambient.Cosmos.Tensor.Product
open import Groupoids.Ordinary.Ambient.Cosmos.Unit.Terminal
open import Groupoids.Ordinary.Ambient.Morphism.Hom
open import Groupoids.Ordinary.Ambient.Morphism.Iso
open import Groupoids.Ordinary.Ambient.Universe.Boot

module Monoidal where
  open Iso
  open ⊗
    using (⟨_,_⟩)
    using (⟨_⊗_⟩)

  record Monoidal {r}..{ℓ} (A : 𝔘 r ℓ) : Set (lsuc ℓ) where
    no-eta-equality
    field
      one : A ▸
      ten : Hom₀ (A ⊗ A) A

    𝟙₀ = one

    _⊛₀_
      : (x y : A ▸)
      → A ▸
    _⊛₀_ x y = ap₀₀ ten (x , y)

    _⊛₁_
      : {x₀ x₁ y₀ y₁ : A ▸}
      → (f : A ▸ 1 ⊢ x₀ ↝ x₁)
      → (g : A ▸ 1 ⊢ y₀ ↝ y₁)
      → A ▸ 1 ⊢ x₀ ⊛₀ y₀ ↝ x₁ ⊛₀ y₁
    _⊛₁_ f g = ap₀₁ ten (f , g)

    _⊛₂_
      : {x₀ x₁ y₀ y₁ : A ▸}
      → {f₀ f₁ : A ▸ 1 ⊢ x₀ ↝ x₁}
      → {g₀ g₁ : A ▸ 1 ⊢ y₀ ↝ y₁}
      → (α : A ▸ 2 ⊢ f₀ ↝ f₁)
      → (β : A ▸ 2 ⊢ g₀ ↝ g₁)
      → A ▸ 2 ⊢ f₀ ⊛₁ g₀ ↝ f₁ ⊛₁ g₁
    _⊛₂_ α β = ap₀₂ ten (α , β)

    field
      ≅λ
        : A ⇒₀ A
        ⊢ ⟨ Δ.ʲ[ 𝟙₀ ] , ↻₀ ⟩ ⟓₀ ten
        ≅ ↻₀
      ≅ρ
        : A ⇒₀ A
        ⊢ ⟨ ↻₀ , Δ.ʲ[ 𝟙₀ ] ⟩ ⟓₀ ten
        ≅ ↻₀
      ≅α
        : A ⊗ A ⊗ A ⇒₀ A
        ⊢ ⟨ ↻₀ ⊗ ten ⟩ ⟓₀ ten
        ≅ ⟨ ten ⊗ ↻₀ ⟩ ⟓₀ ten ⟔₀ ⊗.⊢.α⇐

    λ₀ : {x : A ▸} → _
    λ₀ {x} = ap₁₀ (» ≅λ) x

    ρ₀ : {x : A ▸} → _
    ρ₀ {x} = ap₁₀ (» ≅ρ) x

    α₀ : {x y z : A ▸} → _
    α₀ {x}{y}{z} = ap₁₀ (» ≅α) (x , y , z)

    field
      ⊢tri
        : {x y : A ▸} →
        ● (⇇ (⇇ [ A ] (x ⊛₀ (𝟙₀ ⊛₀ y)) (x ⊛₀ y))
          (seq₀ A α₀ (ρ₀ ⊛₁ idn₀ A))
          (idn₀ A ⊛₁ λ₀))
      ⊢pnt
        : {w x y z : A ▸} →
        ● (⇇ (⇇ [ A ] (w ⊛₀ (x ⊛₀ (y ⊛₀ z))) (((w ⊛₀ x) ⊛₀ y) ⊛₀ z))
          (seq₀ A α₀ α₀)
          (seq₀ A
            (idn₀ A ⊛₁ α₀)
            (seq₀ A α₀ (α₀ ⊛₁ idn₀ A))))

  module _ where
    open Monoidal
    {-# DISPLAY one A = 𝟙 #-}
    {-# DISPLAY ten A = ⊛ #-}
    {-# DISPLAY _⊛₀_ A = _⊛_ #-}
    {-# DISPLAY _⊛₁_ A = _⊛_ #-}
    {-# DISPLAY _⊛₂_ A = _⊛_ #-}

  record Monoid {r}..{ℓ}
    {A : 𝔘 r ℓ}
    (Ψ : Monoidal A)
    : Set ℓ
    where
    no-eta-equality
    open Monoidal Ψ
    field
      mon : A ▸
    field
      mul : A ▸ 1 ⊢ mon ⊛₀ mon ↝ mon
      nil : A ▸ 1 ⊢ 𝟙₀ ↝ mon
    field
      ⊢α : A ▸ 2 ⊢ seq₀ A α₀ (seq₀ A (mul ⊛₁ idn₀ A) mul) ↝ seq₀ A (idn₀ A ⊛₁ mul) mul
      ⊢λ : A ▸ 2 ⊢ seq₀ A (nil ⊛₁ idn₀ A) mul ↝ λ₀
      ⊢ρ : A ▸ 2 ⊢ seq₀ A (idn₀ A ⊛₁ nil) mul ↝ ρ₀

  open Monoid public
  open Monoidal public
open Monoidal public
  hiding (module Monoidal)
  using (Monoidal)
  using (Monoid)
