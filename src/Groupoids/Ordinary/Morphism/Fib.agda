{-# OPTIONS --without-K #-}

module Groupoids.Ordinary.Morphism.Fib where

import Groupoids.Ordinary.Morphism.Hom.Boot
open import Groupoids.Common
open import Groupoids.Ordinary.Construction.Core
open import Groupoids.Ordinary.Morphism.Hom
open import Groupoids.Ordinary.Morphism.Iso
open import Groupoids.Ordinary.Universe.Boot

module Fib where
  record Cartesian
    {r}..{ℓ₀ ℓ₁}
    {E : 𝔘 r ℓ₀}
    {B : 𝔘 r ℓ₁}
    (π : Hom₀ E B)
    {↙ ↘ : E ▸}
    (φ : E ▸ 1 ⊢ ↙ ↝ ↘)
    : Set (ℓ₀ ⊔ ℓ₁)
    where
    no-eta-equality
    π₀[_] = ap₀₀ π
    π₁[_] = ap₀₁ π
    field
      ↓map
        : ∀ {↖}
        → (ψ : E ▸ 1 ⊢ ↖ ↝ ↘)
        → (π₁[↓map] : B ▸ 1 ⊢ π₀[ ↖ ] ↝ π₀[ ↙ ])
        → (ε : B ▸ 2 ⊢ seq₀ B π₁[↓map] π₁[ φ ] ↝ π₁[ ψ ])
        → E ▸ 1 ⊢ ↖ ↝ ↙
      ≃-seq
        : ∀ {↖}
        → (ψ : E ▸ 1 ⊢ ↖ ↝ ↘)
        → (π₁[↓map] : B ▸ 1 ⊢ π₀[ ↖ ] ↝ π₀[ ↙ ])
        → (ε : B ▸ 2 ⊢ seq₀ B π₁[↓map] π₁[ φ ] ↝ π₁[ ψ ])
        → E ▸ 2 ⊢ ψ ↝ seq₀ E (↓map ψ π₁[↓map] ε) φ
      ≃-↓map
        : ∀ {↖}
        → (ψ : E ▸ 1 ⊢ ↖ ↝ ↘)
        → (π₁[↓map] : B ▸ 1 ⊢ π₀[ ↖ ] ↝ π₀[ ↙ ])
        → (ε : B ▸ 2 ⊢ seq₀ B π₁[↓map] π₁[ φ ] ↝ π₁[ ψ ])
        → B ▸ 2 ⊢ π₁[ ↓map ψ π₁[↓map] ε ] ↝ π₁[↓map]
      ≃-unique
        : ∀ {↖}
        → (ψ : E ▸ 1 ⊢ ↖ ↝ ↘)
        → (π₁[↓map] : B ▸ 1 ⊢ π₀[ ↖ ] ↝ π₀[ ↙ ])
        → (ε : B ▸ 2 ⊢ seq₀ B π₁[↓map] π₁[ φ ] ↝ π₁[ ψ ])
        → (k : E ▸ 1 ⊢ ↖ ↝ ↙)
        → (E ▸ 2 ⊢ ψ ↝ seq₀ E k φ)
        → B ▸ 2 ⊢ π₁[ k ] ↝ π₁[↓map]
        → E ▸ 2 ⊢ k ↝ ↓map ψ π₁[↓map] ε
  open Cartesian public
    hiding (π₀[_])
    hiding (π₁[_])

  record Fibration
    {r}..{ℓ₀ ℓ₁}
    {E : 𝔘 r ℓ₀}
    {B : 𝔘 r ℓ₁}
    (π : Hom₀ E B)
    : Set (ℓ₀ ⊔ ℓ₁)
    where
    no-eta-equality
    π₀[_] = ap₀₀ π
    π₁[_] = ap₀₁ π
    field
      lift-obj
        : ∀ {b e}
        → (f : B ▸ 1 ⊢ b ↝ π₀[ e ])
        → E ▸
      lift-map
        : ∀ {b e}
        → (f : B ▸ 1 ⊢ b ↝ π₀[ e ])
        → E ▸ 1 ⊢ lift-obj f ↝ e
      lift-iso
        : ∀ {b e}
        → (f : B ▸ 1 ⊢ b ↝ π₀[ e ])
        → B ⊢ b ≅ π₀[ lift-obj f ]
      lift-coh
        : ∀ {b e}
        → (f : B ▸ 1 ⊢ b ↝ π₀[ e ])
        → B ▸ 2 ⊢ seq₀ B (Iso.« (lift-iso f)) f ↝ π₁[ lift-map f ]
      cartesian
        : ∀ {b e}
        → (f : B ▸ 1 ⊢ b ↝ π₀[ e ])
        → Cartesian π (lift-map f)
  open Fibration public
    hiding (π₀[_])
    hiding (π₁[_])

open Fib public
  using (Cartesian)
  using (Fibration)
