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
    {□00 □10 : E ▸}
    (00□10 : E ▸ 1 ⊢ □00 ↝ □10)
    : Set (ℓ₀ ⊔ ℓ₁)
    where
    no-eta-equality
    π₀[_] = ap₀₀ π
    π₁[_] = ap₀₁ π
    field
      edge-∃
        : ∀ {□01}
        → {01□10 : E ▸ 1 ⊢ □01 ↝ □10}
        → {π₁[01□00] : B ▸ 1 ⊢ π₀[ □01 ] ↝ π₀[ □00 ]}
        → ⦃ ε : B ▸ 2 ⊢ seq₀ B π₁[01□00] π₁[ 00□10 ] ↝ π₁[ 01□10 ] ⦄
        → E ▸ 1 ⊢ □01 ↝ □00
    01□00 = edge-∃
    field
      ⊢edge-⟓
        : ∀ {□01}
        → {01□10 : E ▸ 1 ⊢ □01 ↝ □10}
        → {π₁[01□00] : B ▸ 1 ⊢ π₀[ □01 ] ↝ π₀[ □00 ]}
        → ⦃ ε : B ▸ 2 ⊢ seq₀ B π₁[01□00] π₁[ 00□10 ] ↝ π₁[ 01□10 ] ⦄
        → E ▸ 2 ⊢ 01□10 ↝ seq₀ E 01□00 00□10
      ⊢edge-π[-]
        : ∀ {□01}
        → {01□10 : E ▸ 1 ⊢ □01 ↝ □10}
        → {π₁[01□00] : B ▸ 1 ⊢ π₀[ □01 ] ↝ π₀[ □00 ]}
        → ⦃ ε : B ▸ 2 ⊢ seq₀ B π₁[01□00] π₁[ 00□10 ] ↝ π₁[ 01□10 ] ⦄
        → B ▸ 2 ⊢ π₁[ 01□00 ] ↝ π₁[01□00]
      ⊢edge-!
        : ∀ {□01}
        → {01□10 : E ▸ 1 ⊢ □01 ↝ □10}
        → {π₁[01□00] : B ▸ 1 ⊢ π₀[ □01 ] ↝ π₀[ □00 ]}
        → ⦃ ε : B ▸ 2 ⊢ seq₀ B π₁[01□00] π₁[ 00□10 ] ↝ π₁[ 01□10 ] ⦄
        → (01#00 : E ▸ 1 ⊢ □01 ↝ □00)
        → (E ▸ 2 ⊢ 01□10 ↝ seq₀ E 01#00 00□10)
        → B ▸ 2 ⊢ π₁[ 01#00 ] ↝ π₁[01□00]
        → E ▸ 2 ⊢ 01#00 ↝ 01□00
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
