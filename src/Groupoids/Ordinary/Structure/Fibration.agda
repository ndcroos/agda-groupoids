{-# OPTIONS --without-K #-}

module Groupoids.Ordinary.Structure.Fibration where

open import Groupoids.Basis
open import Groupoids.Ordinary.Ambient.Cosmos.Exponential
open import Groupoids.Ordinary.Ambient.Morphism.Hom
open import Groupoids.Ordinary.Ambient.Morphism.Iso
open import Groupoids.Ordinary.Ambient.Universe.Boot

module Fib where
  record Horn
    {n r}..{ℓ₀ ℓ₁}
    {E : 𝔘 n r ℓ₀}
    {B : 𝔘 n r ℓ₁}
    (π : Hom₀ E B)
    {□00 □10 : E ▸}
    (bot : E ▸ 1 ⊢ □00 ↝ □10)
    : Set (ℓ₀ ⊔ ℓ₁)
    where
    no-eta-equality
    constructor horn
    private
      π₀[_] = ap₀₀ π
      π₁[_] = ap₀₁ π
    field
      {□01} : E ▸
      img   : B ▸ 1 ⊢ π₀[ □01 ] ↝ π₀[ □00 ]
      dia   : E ▸ 1 ⊢ □01 ↝ □10
      coh   : B ▸ 2 ⊢ seq₀ B img π₁[ bot ] ↝ π₁[ dia ]

  record Refined
    {n r}..{ℓ₀ ℓ₁}
    {E : 𝔘 n r ℓ₀}
    {B : 𝔘 n r ℓ₁}
    (π : Hom₀ E B)
    {□00 □10 : E ▸}
    {bot : E ▸ 1 ⊢ □00 ↝ □10}
    (𝔥 : Horn π bot)
    : Set (ℓ₀ ⊔ ℓ₁)
    where
    no-eta-equality
    private
      π₀[_] = ap₀₀ π
      π₁[_] = ap₀₁ π
    open Horn 𝔥
    field
      lhs
        : E ▸ 1 ⊢ □01 ↝ □00
      coh-seq
        : E ▸ 2 ⊢ dia ↝ seq₀ E lhs bot
      coh-img
        : B ▸ 2 ⊢ π₁[ lhs ] ↝ img
      unique
        : (#lhs : E ▸ 1 ⊢ □01 ↝ □00)
        → (#seq : E ▸ 2 ⊢ dia ↝ seq₀ E #lhs bot)
        → (#img : B ▸ 2 ⊢ π₁[ #lhs ] ↝ img)
        → E ▸ 2 ⊢ #lhs ↝ lhs

  record Cartesian
    {n r}..{ℓ₀ ℓ₁}
    {E : 𝔘 n r ℓ₀}
    {B : 𝔘 n r ℓ₁}
    (π : Hom₀ E B)
    {□00 □10 : E ▸}
    (bot : E ▸ 1 ⊢ □00 ↝ □10)
    : Set (ℓ₀ ⊔ ℓ₁)
    where
    no-eta-equality
    private
      π₀[_] = ap₀₀ π
      π₁[_] = ap₀₁ π
    field
      edge : (𝔥 : Horn π bot) → Refined π 𝔥
    module Edge
      {□01}
      (img : B ▸ 1 ⊢ π₀[ □01 ] ↝ π₀[ □00 ])
      (dia : E ▸ 1 ⊢ □01 ↝ □10)
      (coh : B ▸ 2 ⊢ seq₀ B img π₁[ bot ] ↝ π₁[ dia ])
      where
      open Refined (edge (horn img dia coh)) public
  open Cartesian public

  record Lifted
    {n r}..{ℓ₀ ℓ₁}
    {E : 𝔘 n r ℓ₀}
    {B : 𝔘 n r ℓ₁}
    (π : Hom₀ E B)
    {b e}
    (f : B ▸ 1 ⊢ b ↝ ap₀₀ π e)
    : Set (ℓ₀ ⊔ ℓ₁)
    where
    no-eta-equality
    open Iso
    private
      π₀[_] = ap₀₀ π
      π₁[_] = ap₀₁ π
    field
      dom : E ▸
      map : E ▸ 1 ⊢ dom ↝ e
      car : Cartesian π map
    field
      coe : B ⊢ b ≅ π₀[ dom ]
      coh : B ▸ 2 ⊢ seq₀ B (« coe) f ↝ π₁[ map ]

  record Fibration
    {n r}..{ℓ₀ ℓ₁}
    {E : 𝔘 n r ℓ₀}
    {B : 𝔘 n r ℓ₁}
    (π : Hom₀ E B)
    : Set (ℓ₀ ⊔ ℓ₁)
    where
    no-eta-equality
    private
      π₀[_] = ap₀₀ π
      π₁[_] = ap₀₁ π
    field
      lift
        : ∀ {b e}
        → (f : B ▸ 1 ⊢ b ↝ π₀[ e ])
        → Lifted π f
    module Lift {b e} (f : B ▸ 1 ⊢ b ↝ π₀[ e ]) where
      open Lifted (lift f) public
  open Fibration public

  OpFibration
    : ∀ {n r}..{ℓ₀ ℓ₁}
    → {E : 𝔘 n r ℓ₀}
    → {B : 𝔘 n r ℓ₁}
    → (π : Hom₀ E B)
    → Set (ℓ₀ ⊔ ℓ₁)
  OpFibration π = Fibration (ap₀₀ ⇒.⊢.op⇒ π)

  record BiFibration
    {n r}..{ℓ₀ ℓ₁}
    {E : 𝔘 n r ℓ₀}
    {B : 𝔘 n r ℓ₁}
    (π : Hom₀ E B)
    : Set (ℓ₀ ⊔ ℓ₁)
    where
    field
      fib→ :   Fibration π
      fib← : OpFibration π

  Fib→ =   Fibration
  Fib← = OpFibration
  Fib↔ = BiFibration

  {-# DISPLAY   Fibration = Fib→ #-}
  {-# DISPLAY OpFibration = Fib← #-}
  {-# DISPLAY BiFibration = Fib↔ #-}

open Fib public
  using (Cartesian)
  using (Fibration)
