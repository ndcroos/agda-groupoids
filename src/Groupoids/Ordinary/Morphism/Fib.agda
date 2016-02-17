{-# OPTIONS --without-K #-}

module Groupoids.Ordinary.Morphism.Fib where

import Groupoids.Ordinary.Morphism.Hom.Boot
open import Groupoids.Common
open import Groupoids.Ordinary.Construction.Core
open import Groupoids.Ordinary.Morphism.Hom
open import Groupoids.Ordinary.Morphism.Iso
open import Groupoids.Ordinary.Universe.Boot

module Fib where
  record Horn
    {r}..{ℓ₀ ℓ₁}
    {E : 𝔘 r ℓ₀}
    {B : 𝔘 r ℓ₁}
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
      {□01}   : E ▸
      π₁[lhs] : B ▸ 1 ⊢ π₀[ □01 ] ↝ π₀[ □00 ]
      dia     : E ▸ 1 ⊢ □01 ↝ □10
      coh     : B ▸ 2 ⊢ seq₀ B π₁[lhs] π₁[ bot ] ↝ π₁[ dia ]

  record Refined
    {r}..{ℓ₀ ℓ₁}
    {E : 𝔘 r ℓ₀}
    {B : 𝔘 r ℓ₁}
    (π : Hom₀ E B)
    {□00 □10 : E ▸}
    {bot : E ▸ 1 ⊢ □00 ↝ □10}
    (π-horn : Horn π bot)
    : Set (ℓ₀ ⊔ ℓ₁)
    where
    no-eta-equality
    private
      π₀[_] = ap₀₀ π
      π₁[_] = ap₀₁ π
    open Horn π-horn
    field
      lhs
        : E ▸ 1 ⊢ □01 ↝ □00
      ⊢seq
        : E ▸ 2 ⊢ dia ↝ seq₀ E lhs bot
      ⊢img
        : B ▸ 2 ⊢ π₁[ lhs ] ↝ π₁[lhs]
      ⊢unique
        : (#lhs : E ▸ 1 ⊢ □01 ↝ □00)
        → E ▸ 2 ⊢ dia ↝ seq₀ E #lhs bot
        → B ▸ 2 ⊢ π₁[ #lhs ] ↝ π₁[lhs]
        → E ▸ 2 ⊢ #lhs ↝ lhs

  record Cartesian
    {r}..{ℓ₀ ℓ₁}
    {E : 𝔘 r ℓ₀}
    {B : 𝔘 r ℓ₁}
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
      edge : (horn : Horn π bot) → Refined π horn
    module Edge
      {□01}
      (π₁[lhs] : B ▸ 1 ⊢ π₀[ □01 ] ↝ π₀[ □00 ])
      (dia : E ▸ 1 ⊢ □01 ↝ □10)
      (coh : B ▸ 2 ⊢ seq₀ B π₁[lhs] π₁[ bot ] ↝ π₁[ dia ])
      where
      open Refined (edge (horn π₁[lhs] dia coh)) public
  open Cartesian public

  record Lifted
    {r}..{ℓ₀ ℓ₁}
    {E : 𝔘 r ℓ₀}
    {B : 𝔘 r ℓ₁}
    (π : Hom₀ E B)
    {b e}
    (f : B ▸ 1 ⊢ b ↝ ap₀₀ π e)
    : Set (ℓ₀ ⊔ ℓ₁)
    where
    no-eta-equality
    private
      π₀[_] = ap₀₀ π
      π₁[_] = ap₀₁ π
    field
      dom : E ▸
      map : E ▸ 1 ⊢ dom ↝ e
      iso : B ⊢ b ≅ π₀[ dom ]
      coh : B ▸ 2 ⊢ seq₀ B (Iso.« iso) f ↝ π₁[ map ]
      car : Cartesian π map

  record Fibration
    {r}..{ℓ₀ ℓ₁}
    {E : 𝔘 r ℓ₀}
    {B : 𝔘 r ℓ₁}
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

open Fib public
  using (Cartesian)
  using (Fibration)
