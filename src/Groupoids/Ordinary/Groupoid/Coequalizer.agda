{-# OPTIONS --without-K #-}

module Groupoids.Ordinary.Groupoid.Coequalizer where

open import Groupoids.Common
open import Groupoids.Ordinary.Groupoid.Lift
open import Groupoids.Ordinary.Morphism.Hom.Boot
open import Groupoids.Ordinary.Universe.Boot

module Coequalizer where
  data Rel : Set where
    ⊢⇇ : Rel
    ⊢ι : Rel
    ⊢idn : Rel
    ⊢seq : (κ₀ κ₁ : Rel) → Rel
    ⊢inv : (κ : Rel) → Rel

  rel
    : ∀ {r}..{ℓ₀ ℓ₁}
    → {A : 𝔘 r ℓ₀}
    → {B : 𝔘 r ℓ₁}
    → (F G : Hom₀ A B)
    → (κ : Rel)
    → (b₀ b₁ : ● [ B ])
    → 𝔘 _ (ℓ₀ ⊔ ℓ₁)
  rel {ℓ₀ = ℓ₀}{B = B} F G ⊢⇇ b₀ b₁ =
    ⊔↑ {ℓ₁ = ℓ₀} {!!}
  rel F G ⊢ι b₀ b₁ =
    {!!}
  rel F G ⊢idn b₀ b₁ =
    {!!}
  rel F G (⊢seq κ κ₁) b₀ b₁ =
    {!!}
  rel F G (⊢inv κ) b₀ b₁ =
    {!!}

  CoEq
    : ∀ {r}..{ℓ₀ ℓ₁}
    → {A : 𝔘 r ℓ₀}
    → {B : 𝔘 r ℓ₁}
    → (F G : Hom₀ A B)
    → 𝔘 r _
  [ CoEq F G ] =
    𝔊.CoEq {!!} {!!}
  idn₀ (CoEq F G) =
    {!!}
  seq₀ (CoEq F G) =
    {!!}
  inv₀ (CoEq F G) =
    {!!}
  seq₀* (CoEq F G) =
    {!!}
  inv₀* (CoEq F G) =
    {!!}
  ⊢idn₀-λ (CoEq F G) =
    {!!}
  ⊢idn₀-ρ (CoEq F G) =
    {!!}
  ⊢seq₀-α (CoEq F G) =
    {!!}
  ⊢inv₀-λ (CoEq F G) =
    {!!}
  ⊢inv₀-ρ (CoEq F G) =
    {!!}
  idn₁ (CoEq F G) =
    {!!}
  seq₁ (CoEq F G) =
    {!!}
  inv₁ (CoEq F G) =
    {!!}
