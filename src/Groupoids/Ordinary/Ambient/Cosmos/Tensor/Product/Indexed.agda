{-# OPTIONS --without-K #-}

module Groupoids.Ordinary.Ambient.Cosmos.Tensor.Product.Indexed where

open import Groupoids.Basis
open import Groupoids.Ordinary.Ambient.Cosmos.Tensor.Product
open import Groupoids.Ordinary.Ambient.Morphism.Hom.Boot
open import Groupoids.Ordinary.Ambient.Universe.Boot

module Π where
  infix 0 Π

  Π : ∀ {r}..{ℓ₀ ℓ₁}
    → (I : Set ℓ₀)
    → (A : I → 𝔘 r ℓ₁)
    → 𝔘 r _
  [ Π I A ] =
    𝔊.Π.[ I ∋ i ] [ A i ]
  idn₀ (Π I A) {a}{i} =
    idn₀ (A i)
  seq₀ (Π I A) f g =
    seq₀ (A _) f g
  inv₀ (Π I A) f {≜} =
    inv₀ (A _) f {≜}
  seq₀* (Π I A) α β =
    seq₀* (A _) α β
  inv₀* (Π I A) α {≜} =
    inv₀* (A _) α {≜}
  ⊢idn₀-λ (Π I A) =
    ⊢idn₀-λ (A _)
  ⊢idn₀-ρ (Π I A) =
    ⊢idn₀-ρ (A _)
  ⊢seq₀-α (Π I A) =
    ⊢seq₀-α (A _)
  ⊢inv₀-λ (Π I A) {≜ = ≜} =
    ⊢inv₀-λ (A _) {≜ = ≜}
  ⊢inv₀-ρ (Π I A) {≜ = ≜} =
    ⊢inv₀-ρ (A _) {≜ = ≜}
  idn₁ (Π I A) =
    idn₁ (A _)
  seq₁ (Π I A) α β =
    seq₁ (A _) α β
  inv₁ (Π I A) α =
    inv₁ (A _) α

  syntax Π I (λ i → A) = [ I ∋ i ] A

open Π public
  using (Π)
