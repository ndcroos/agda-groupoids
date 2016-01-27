{-# OPTIONS --without-K #-}

module Groupoids.Core.Groupoid.Ordinary.Universe.Boot where

open import Groupoids.Common
open 𝔊
  hiding (_▸_)

record 𝔘 n (r : Fin 2) ..ℓ : Set (lsuc ℓ) where
  no-eta-equality
  infix 3 [_]
  open Fin
  field
    [_] : Gph (2+ n) (⊆nat∞ r) ℓ
  complex = [_]
  field
    lvl : Type [_] (2+ n)
  isGpd : Set
  isGpd = r T.≡ ze
  open Gph public
  open Cell complex
  field
    idn₀
      : {a : ·}
      → 1 ⊢ a ↝ a
    seq₀
      : {a b c : ·}
      → (f : 1 ⊢ a ↝ b)
      → (g : 1 ⊢ b ↝ c)
      → 1 ⊢ a ↝ c
    inv₀
      : {a b : ·}
      → (f : 1 ⊢ a ↝ b)
      → {≜ : isGpd}
      → 1 ⊢ b ↝ a
  field
    seq₀*
      : {a b c : ·}
      → {f₀ f₁ : 1 ⊢ a ↝ b}
      → {g₀ g₁ : 1 ⊢ b ↝ c}
      → (α : 2 ⊢ f₀ ↝ f₁)
      → (β : 2 ⊢ g₀ ↝ g₁)
      → 2 ⊢ seq₀ f₀ g₀ ↝ seq₀ f₁ g₁
    inv₀*
      : {a b : ·}
      → {f g : 1 ⊢ a ↝ b}
      → (α : 2 ⊢ f ↝ g)
      → {≜ : isGpd}
      → 2 ⊢ inv₀ f {≜} ↝ inv₀ g {≜}
  field
    ⊢λ₀
      : {a b : ·}
      → {f : 1 ⊢ a ↝ b}
      → 2 ⊢ seq₀ idn₀ f ↝ f
    ⊢ρ₀
      : {a b : ·}
      → {f : 1 ⊢ a ↝ b}
      → 2 ⊢ seq₀ f idn₀ ↝ f
    ⊢α₀
      : {a b c d : ·}
      → {f : 1 ⊢ a ↝ b}
      → {g : 1 ⊢ b ↝ c}
      → {h : 1 ⊢ c ↝ d}
      → 2 ⊢ seq₀ f (seq₀ g h) ↝ seq₀ (seq₀ f g) h
    ⊢λ₀⁻¹
      : {a b : ·}
      → {f : 1 ⊢ a ↝ b}
      → {≜ : isGpd}
      → 2 ⊢ seq₀ (inv₀ f {≜}) f ↝ idn₀
    ⊢ρ₀⁻¹
      : {a b : ·}
      → {f : 1 ⊢ a ↝ b}
      → {≜ : isGpd}
      → 2 ⊢ seq₀ f (inv₀ f {≜}) ↝ idn₀
  field
    idn₁
      : {a b : ·}
      → {f : 1 ⊢ a ↝ b}
      → 2 ⊢ f ↝ f
    seq₁
      : {a b : ·}
      → {f g h : 1 ⊢ a ↝ b}
      → (α : 2 ⊢ f ↝ g)
      → (β : 2 ⊢ g ↝ h)
      → 2 ⊢ f ↝ h
    inv₁
      : {a b : ·}
      → {f g : 1 ⊢ a ↝ b}
      → (α : 2 ⊢ f ↝ g)
      → 2 ⊢ g ↝ f

  seq₀*λ
    : {a b c : ·}
    → {f₀ f₁ : 1 ⊢ a ↝ b}
    → {g : 1 ⊢ b ↝ c}
    → (α : 2 ⊢ f₀ ↝ f₁)
    → 2 ⊢ seq₀ f₀ g ↝ seq₀ f₁ g
  seq₀*λ α = seq₀* α idn₁

  seq₀*ρ
    : {a b c : ·}
    → {f : 1 ⊢ a ↝ b}
    → {g₀ g₁ : 1 ⊢ b ↝ c}
    → (β : 2 ⊢ g₀ ↝ g₁)
    → 2 ⊢ seq₀ f g₀ ↝ seq₀ f g₁
  seq₀*ρ β = seq₀* idn₁ β

  cmp₀
    : {a b c : ·}
    → (g : 1 ⊢ b ↝ c)
    → (f : 1 ⊢ a ↝ b)
    → 1 ⊢ a ↝ c
  cmp₀ g f = seq₀ f g

  cmp₁
    : {a b : ·}
    → {f g h : 1 ⊢ a ↝ b}
    → (β : 2 ⊢ g ↝ h)
    → (α : 2 ⊢ f ↝ g)
    → 2 ⊢ f ↝ h
  cmp₁ β α = seq₁ α β

  cmp₀*
    : {a b c : ·}
    → {f₀ f₁ : 1 ⊢ a ↝ b}
    → {g₀ g₁ : 1 ⊢ b ↝ c}
    → (β : 2 ⊢ g₀ ↝ g₁)
    → (α : 2 ⊢ f₀ ↝ f₁)
    → 2 ⊢ cmp₀ g₀ f₀ ↝ cmp₀ g₁ f₁
  cmp₀* β α = seq₀* α β

  cmp₀*λ
    : {a b c : ·}
    → {f₀ f₁ : 1 ⊢ a ↝ b}
    → {g : 1 ⊢ b ↝ c}
    → (α : 2 ⊢ f₀ ↝ f₁)
    → 2 ⊢ cmp₀ g f₀ ↝ cmp₀ g f₁
  cmp₀*λ α = cmp₀* idn₁ α

  cmp₀*ρ
    : {a b c : ·}
    → {f : 1 ⊢ a ↝ b}
    → {g₀ g₁ : 1 ⊢ b ↝ c}
    → (β : 2 ⊢ g₀ ↝ g₁)
    → 2 ⊢ cmp₀ g₀ f ↝ cmp₀ g₁ f
  cmp₀*ρ β = cmp₀* β idn₁

  infix 0 _▸
  infix 0 _▸_⊢_↝_

  _▸ : Set _
  _▸ = cell complex 0

  _▸_⊢_↝_ : (i : Nat) → Glob complex i [·]
  _▸_⊢_↝_ = cell complex

  _▸_⊩_↝_ : (i : Nat) → Glob complex i [*]
  _▸_⊩_↝_ = quiver complex

  {-# DISPLAY cell A i a b = A ▸ i ⊢ a ↝ b #-}
  {-# DISPLAY cell A 0 = A ▸ #-}
