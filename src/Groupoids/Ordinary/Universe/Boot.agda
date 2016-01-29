{-# OPTIONS --without-K #-}

module Groupoids.Ordinary.Universe.Boot where

open import Groupoids.Common
open 𝔊
  hiding (_▸_)

record 𝔘 (n r : ℕ∞) ..ℓ : Set (lsuc ℓ) where
  no-eta-equality
  infix 3 [_]
  open Fin
  field
    [_] : Gph 2+[ n ] r ℓ
  complex = [_]
  isGpd : Set
  isGpd = r T.≡ 0
  open Gph public
  open Cell {𝒢 = complex}
  idn₀
    : {a : ⊢[]}
    → 1 ⊢ a ↝ a
  idn₀ = ↻ [_]
  field
    seq₀
      : {a b c : ⊢[]}
      → (f : 1 ⊢ a ↝ b)
      → (g : 1 ⊢ b ↝ c)
      → 1 ⊢ a ↝ c
    inv₀
      : {a b : ⊢[]}
      → (f : 1 ⊢ a ↝ b)
      → {≜ : isGpd}
      → 1 ⊢ b ↝ a
  field
    seq₀*
      : {a b c : ⊢[]}
      → {f₀ f₁ : 1 ⊢ a ↝ b}
      → {g₀ g₁ : 1 ⊢ b ↝ c}
      → (α : 2 ⊢ f₀ ↝ f₁)
      → (β : 2 ⊢ g₀ ↝ g₁)
      → 2 ⊢ seq₀ f₀ g₀ ↝ seq₀ f₁ g₁
    inv₀*
      : {a b : ⊢[]}
      → {f g : 1 ⊢ a ↝ b}
      → (α : 2 ⊢ f ↝ g)
      → {≜ : isGpd}
      → 2 ⊢ inv₀ f {≜} ↝ inv₀ g {≜}
  field
    ⊢idn₀-λ
      : {a b : ⊢[]}
      → {f : 1 ⊢ a ↝ b}
      → 2 ⊢ seq₀ idn₀ f ↝ f
    ⊢idn₀-ρ
      : {a b : ⊢[]}
      → {f : 1 ⊢ a ↝ b}
      → 2 ⊢ seq₀ f idn₀ ↝ f
    ⊢seq₀-α
      : {a b c d : ⊢[]}
      → {f : 1 ⊢ a ↝ b}
      → {g : 1 ⊢ b ↝ c}
      → {h : 1 ⊢ c ↝ d}
      → 2 ⊢ seq₀ f (seq₀ g h) ↝ seq₀ (seq₀ f g) h
    ⊢inv₀-λ
      : {a b : ⊢[]}
      → {f : 1 ⊢ a ↝ b}
      → {≜ : isGpd}
      → 2 ⊢ seq₀ (inv₀ f {≜}) f ↝ idn₀
    ⊢inv₀-ρ
      : {a b : ⊢[]}
      → {f : 1 ⊢ a ↝ b}
      → {≜ : isGpd}
      → 2 ⊢ seq₀ f (inv₀ f {≜}) ↝ idn₀
  field
    idn₁
      : {a b : ⊢[]}
      → {f : 1 ⊢ a ↝ b}
      → 2 ⊢ f ↝ f
    seq₁
      : {a b : ⊢[]}
      → {f g h : 1 ⊢ a ↝ b}
      → (α : 2 ⊢ f ↝ g)
      → (β : 2 ⊢ g ↝ h)
      → 2 ⊢ f ↝ h
    inv₁
      : {a b : ⊢[]}
      → {f g : 1 ⊢ a ↝ b}
      → (α : 2 ⊢ f ↝ g)
      → 2 ⊢ g ↝ f

  seq₀*-λ
    : {a b c : ⊢[]}
    → {f₀ f₁ : 1 ⊢ a ↝ b}
    → {g : 1 ⊢ b ↝ c}
    → (α : 2 ⊢ f₀ ↝ f₁)
    → 2 ⊢ seq₀ f₀ g ↝ seq₀ f₁ g
  seq₀*-λ α = seq₀* α idn₁

  seq₀*-ρ
    : {a b c : ⊢[]}
    → {f : 1 ⊢ a ↝ b}
    → {g₀ g₁ : 1 ⊢ b ↝ c}
    → (β : 2 ⊢ g₀ ↝ g₁)
    → 2 ⊢ seq₀ f g₀ ↝ seq₀ f g₁
  seq₀*-ρ β = seq₀* idn₁ β

  cmp₀
    : {a b c : ⊢[]}
    → (g : 1 ⊢ b ↝ c)
    → (f : 1 ⊢ a ↝ b)
    → 1 ⊢ a ↝ c
  cmp₀ g f = seq₀ f g

  cmp₁
    : {a b : ⊢[]}
    → {f g h : 1 ⊢ a ↝ b}
    → (β : 2 ⊢ g ↝ h)
    → (α : 2 ⊢ f ↝ g)
    → 2 ⊢ f ↝ h
  cmp₁ β α = seq₁ α β

  cmp₀*
    : {a b c : ⊢[]}
    → {f₀ f₁ : 1 ⊢ a ↝ b}
    → {g₀ g₁ : 1 ⊢ b ↝ c}
    → (β : 2 ⊢ g₀ ↝ g₁)
    → (α : 2 ⊢ f₀ ↝ f₁)
    → 2 ⊢ cmp₀ g₀ f₀ ↝ cmp₀ g₁ f₁
  cmp₀* β α = seq₀* α β

  cmp₀*λ
    : {a b c : ⊢[]}
    → {f₀ f₁ : 1 ⊢ a ↝ b}
    → {g : 1 ⊢ b ↝ c}
    → (α : 2 ⊢ f₀ ↝ f₁)
    → 2 ⊢ cmp₀ g f₀ ↝ cmp₀ g f₁
  cmp₀*λ α = cmp₀* idn₁ α

  cmp₀*ρ
    : {a b c : ⊢[]}
    → {f : 1 ⊢ a ↝ b}
    → {g₀ g₁ : 1 ⊢ b ↝ c}
    → (β : 2 ⊢ g₀ ↝ g₁)
    → 2 ⊢ cmp₀ g₀ f ↝ cmp₀ g₁ f
  cmp₀*ρ β = cmp₀* β idn₁

  ⊢seq₀-α-«
    : {a b c d : ⊢[]}
    → {f : 1 ⊢ a ↝ b}
    → {g : 1 ⊢ b ↝ c}
    → {h : 1 ⊢ c ↝ d}
    → 2 ⊢ seq₀ (seq₀ f g) h ↝ seq₀ f (seq₀ g h)
  ⊢seq₀-α-« = inv₁ ⊢seq₀-α

  ⊢cmp₀-α
    : {a b c d : ⊢[]}
    → {f : 1 ⊢ a ↝ b}
    → {g : 1 ⊢ b ↝ c}
    → {h : 1 ⊢ c ↝ d}
    → 2 ⊢ cmp₀ h (cmp₀ g f) ↝ cmp₀ (cmp₀ h g) f
  ⊢cmp₀-α = inv₁ ⊢seq₀-α

  ⊢cmp₀-α-«
    : {a b c d : ⊢[]}
    → {f : 1 ⊢ a ↝ b}
    → {g : 1 ⊢ b ↝ c}
    → {h : 1 ⊢ c ↝ d}
    → 2 ⊢ cmp₀ (cmp₀ h g) f ↝ cmp₀ h (cmp₀ g f)
  ⊢cmp₀-α-« = ⊢seq₀-α

  infix 0 _▸
  infix 0 _▸_⊢_↝_

  _▸ : Set _
  _▸ = cell complex 0

  _▸_⊢_↝_ : (i : Nat) → Glob complex i [●]
  _▸_⊢_↝_ = cell complex

  _▸_⊩_↝_ : (i : Nat) → Glob complex i [⇇]
  _▸_⊩_↝_ = quiver complex

  {-# DISPLAY cell A i a b = A ▸ i ⊢ a ↝ b #-}
  {-# DISPLAY cell A 0 = A ▸ #-}

  infix 2 _⟓*_
  infix 2 _⟓_
  infix 2 _⟔_
  infix 4 _⁻¹

  _⟓_ = #display
  _⟔_ = #display
  _⁻¹ = #display
  _⟓*_ = #display
  _⁻¹* = #display

  {-# DISPLAY ↻ [_] = idn₀ #-}

  {-# DISPLAY idn₀ A = ↻ #-}
  {-# DISPLAY idn₁ A = ↻ #-}

  {-# DISPLAY seq₀ A f g = f ⟓ g #-}
  {-# DISPLAY seq₁ A α β = α ⟓ β #-}

  {-# DISPLAY cmp₀ A g f = g ⟔ f #-}
  {-# DISPLAY cmp₁ A β α = β ⟔ α #-}

  {-# DISPLAY inv₀ A f = f ⁻¹ #-}
  {-# DISPLAY inv₁ A α = α ⁻¹ #-}

  {-# DISPLAY seq₀* A β α = α ⟓* β #-}
  {-# DISPLAY inv₀* A α = α ⁻¹* #-}
open 𝔘 public

module _ where
  open 𝔘
  open Cell
  {-# DISPLAY ⊢[] {𝒢 = 𝒢} = 𝒢 ▸ #-}
  {-# DISPLAY _⊢_↝_ {𝒢 = 𝒢} i a b = 𝒢 ▸ i ⊢ a ↝ b #-}
  {-# DISPLAY _⊢_↝_ {𝒢 = 𝒢} i {a}{b} f g = 𝒢 ▸ i ⊢ f ↝ g #-}
  {-# DISPLAY _⊢_↝_ {𝒢 = 𝒢} i {a}{b}{f}{g} α β = 𝒢 ▸ i ⊢ α ↝ β #-}
open 𝔊 public
  using (⊢_)
  using (_↝_)
open 𝔊.Cell public
