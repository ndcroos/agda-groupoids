{-# OPTIONS --without-K #-}

module Groupoids.Ordinary.Construction.Simplex where

open import Groupoids.Common
open import Groupoids.Ordinary.Universe
open import Prelude.Natural

module Simplex where
  -- Augmented Simplex based on Sjoerd Visscher's Haskell encoding

  infix 0 _⊒_
  infix 1 _▸*

  -- ∆ = \increment
  ∆₀ : Set
  ∆₀ = Nat

  pattern ∅ = ze
  pattern _▸* Γ = su Γ

  data _⊒_ : ∆₀ → ∆₀ → Set where
    stop : ∅ ⊒ ∅
    drop_ : ∀ {Γ Δ} (ρ : Δ ⊒ Γ) → Δ ⊒ Γ ▸*
    dgen_ : ∀ {Γ Δ} (ρ : Δ ⊒ Γ ▸*) → Δ ▸* ⊒ Γ ▸*

  pattern ε = stop
  pattern δ_ ρ = drop ρ
  pattern σ_ ρ = dgen ρ

  ∆-idn₀
    : ∀ {Γ}
    → Γ ⊒ Γ
  ∆-idn₀ {∅} = stop
  ∆-idn₀ {Γ ▸*} = dgen drop ∆-idn₀

  ∆-seq₀
    : ∀ {Γ Δ Θ}
    → (f : Θ ⊒ Δ)
    → (g : Δ ⊒ Γ)
    → Θ ⊒ Γ
  ∆-seq₀ ρ₀ (drop ρ₁) = drop ∆-seq₀ ρ₀ ρ₁
  ∆-seq₀ stop ρ₁ = ρ₁
  ∆-seq₀ (drop ρ₀) (dgen ρ₁) = ∆-seq₀ ρ₀ ρ₁
  ∆-seq₀ (dgen ρ₀) (dgen ρ₁) = dgen ∆-seq₀ ρ₀ (dgen ρ₁)

  ∆-⊢idn₀-λ
    : ∀ {Γ Δ}
    → {f : Δ ⊒ Γ}
    → ∆-seq₀ ∆-idn₀ f T.≡ f
  ∆-⊢idn₀-λ {f = stop} = T.≡.idn
  ∆-⊢idn₀-λ {f = drop f} = T.≡.ap¹ drop_ ∆-⊢idn₀-λ
  ∆-⊢idn₀-λ {f = dgen f} = T.≡.ap¹ dgen_ ∆-⊢idn₀-λ

  ∆-⊢idn₀-ρ
    : ∀ {Γ Δ}
    → {f : Δ ⊒ Γ}
    → ∆-seq₀ f ∆-idn₀ T.≡ f
  ∆-⊢idn₀-ρ {f = stop} = T.≡.idn
  ∆-⊢idn₀-ρ {f = drop f} = T.≡.ap¹ drop_ ∆-⊢idn₀-ρ
  ∆-⊢idn₀-ρ {f = dgen f} = T.≡.ap¹ dgen_ ∆-⊢idn₀-ρ

  ∆-⊢seq₀-α
    : ∀ {Γ Δ Θ Ξ}
    → {f : Ξ ⊒ Θ}
    → {g : Θ ⊒ Δ}
    → {h : Δ ⊒ Γ}
    → ∆-seq₀ f (∆-seq₀ g h) T.≡ ∆-seq₀ (∆-seq₀ f g) h
  ∆-⊢seq₀-α {f = stop} {stop} {stop} = T.≡.idn
  ∆-⊢seq₀-α {f = drop f} {()} {stop}
  ∆-⊢seq₀-α {f = dgen f} {()} {stop}
  ∆-⊢seq₀-α {f = f} {g} {drop h} = T.≡.ap¹ drop_ (∆-⊢seq₀-α {h = h})
  ∆-⊢seq₀-α {f = f} {drop g} {dgen h} = ∆-⊢seq₀-α {h = h}
  ∆-⊢seq₀-α {f = drop f} {dgen g} {dgen h} = ∆-⊢seq₀-α {g = g}{dgen h}
  ∆-⊢seq₀-α {f = dgen f} {dgen g} {dgen h} = T.≡.ap¹ dgen_ (∆-⊢seq₀-α {f = f}{dgen g}{dgen h})

  ∆ : 𝔘 1 lzero
  ● [ ∆ ] = ∆₀
  ● (⇇ [ ∆ ] Δ Γ) = Δ ⊒ Γ
  ⇇ (⇇ [ ∆ ] x y) f g = 𝔊.ℼ[ f T.≡ g ]
  ↻ (⇇ [ ∆ ] x y) = T.≡.idn
  ↻ [ ∆ ] = ∆-idn₀
  seq₀ ∆ = ∆-seq₀
  inv₀ ∆ f {≜ = ()}
  seq₀* ∆ T.≡.idn T.≡.idn = T.≡.idn
  inv₀* ∆ α {≜ = ()}
  ⊢idn₀-λ ∆ = ∆-⊢idn₀-λ
  ⊢idn₀-ρ ∆ = ∆-⊢idn₀-ρ
  ⊢seq₀-α ∆ {f = f}{g}{h} = ∆-⊢seq₀-α {f = f}{g}{h}
  ⊢inv₀-λ ∆ {≜ = ()}
  ⊢inv₀-ρ ∆ {≜ = ()}
  idn₁ ∆ = T.≡.idn
  seq₁ ∆ T.≡.idn T.≡.idn = T.≡.idn
  inv₁ ∆ T.≡.idn = T.≡.idn

  ∆Std : Set _
  ∆Std = Psh ∆

  «∆Std» : 𝔘 _ _
  «∆Std» = «Psh» ∆
