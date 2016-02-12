{-# OPTIONS --without-K #-}

module Groupoids.Ordinary.Construction.Simplex where

open import Groupoids.Common
open import Groupoids.Ordinary.Construction.Yoneda
open import Groupoids.Ordinary.Homomorphism
open import Groupoids.Ordinary.Universe
open import Prelude.Natural

module Simplex where
  -- * Simplex based on Sjoerd Visscher's Haskell encoding

  infix 0 _⊒_
  infix 0 _⊒+_
  infix 1 _▸*

  ∆₀ : Set
  ∆₀ = Nat

  pattern ∅ = ze
  pattern _▸* Γ = su Γ

  data _⊒_ : ∆₀ → ∆₀ → Set where
    stop : ∅ ⊒ ∅
    face_ : ∀ {Γ Δ} (ρ : Δ ⊒ Γ) → Δ ⊒ Γ ▸*
    dgen_ : ∀ {Γ Δ} (ρ : Δ ⊒ Γ ▸*) → Δ ▸* ⊒ Γ ▸*

  pattern ε = stop
  pattern δ_ ρ = face ρ
  pattern σ_ ρ = dgen ρ

  ∆-idn₀
    : ∀ {Γ}
    → Γ ⊒ Γ
  ∆-idn₀ {∅} = stop
  ∆-idn₀ {Γ ▸*} = dgen face ∆-idn₀

  ∆-seq₀
    : ∀ {Γ Δ Θ}
    → (f : Θ ⊒ Δ)
    → (g : Δ ⊒ Γ)
    → Θ ⊒ Γ
  ∆-seq₀ ρ₀ (face ρ₁) = face ∆-seq₀ ρ₀ ρ₁
  ∆-seq₀ stop ρ₁ = ρ₁
  ∆-seq₀ (face ρ₀) (dgen ρ₁) = ∆-seq₀ ρ₀ ρ₁
  ∆-seq₀ (dgen ρ₀) (dgen ρ₁) = dgen ∆-seq₀ ρ₀ (dgen ρ₁)

  ∆-⊢idn₀-λ
    : ∀ {Γ Δ}
    → {f : Δ ⊒ Γ}
    → ∆-seq₀ ∆-idn₀ f T.≡ f
  ∆-⊢idn₀-λ {f = stop} = T.≡.idn
  ∆-⊢idn₀-λ {f = face f} = T.≡.ap¹ face_ ∆-⊢idn₀-λ
  ∆-⊢idn₀-λ {f = dgen f} = T.≡.ap¹ dgen_ ∆-⊢idn₀-λ

  ∆-⊢idn₀-ρ
    : ∀ {Γ Δ}
    → {f : Δ ⊒ Γ}
    → ∆-seq₀ f ∆-idn₀ T.≡ f
  ∆-⊢idn₀-ρ {f = stop} = T.≡.idn
  ∆-⊢idn₀-ρ {f = face f} = T.≡.ap¹ face_ ∆-⊢idn₀-ρ
  ∆-⊢idn₀-ρ {f = dgen f} = T.≡.ap¹ dgen_ ∆-⊢idn₀-ρ

  ∆-⊢seq₀-α
    : ∀ {Γ Δ Θ Ξ}
    → {f : Ξ ⊒ Θ}
    → {g : Θ ⊒ Δ}
    → {h : Δ ⊒ Γ}
    → ∆-seq₀ f (∆-seq₀ g h) T.≡ ∆-seq₀ (∆-seq₀ f g) h
  ∆-⊢seq₀-α {f = stop} {stop} {stop} = T.≡.idn
  ∆-⊢seq₀-α {f = face f} {()} {stop}
  ∆-⊢seq₀-α {f = dgen f} {()} {stop}
  ∆-⊢seq₀-α {f = f} {g} {face h} = T.≡.ap¹ face_ (∆-⊢seq₀-α {h = h})
  ∆-⊢seq₀-α {f = f} {face g} {dgen h} = ∆-⊢seq₀-α {h = h}
  ∆-⊢seq₀-α {f = face f} {dgen g} {dgen h} = ∆-⊢seq₀-α {g = g}{dgen h}
  ∆-⊢seq₀-α {f = dgen f} {dgen g} {dgen h} = T.≡.ap¹ dgen_ (∆-⊢seq₀-α {f = f}{dgen g}{dgen h})

  ∆ : 𝔘 1 lzero
  ● [ ∆ ] = ∆₀
  ● (⇇ [ ∆ ] Δ Γ) = Δ ⊒ Γ
  ⇇ (⇇ [ ∆ ] Δ Γ) f g = 𝔊.ℼ[ f T.≡ g ]
  ↻ (⇇ [ ∆ ] Δ Γ) = T.≡.idn
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

  ∆+₀ : Set
  ∆+₀ = ∆₀

  _⊒+_ : ∆+₀ → ∆+₀ → Set
  Δ ⊒+ Γ = Δ ▸* ⊒ Γ ▸*

  ∆+ : 𝔘 1 lzero
  ● [ ∆+ ] = ∆+₀
  ● (⇇ [ ∆+ ] Δ Γ) = Δ ⊒+ Γ
  ⇇ (⇇ [ ∆+ ] Δ Γ) f g = 𝔊.ℼ[ f T.≡ g ]
  ↻ (⇇ [ ∆+ ] Δ Γ) = T.≡.idn
  ↻ [ ∆+ ] = ∆-idn₀
  seq₀ ∆+ = ∆-seq₀
  inv₀ ∆+ f {≜ = ()}
  seq₀* ∆+ T.≡.idn T.≡.idn = T.≡.idn
  inv₀* ∆+ α {≜ = ()}
  ⊢idn₀-λ ∆+ = ∆-⊢idn₀-λ
  ⊢idn₀-ρ ∆+ = ∆-⊢idn₀-ρ
  ⊢seq₀-α ∆+ {f = f}{g}{h} = ∆-⊢seq₀-α {f = f}{g}{h}
  ⊢inv₀-λ ∆+ {≜ = ()}
  ⊢inv₀-ρ ∆+ {≜ = ()}
  idn₁ ∆+ = T.≡.idn
  seq₁ ∆+ T.≡.idn T.≡.idn = T.≡.idn
  inv₁ ∆+ T.≡.idn = T.≡.idn

  ∆Std : Set _
  ∆Std = Psh ∆

  «∆Std» : 𝔘 _ _
  «∆Std» = «Psh» ∆

  ∆+Std : Set _
  ∆+Std = Psh ∆+

  «∆+Std» : 𝔘 _ _
  «∆+Std» = «Psh» ∆+

  open Yoneda

  ∆[-] : Fun₀ ∆ «∆Std»
  ∆[-] = 𝓎[ ∆ ]
  {-# DISPLAY 𝓎[_] ∆ = ∆[-] #-}

  ∆[_]₀ : ∆₀ → ∆Std
  ∆[_]₀ = ap₀₀ ∆[-]
  {-# DISPLAY ap₀₀ ∆[-] Γ = ∆[ Γ ]₀ #-}

  ∆[_]₁
    : ∀ {Γ Δ}
    → Γ ⊒ Δ
    → «∆Std» ▸ 1 ⊢ ∆[ Γ ]₀ ↝ ∆[ Δ ]₀
  ∆[_]₁ = ap₀₁ ∆[-]
  {-# DISPLAY ap₀₁ ∆[-] f = ∆[ f ]₁ #-}

  ∆[_]₂
    : ∀ {Γ Δ}
    → {f₀ f₁ : Γ ⊒ Δ}
    → ∆ ▸ 2 ⊢ f₀ ↝ f₁
    → «∆Std» ▸ 2 ⊢ ∆[ f₀ ]₁ ↝ ∆[ f₁ ]₁
  ∆[_]₂ = ap₀₂ ∆[-]
  {-# DISPLAY ap₀₂ ∆[-] α = ∆[ α ]₂ #-}

  ∆+[-] : Fun₀ ∆+ «∆+Std»
  ∆+[-] = 𝓎[ ∆+ ]
  {-# DISPLAY 𝓎[_] ∆+ = ∆+[-] #-}

  ∆+[_]₀ : ∆+₀ → ∆+Std
  ∆+[_]₀ = ap₀₀ ∆+[-]
  {-# DISPLAY ap₀₀ ∆+[-] Γ = ∆+[ Γ ]₀ #-}

  ∆+[_]₁
    : ∀ {Γ Δ}
    → Γ ⊒+ Δ
    → «∆+Std» ▸ 1 ⊢ ∆+[ Γ ]₀ ↝ ∆+[ Δ ]₀
  ∆+[_]₁ = ap₀₁ ∆+[-]
  {-# DISPLAY ap₀₁ ∆+[-] f = ∆+[ f ]₁ #-}

  ∆+[_]₂
    : ∀ {Γ Δ}
    → {f₀ f₁ : Γ ⊒+ Δ}
    → ∆+ ▸ 2 ⊢ f₀ ↝ f₁
    → «∆+Std» ▸ 2 ⊢ ∆+[ f₀ ]₁ ↝ ∆+[ f₁ ]₁
  ∆+[_]₂ = ap₀₂ ∆+[-]
  {-# DISPLAY ap₀₂ ∆+[-] α = ∆+[ α ]₂ #-}

  ⟦_⟧
    : ∀ {Γ Δ}
    → Γ ⊒ Δ
    → Fin Γ → Fin Δ
  ⟦ stop ⟧ i = i
  ⟦ face ρ ⟧ i = su ⟦ ρ ⟧ i
  ⟦ dgen ρ ⟧ ze = ze
  ⟦ dgen ρ ⟧ (su i) = ⟦ ρ ⟧ i
