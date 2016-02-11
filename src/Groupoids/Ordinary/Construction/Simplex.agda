{-# OPTIONS --without-K #-}

module Groupoids.Ordinary.Construction.Simplex where

open import Groupoids.Common
open import Groupoids.Ordinary.Universe.Boot
open import Prelude.Natural

module Simplex where
  -- Augmented Simplex based on Sjoerd Visscher's Haskell encoding

  Δ₀ : Set
  Δ₀ = Nat

  data Δ₁ : Δ₀ → Δ₀ → Set where
    Z : Δ₁ ze ze
    Y_ : ∀ {m n} → Δ₁ m n → Δ₁ m (su n)
    X_ : ∀ {m n} → Δ₁ m (su n) → Δ₁ (su m) (su n)

  Δ-idn₀
    : ∀ {m}
    → Δ₁ m m
  Δ-idn₀ {ze} = Z
  Δ-idn₀ {su m} = X Y Δ-idn₀ {m}

  Δ-seq₀
    : ∀ {m n o}
    → (f : Δ₁ m n)
    → (g : Δ₁ n o)
    → Δ₁ m o
  Δ-seq₀ f (Y g) = Y Δ-seq₀ f g
  Δ-seq₀ Z g = g
  Δ-seq₀ (Y f) (X g) = Δ-seq₀ f g
  Δ-seq₀ (X f) (X g) = X Δ-seq₀ f (X g)

  Δ-⊢idn₀-λ
    : ∀ {m n}
    → {f : Δ₁ m n}
    → Δ-seq₀ Δ-idn₀ f T.≡ f
  Δ-⊢idn₀-λ {f = Z} = T.≡.idn
  Δ-⊢idn₀-λ {f = Y f} = T.≡.ap¹ Y_ Δ-⊢idn₀-λ
  Δ-⊢idn₀-λ {f = X f} = T.≡.ap¹ X_ Δ-⊢idn₀-λ

  Δ-⊢idn₀-ρ
    : ∀ {m n}
    → {f : Δ₁ m n}
    → Δ-seq₀ f Δ-idn₀ T.≡ f
  Δ-⊢idn₀-ρ {f = Z} = T.≡.idn
  Δ-⊢idn₀-ρ {f = Y f} = T.≡.ap¹ Y_ Δ-⊢idn₀-ρ
  Δ-⊢idn₀-ρ {f = X f} = T.≡.ap¹ X_ Δ-⊢idn₀-ρ

  Δ-⊢seq₀-α
    : ∀ {m n o p}
    → {f : Δ₁ m n}
    → {g : Δ₁ n o}
    → {h : Δ₁ o p}
    → Δ-seq₀ f (Δ-seq₀ g h) T.≡ Δ-seq₀ (Δ-seq₀ f g) h
  Δ-⊢seq₀-α {f = Z} {Z} {Z} = T.≡.idn
  Δ-⊢seq₀-α {f = Y f} {()} {Z}
  Δ-⊢seq₀-α {f = X f} {()} {Z}
  Δ-⊢seq₀-α {f = f} {g} {Y h} = T.≡.ap¹ Y_ (Δ-⊢seq₀-α {h = h})
  Δ-⊢seq₀-α {f = f} {Y g} {X h} = Δ-⊢seq₀-α {h = h}
  Δ-⊢seq₀-α {f = Y f} {X g} {X h} = Δ-⊢seq₀-α {g = g}{X h}
  Δ-⊢seq₀-α {f = X f} {X g} {X h} = T.≡.ap¹ X_ (Δ-⊢seq₀-α {f = f}{X g}{X h})

  Δ : 𝔘 1 lzero
  ● [ Δ ] = Δ₀
  ● (⇇ [ Δ ] x y) = Δ₁ x y
  ⇇ (⇇ [ Δ ] x y) f g = 𝔊.ℼ[ f T.≡ g ]
  ↻ (⇇ [ Δ ] x y) = T.≡.idn
  ↻ [ Δ ] = Δ-idn₀
  seq₀ Δ = Δ-seq₀
  inv₀ Δ f {≜ = ()}
  seq₀* Δ T.≡.idn T.≡.idn = T.≡.idn
  inv₀* Δ α {≜ = ()}
  ⊢idn₀-λ Δ = Δ-⊢idn₀-λ
  ⊢idn₀-ρ Δ = Δ-⊢idn₀-ρ
  ⊢seq₀-α Δ {f = f}{g}{h} = Δ-⊢seq₀-α {f = f}{g}{h}
  ⊢inv₀-λ Δ {≜ = ()}
  ⊢inv₀-ρ Δ {≜ = ()}
  idn₁ Δ = T.≡.idn
  seq₁ Δ T.≡.idn T.≡.idn = T.≡.idn
  inv₁ Δ T.≡.idn = T.≡.idn
