{-# OPTIONS --without-K #-}

module Groupoids.Ordinary.Construction.Cube where

open import Groupoids.Common
open import Groupoids.Ordinary.Universe
open import Prelude.Natural

module Cube where
  -- * Cube based on Sjoerd Visscher's Haskell encoding
  --
  -- * I think this may be similar to how Crans describes it in the "Pasting
  -- * schemes" paper but I haven't read it yet.

  □₀ : Set
  □₀ = Nat

  data Sign : Set where
    M P : Sign

  data □₁ : □₀ → □₀ → Set where
    Z : □₁ ze ze
    S_ : ∀ {m n} → □₁ m n → □₁ (su m) (su n)
    Y[_]_ : ∀ {m n} (s : Sign) → □₁ m n → □₁ m (su n)
    X_ : ∀ {m n} → □₁ m n → □₁ (su m) n

  pattern δ[_]_ s f = Y[ s ] f
  pattern σ_ f = X f

  □-idn₀
    : ∀ {m}
    → □₁ m m
  □-idn₀ {ze} = Z
  □-idn₀ {su m} = S □-idn₀

  □-seq₀
    : ∀ {m n o}
    → (f : □₁ m n)
    → (g : □₁ n o)
    → □₁ m o
  □-seq₀ f (Y[ s ] g) = Y[ s ] □-seq₀ f g
  □-seq₀ (Y[ s ] f) (X g) = □-seq₀ f g
  □-seq₀ (X f) g = X □-seq₀ f g
  □-seq₀ (S f) (X g) = X □-seq₀ f g
  □-seq₀ (Y[ s ] f) (S g) = Y[ s ] □-seq₀ f g
  □-seq₀ (S f) (S g) = S □-seq₀ f g
  □-seq₀ f Z = f

  □-⊢idn₀-λ
    : ∀ {m n}
    → {f : □₁ m n}
    → □-seq₀ □-idn₀ f T.≡ f
  □-⊢idn₀-λ {f = Y[ s ] f} = T.≡.ap¹ (Y[_]_ s) □-⊢idn₀-λ
  □-⊢idn₀-λ {f = X f} = T.≡.ap¹ X_ □-⊢idn₀-λ
  □-⊢idn₀-λ {f = S f} = T.≡.ap¹ S_ □-⊢idn₀-λ
  □-⊢idn₀-λ {f = Z} = T.≡.idn

  □-⊢idn₀-ρ
    : ∀ {m n}
    → {f : □₁ m n}
    → □-seq₀ f □-idn₀ T.≡ f
  □-⊢idn₀-ρ {f = Y[ s ] f} = T.≡.ap¹ (Y[_]_ s) □-⊢idn₀-ρ
  □-⊢idn₀-ρ {n = ze} {X f} = T.≡.ap¹ X_ □-⊢idn₀-ρ
  □-⊢idn₀-ρ {n = su n} {X f} = T.≡.ap¹ X_ □-⊢idn₀-ρ
  □-⊢idn₀-ρ {f = S f} = T.≡.ap¹ S_ □-⊢idn₀-ρ
  □-⊢idn₀-ρ {f = Z} = T.≡.idn

  -- FIXME: simplify
  □-⊢seq₀-α
    : ∀ {m n o p}
    → {f : □₁ m n}
    → {g : □₁ n o}
    → {h : □₁ o p}
    → □-seq₀ f (□-seq₀ g h) T.≡ □-seq₀ (□-seq₀ f g) h
  □-⊢seq₀-α {h = Y[ s ] h} = T.≡.ap¹ (Y[_]_ s) (□-⊢seq₀-α {h = h})
  □-⊢seq₀-α {g = Y[ s ] g} {X h} = □-⊢seq₀-α {g = g}{h}
  □-⊢seq₀-α {f = Y[ s ] f} {X g} {X h} = □-⊢seq₀-α {f = f}{g}{X h}
  □-⊢seq₀-α {f = X f} {X g} {X h} = T.≡.ap¹ X_ (□-⊢seq₀-α {f = f}{X g}{X h})
  □-⊢seq₀-α {f = S f} {X g} {X h} = T.≡.ap¹ X_ (□-⊢seq₀-α {f = f}{g}{X h})
  □-⊢seq₀-α {f = Y[ s ] f} {S g} {X h} = □-⊢seq₀-α {f = f}{g}{h}
  □-⊢seq₀-α {f = X f} {S g} {X h} = T.≡.ap¹ X_ (□-⊢seq₀-α {f = f}{S g}{X h})
  □-⊢seq₀-α {f = S f} {S g} {X h} = T.≡.ap¹ X_ (□-⊢seq₀-α {f = f}{g}{h})
  □-⊢seq₀-α {g = Y[ s ] g} {S h} = T.≡.ap¹ (Y[_]_ s) (□-⊢seq₀-α {g = g}{h})
  □-⊢seq₀-α {f = Y[ s ] f} {X g} {S h} = □-⊢seq₀-α {f = f}{g}{h = S h}
  □-⊢seq₀-α {f = X f} {X g} {S h} = T.≡.ap¹ X_ (□-⊢seq₀-α {f = f}{X g}{S h})
  □-⊢seq₀-α {f = S f} {X g} {S h} = T.≡.ap¹ X_ (□-⊢seq₀-α {f = f}{g}{S h})
  □-⊢seq₀-α {f = Y[ s ] f} {S g} {S h} = T.≡.ap¹ (Y[_]_ s) (□-⊢seq₀-α {f = f}{g}{h})
  □-⊢seq₀-α {f = X f} {S g} {S h} = T.≡.ap¹ X_ (□-⊢seq₀-α {f = f}{S g}{S h})
  □-⊢seq₀-α {f = S f} {S g} {S h} = T.≡.ap¹ S_ (□-⊢seq₀-α {f = f}{g}{h})
  □-⊢seq₀-α {f = Y[ s ] f} {X g} {Z} = □-⊢seq₀-α {f = f}{g}{Z}
  □-⊢seq₀-α {f = X f} {X g} {Z} = T.≡.ap¹ X_ (□-⊢seq₀-α {f = f}{X g}{Z})
  □-⊢seq₀-α {f = S f} {X g} {Z} = T.≡.ap¹ X_ (□-⊢seq₀-α {f = f}{g}{Z})
  □-⊢seq₀-α {f = X f} {Z} {Z} = T.≡.ap¹ X_ (□-⊢seq₀-α {f = f}{Z}{Z})
  □-⊢seq₀-α {f = Z} {Z} {Z} = T.≡.idn

  □ : 𝔘 1 lzero
  ● [ □ ] = □₀
  ● (⇇ [ □ ] x y) = □₁ x y
  ⇇ (⇇ [ □ ] x y) f g = 𝔊.ℼ[ f T.≡ g ]
  ↻ (⇇ [ □ ] x y) = T.≡.idn
  ↻ [ □ ] = □-idn₀
  seq₀ □ = □-seq₀
  inv₀ □ f {≜ = ()}
  seq₀* □ T.≡.idn T.≡.idn = T.≡.idn
  inv₀* □ α {≜ = ()}
  ⊢idn₀-λ □ = □-⊢idn₀-λ
  ⊢idn₀-ρ □ = □-⊢idn₀-ρ
  ⊢seq₀-α □ {f = f}{g}{h} = □-⊢seq₀-α {f = f}{g}{h}
  ⊢inv₀-λ □ {≜ = ()}
  ⊢inv₀-ρ □ {≜ = ()}
  idn₁ □ = T.≡.idn
  seq₁ □ T.≡.idn T.≡.idn = T.≡.idn
  inv₁ □ T.≡.idn = T.≡.idn

  □Std : Set _
  □Std = Psh □

  «□Std» : 𝔘 _ _
  «□Std» = «Psh» □
