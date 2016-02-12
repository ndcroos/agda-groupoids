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

  infix 0 _⊒_
  infix 1 _▸*

  -- □ = \Box
  □₀ : Set
  □₀ = Nat

  data Sign : Set where
    - + : Sign

  pattern ∅ = ze
  pattern _▸* Γ = su Γ

  data _⊒_ : □₀ → □₀ → Set where
    stop : ∅ ⊒ ∅
    keep_ : ∀ {Γ Δ} → Δ ⊒ Γ → Δ ▸* ⊒ Γ ▸*
    drop[_]_ : ∀ {Γ Δ} (s : Sign) (ρ : Δ ⊒ Γ) → Δ ⊒ Γ ▸*
    dgen_ : ∀ {Γ Δ} → Δ ⊒ Γ → Δ ▸* ⊒ Γ

  pattern ε = stop
  pattern ⇑_ ρ = keep ρ
  pattern δ[_]_ s ρ = drop[ s ] ρ
  pattern σ_ ρ = dgen ρ

  □-idn₀
    : ∀ {Γ}
    → Γ ⊒ Γ
  □-idn₀ {∅} = stop
  □-idn₀ {Γ ▸*} = keep □-idn₀

  □-seq₀
    : ∀ {Γ Δ Θ}
    → (f : Θ ⊒ Δ)
    → (g : Δ ⊒ Γ)
    → Θ ⊒ Γ
  □-seq₀ f (drop[ s ] g) = drop[ s ] □-seq₀ f g
  □-seq₀ (drop[ s ] f) (dgen g) = □-seq₀ f g
  □-seq₀ (dgen f) g = dgen □-seq₀ f g
  □-seq₀ (keep f) (dgen g) = dgen □-seq₀ f g
  □-seq₀ (drop[ s ] f) (keep g) = drop[ s ] □-seq₀ f g
  □-seq₀ (keep f) (keep g) = keep □-seq₀ f g
  □-seq₀ f stop = f

  □-⊢idn₀-λ
    : ∀ {Δ Γ}
    → {f : Δ ⊒ Γ}
    → □-seq₀ □-idn₀ f T.≡ f
  □-⊢idn₀-λ {f = drop[ s ] f} = T.≡.ap¹ (drop[_]_ s) □-⊢idn₀-λ
  □-⊢idn₀-λ {f = dgen f} = T.≡.ap¹ dgen_ □-⊢idn₀-λ
  □-⊢idn₀-λ {f = keep f} = T.≡.ap¹ keep_ □-⊢idn₀-λ
  □-⊢idn₀-λ {f = stop} = T.≡.idn

  □-⊢idn₀-ρ
    : ∀ {Δ Γ}
    → {f : Δ ⊒ Γ}
    → □-seq₀ f □-idn₀ T.≡ f
  □-⊢idn₀-ρ {f = drop[ s ] f} = T.≡.ap¹ (drop[_]_ s) □-⊢idn₀-ρ
  □-⊢idn₀-ρ {Γ = ze} {dgen f} = T.≡.ap¹ dgen_ □-⊢idn₀-ρ
  □-⊢idn₀-ρ {Γ = su n} {dgen f} = T.≡.ap¹ dgen_ □-⊢idn₀-ρ
  □-⊢idn₀-ρ {f = keep f} = T.≡.ap¹ keep_ □-⊢idn₀-ρ
  □-⊢idn₀-ρ {f = stop} = T.≡.idn

  -- FIXME: simplify
  □-⊢seq₀-α
    : ∀ {m n o p}
    → {f : m ⊒ n}
    → {g : n ⊒ o}
    → {h : o ⊒ p}
    → □-seq₀ f (□-seq₀ g h) T.≡ □-seq₀ (□-seq₀ f g) h
  □-⊢seq₀-α {h = drop[ s ] h} = T.≡.ap¹ (drop[_]_ s) (□-⊢seq₀-α {h = h})
  □-⊢seq₀-α {g = drop[ s ] g} {dgen h} = □-⊢seq₀-α {g = g}{h}
  □-⊢seq₀-α {f = drop[ s ] f} {dgen g} {dgen h} = □-⊢seq₀-α {f = f}{g}{dgen h}
  □-⊢seq₀-α {f = dgen f} {dgen g} {dgen h} = T.≡.ap¹ dgen_ (□-⊢seq₀-α {f = f}{dgen g}{dgen h})
  □-⊢seq₀-α {f = keep f} {dgen g} {dgen h} = T.≡.ap¹ dgen_ (□-⊢seq₀-α {f = f}{g}{dgen h})
  □-⊢seq₀-α {f = drop[ s ] f} {keep g} {dgen h} = □-⊢seq₀-α {f = f}{g}{h}
  □-⊢seq₀-α {f = dgen f} {keep g} {dgen h} = T.≡.ap¹ dgen_ (□-⊢seq₀-α {f = f}{keep g}{dgen h})
  □-⊢seq₀-α {f = keep f} {keep g} {dgen h} = T.≡.ap¹ dgen_ (□-⊢seq₀-α {f = f}{g}{h})
  □-⊢seq₀-α {g = drop[ s ] g} {keep h} = T.≡.ap¹ (drop[_]_ s) (□-⊢seq₀-α {g = g}{h})
  □-⊢seq₀-α {f = drop[ s ] f} {dgen g} {keep h} = □-⊢seq₀-α {f = f}{g}{h = keep h}
  □-⊢seq₀-α {f = dgen f} {dgen g} {keep h} = T.≡.ap¹ dgen_ (□-⊢seq₀-α {f = f}{dgen g}{keep h})
  □-⊢seq₀-α {f = keep f} {dgen g} {keep h} = T.≡.ap¹ dgen_ (□-⊢seq₀-α {f = f}{g}{keep h})
  □-⊢seq₀-α {f = drop[ s ] f} {keep g} {keep h} = T.≡.ap¹ (drop[_]_ s) (□-⊢seq₀-α {f = f}{g}{h})
  □-⊢seq₀-α {f = dgen f} {keep g} {keep h} = T.≡.ap¹ dgen_ (□-⊢seq₀-α {f = f}{keep g}{keep h})
  □-⊢seq₀-α {f = keep f} {keep g} {keep h} = T.≡.ap¹ keep_ (□-⊢seq₀-α {f = f}{g}{h})
  □-⊢seq₀-α {f = drop[ s ] f} {dgen g} {stop} = □-⊢seq₀-α {f = f}{g}{stop}
  □-⊢seq₀-α {f = dgen f} {dgen g} {stop} = T.≡.ap¹ dgen_ (□-⊢seq₀-α {f = f}{dgen g}{stop})
  □-⊢seq₀-α {f = keep f} {dgen g} {stop} = T.≡.ap¹ dgen_ (□-⊢seq₀-α {f = f}{g}{stop})
  □-⊢seq₀-α {f = dgen f} {stop} {stop} = T.≡.ap¹ dgen_ (□-⊢seq₀-α {f = f}{stop}{stop})
  □-⊢seq₀-α {f = stop} {stop} {stop} = T.≡.idn

  □ : 𝔘 1 lzero
  ● [ □ ] = □₀
  ● (⇇ [ □ ] Δ Γ) = Δ ⊒ Γ
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
