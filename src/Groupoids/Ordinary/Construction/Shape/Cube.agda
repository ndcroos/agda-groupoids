{-# OPTIONS --without-K #-}

module Groupoids.Ordinary.Construction.Shape.Cube where

open import Groupoids.Common
open import Groupoids.Ordinary.Construction.Yoneda
open import Groupoids.Ordinary.Morphism.Hom.Boot
open import Groupoids.Ordinary.Universe
import Prelude.Bool
open import Prelude.Natural
open import Prelude.Vector

module Cube where
  infix 0 _⊒_
  infix 1 _▸*

  □₀ : Set
  □₀ = Nat

  open Prelude.Bool.𝟚↑ public
    renaming (𝟚 to Sign)
    renaming (ff to -)
    renaming (tt to +)
    using ()

  pattern ∅ = ze
  pattern _▸* Γ = su Γ

  data _⊒_ : □₀ → □₀ → Set where
    stop : ∅ ⊒ ∅
    lift_ : ∀ {Γ Δ} → Δ ⊒ Γ → Δ ▸* ⊒ Γ ▸*
    face[_]_ : ∀ {Γ Δ} (s : Sign) (ρ : Δ ⊒ Γ) → Δ ⊒ Γ ▸*
    dgen_ : ∀ {Γ Δ} → Δ ⊒ Γ → Δ ▸* ⊒ Γ

  pattern ε = stop
  pattern ⇑_ ρ = lift ρ
  pattern δ[_]_ s ρ = face[ s ] ρ
  pattern σ_ ρ = dgen ρ

  □-idn₀
    : ∀ {Γ}
    → Γ ⊒ Γ
  □-idn₀ {∅} = stop
  □-idn₀ {Γ ▸*} = lift □-idn₀

  □-seq₀
    : ∀ {Γ Δ Θ}
    → (f : Θ ⊒ Δ)
    → (g : Δ ⊒ Γ)
    → Θ ⊒ Γ
  □-seq₀ f (face[ s ] g) = face[ s ] □-seq₀ f g
  □-seq₀ (face[ s ] f) (dgen g) = □-seq₀ f g
  □-seq₀ (dgen f) g = dgen □-seq₀ f g
  □-seq₀ (lift f) (dgen g) = dgen □-seq₀ f g
  □-seq₀ (face[ s ] f) (lift g) = face[ s ] □-seq₀ f g
  □-seq₀ (lift f) (lift g) = lift □-seq₀ f g
  □-seq₀ f stop = f

  □-⊢idn₀-λ
    : ∀ {Δ Γ}
    → {f : Δ ⊒ Γ}
    → □-seq₀ □-idn₀ f T.≡ f
  □-⊢idn₀-λ {f = face[ s ] f} = T.≡.ap¹ (face[_]_ s) □-⊢idn₀-λ
  □-⊢idn₀-λ {f = dgen f} = T.≡.ap¹ dgen_ □-⊢idn₀-λ
  □-⊢idn₀-λ {f = lift f} = T.≡.ap¹ lift_ □-⊢idn₀-λ
  □-⊢idn₀-λ {f = stop} = T.≡.idn

  □-⊢idn₀-ρ
    : ∀ {Δ Γ}
    → {f : Δ ⊒ Γ}
    → □-seq₀ f □-idn₀ T.≡ f
  □-⊢idn₀-ρ {f = face[ s ] f} = T.≡.ap¹ (face[_]_ s) □-⊢idn₀-ρ
  □-⊢idn₀-ρ {Γ = ze} {dgen f} = T.≡.ap¹ dgen_ □-⊢idn₀-ρ
  □-⊢idn₀-ρ {Γ = su n} {dgen f} = T.≡.ap¹ dgen_ □-⊢idn₀-ρ
  □-⊢idn₀-ρ {f = lift f} = T.≡.ap¹ lift_ □-⊢idn₀-ρ
  □-⊢idn₀-ρ {f = stop} = T.≡.idn

  -- FIXME: simplify
  □-⊢seq₀-α
    : ∀ {m n o p}
    → {f : m ⊒ n}
    → {g : n ⊒ o}
    → {h : o ⊒ p}
    → □-seq₀ f (□-seq₀ g h) T.≡ □-seq₀ (□-seq₀ f g) h
  □-⊢seq₀-α {h = face[ s ] h} = T.≡.ap¹ (face[_]_ s) (□-⊢seq₀-α {h = h})
  □-⊢seq₀-α {g = face[ s ] g} {dgen h} = □-⊢seq₀-α {g = g}{h}
  □-⊢seq₀-α {f = face[ s ] f} {dgen g} {dgen h} = □-⊢seq₀-α {f = f}{g}{dgen h}
  □-⊢seq₀-α {f = dgen f} {dgen g} {dgen h} = T.≡.ap¹ dgen_ (□-⊢seq₀-α {f = f}{dgen g}{dgen h})
  □-⊢seq₀-α {f = lift f} {dgen g} {dgen h} = T.≡.ap¹ dgen_ (□-⊢seq₀-α {f = f}{g}{dgen h})
  □-⊢seq₀-α {f = face[ s ] f} {lift g} {dgen h} = □-⊢seq₀-α {f = f}{g}{h}
  □-⊢seq₀-α {f = dgen f} {lift g} {dgen h} = T.≡.ap¹ dgen_ (□-⊢seq₀-α {f = f}{lift g}{dgen h})
  □-⊢seq₀-α {f = lift f} {lift g} {dgen h} = T.≡.ap¹ dgen_ (□-⊢seq₀-α {f = f}{g}{h})
  □-⊢seq₀-α {g = face[ s ] g} {lift h} = T.≡.ap¹ (face[_]_ s) (□-⊢seq₀-α {g = g}{h})
  □-⊢seq₀-α {f = face[ s ] f} {dgen g} {lift h} = □-⊢seq₀-α {f = f}{g}{h = lift h}
  □-⊢seq₀-α {f = dgen f} {dgen g} {lift h} = T.≡.ap¹ dgen_ (□-⊢seq₀-α {f = f}{dgen g}{lift h})
  □-⊢seq₀-α {f = lift f} {dgen g} {lift h} = T.≡.ap¹ dgen_ (□-⊢seq₀-α {f = f}{g}{lift h})
  □-⊢seq₀-α {f = face[ s ] f} {lift g} {lift h} = T.≡.ap¹ (face[_]_ s) (□-⊢seq₀-α {f = f}{g}{h})
  □-⊢seq₀-α {f = dgen f} {lift g} {lift h} = T.≡.ap¹ dgen_ (□-⊢seq₀-α {f = f}{lift g}{lift h})
  □-⊢seq₀-α {f = lift f} {lift g} {lift h} = T.≡.ap¹ lift_ (□-⊢seq₀-α {f = f}{g}{h})
  □-⊢seq₀-α {f = face[ s ] f} {dgen g} {stop} = □-⊢seq₀-α {f = f}{g}{stop}
  □-⊢seq₀-α {f = dgen f} {dgen g} {stop} = T.≡.ap¹ dgen_ (□-⊢seq₀-α {f = f}{dgen g}{stop})
  □-⊢seq₀-α {f = lift f} {dgen g} {stop} = T.≡.ap¹ dgen_ (□-⊢seq₀-α {f = f}{g}{stop})
  □-⊢seq₀-α {f = dgen f} {stop} {stop} = T.≡.ap¹ dgen_ (□-⊢seq₀-α {f = f}{stop}{stop})
  □-⊢seq₀-α {f = stop} {stop} {stop} = T.≡.idn

  □ : 𝔘 1 lzero
  ● [ □ ] = □₀
  ● (⇇ [ □ ] Δ Γ) = Δ ⊒ Γ
  ⇇ (⇇ [ □ ] Δ Γ) f g = 𝔊.ℼ[ f T.≡ g ]
  idn₀ □ = □-idn₀
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

  open Yoneda

  □[-] : Hom₀ □ «□Std»
  □[-] = 𝓎[ □ ]
  {-# DISPLAY 𝓎[_] □ = □[-] #-}

  □[_]₀ : □₀ → □Std
  □[_]₀ = ap₀₀ □[-]
  {-# DISPLAY ap₀₀ □[-] Γ = □[ Γ ]₀ #-}

  □[_]₁
    : ∀ {Γ Δ}
    → Γ ⊒ Δ
    → «□Std» ▸ 1 ⊢ □[ Γ ]₀ ↝ □[ Δ ]₀
  □[_]₁ = ap₀₁ □[-]
  {-# DISPLAY ap₀₁ □[-] f = □[ f ]₁ #-}

  □[_]₂
    : ∀ {Γ Δ}
    → {f₀ f₁ : Γ ⊒ Δ}
    → □ ▸ 2 ⊢ f₀ ↝ f₁
    → «□Std» ▸ 2 ⊢ □[ f₀ ]₁ ↝ □[ f₁ ]₁
  □[_]₂ = ap₀₂ □[-]
  {-# DISPLAY ap₀₂ □[-] α = □[ α ]₂ #-}

  Cube : Nat → Set
  Cube = Vec Sign
  {-# DISPLAY Vec Sign n = Cube n #-}

  ⟦_⟧
    : ∀ {Γ Δ}
    → Γ ⊒ Δ
    → (Cube Γ → Cube Δ)
  ⟦ stop ⟧ c = c
  ⟦ lift ρ ⟧ (s ∷ c) = s ∷ ⟦ ρ ⟧ c
  ⟦ face[ s ] ρ ⟧ c = s ∷ ⟦ ρ ⟧ c
  ⟦ dgen ρ ⟧ (s ∷ c) = ⟦ ρ ⟧ c
