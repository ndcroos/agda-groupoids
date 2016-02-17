{-# OPTIONS --without-K #-}

module Groupoids.Ordinary.Construction.Arrow where

open import Groupoids.Common
open import Groupoids.Ordinary.Construction.Comma
open import Groupoids.Ordinary.Monoidal.Tensor.Product
open import Groupoids.Ordinary.Morphism.Fib
open import Groupoids.Ordinary.Morphism.Hom.Boot
open import Groupoids.Ordinary.Universe.Boot

module Arrow where
  _↗²
    : ∀ {r}..{ℓ}
    → (A : 𝔘 r ℓ)
    → 𝔘 r _
  A ↗² = ⇒₀.idn {A = A} ↓ ⇒₀.idn {A = A}

  points
    : ∀ {r}..{ℓ}
    → (A : 𝔘 r ℓ)
    → Hom₀ (A ↗²) (A ⊗ A)
  ap₀₀ (points A) =
    T.Σ.fst
  ap₀₁ (points A) =
    T.Σ.fst
  ap₀₂ (points A) =
    T.⊔⇑.π
  ⇒₀.⊢idn (points A) =
    idn₁ A , idn₁ A
  ⇒₀.⊢seq (points A) =
    idn₁ A , idn₁ A
  ⇒₀.⊢inv (points A) =
    idn₁ A , idn₁ A

  dom
    : ∀ {r}..{ℓ}
    → (A : 𝔘 r ℓ)
    → Hom₀ (A ↗²) A
  dom A = ⇒₀.seq (points A) ⊗.fst

  cod
    : ∀ {r}..{ℓ}
    → (A : 𝔘 r ℓ)
    → Hom₀ (A ↗²) A
  cod A = ⇒₀.seq (points A) ⊗.snd

open Arrow public
  using (_↗²)
