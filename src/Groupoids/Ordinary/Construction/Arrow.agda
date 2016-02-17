{-# OPTIONS --without-K #-}

module Groupoids.Ordinary.Construction.Arrow where

open import Groupoids.Common
open import Groupoids.Ordinary.Construction.Comma
open import Groupoids.Ordinary.Monoidal.Tensor.Product
open import Groupoids.Ordinary.Morphism.Fib
open import Groupoids.Ordinary.Morphism.Hom.Boot
open import Groupoids.Ordinary.Universe.Boot

module Arrow where
  ⇇∐[_]
    : ∀ {r}..{ℓ}
    → (A : 𝔘 r ℓ)
    → 𝔘 r _
  ⇇∐[ A ] = ⇒₀.idn {A = A} ↓ ⇒₀.idn {A = A}

  nodes
    : ∀ {r}..{ℓ}
    → (A : 𝔘 r ℓ)
    → Hom₀ ⇇∐[ A ] (A ⊗ A)
  ap₀₀ (nodes A) =
    T.Σ.fst
  ap₀₁ (nodes A) =
    T.Σ.fst
  ap₀₂ (nodes A) =
    T.⊔⇑.π
  ⇒₀.⊢idn (nodes A) =
    idn₁ A , idn₁ A
  ⇒₀.⊢seq (nodes A) =
    idn₁ A , idn₁ A
  ⇒₀.⊢inv (nodes A) =
    idn₁ A , idn₁ A

  dom
    : ∀ {r}..{ℓ}
    → (A : 𝔘 r ℓ)
    → Hom₀ ⇇∐[ A ] A
  dom A = ⇒₀.seq (nodes A) ⊗.fst

  cod
    : ∀ {r}..{ℓ}
    → (A : 𝔘 r ℓ)
    → Hom₀ ⇇∐[ A ] A
  cod A = ⇒₀.seq (nodes A) ⊗.snd

open Arrow public
  using (⇇∐[_])
