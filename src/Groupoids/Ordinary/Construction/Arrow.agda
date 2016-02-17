{-# OPTIONS --without-K #-}

module Groupoids.Ordinary.Construction.Arrow where

open import Groupoids.Common
open import Groupoids.Ordinary.Construction.Comma
open import Groupoids.Ordinary.Morphism.Fib
open import Groupoids.Ordinary.Morphism.Hom.Boot
open import Groupoids.Ordinary.Universe.Boot

module Arrow where
  _↗²
    : ∀ {r}..{ℓ}
    → (A : 𝔘 r ℓ)
    → 𝔘 r _
  A ↗² = ⇒₀.idn {A = A} ↓ ⇒₀.idn {A = A}

  cod
    : ∀ {r}..{ℓ}
    → (A : 𝔘 r ℓ)
    → Hom₀ (A ↗²) A
  ap₀₀ (cod A)
    ((↑ , ↓) T.▸ f)
    =
    ↓
  ap₀₁ (cod A)
    {(↖ , ↙) T.▸ ↖←↙}
    {(↗ , ↘) T.▸ ↗→↘}
    ((↖↑↗ , ↙↓↘) T.▸ ⇙)
    =
    ↙↓↘
  ap₀₂ (cod A)
    -- {(↖ , ↙) T.▸ ↖←↙}
    -- {(↗ , ↘) T.▸ ↗→↘}
    -- {(↖↑↗₀ , ↙↓↘₀) T.▸ ⇙₀}
    -- {(↖↑↗₁ , ↙↓↘₁) T.▸ ⇙₁}
    (ι (α₀ , α₁))
    =
    α₁
  ⇒₀.⊢idn (cod A) =
    idn₁ A
  ⇒₀.⊢seq (cod A) =
    idn₁ A
  ⇒₀.⊢inv (cod A) =
    idn₁ A

open Arrow public
  using (_↗²)
