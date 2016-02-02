{-# OPTIONS --without-K #-}

module Groupoids.Ordinary.Monoidal.Diagonal where

open import Groupoids.Common
open import Groupoids.Ordinary.Homomorphism.Boot
open import Groupoids.Ordinary.Universe.Boot

module Δ where
  open ⇒₀

  ʲ[_]
    : ∀ {r}..{ℓ₀ ℓ₁}
    → {X : 𝔘 r ℓ₀}
    → {A : 𝔘 r ℓ₁}
    → (a : A ▸)
    → Fun₀ X A
  ap₀₀ ʲ[ a ] = T.Δ.ʲ[ a ]
  ap₀₁ (ʲ[_] {A = A} a) = T.Δ.ʲ[ idn₀ A ]
  ap₀₂ (ʲ[_] {A = A} a) = T.Δ.ʲ[ idn₁ A ]
  ⊢idn (ʲ[_] {A = A} a) = idn₁ A
  ⊢seq (ʲ[_] {A = A} a) = inv₁ A (⊢idn₀-λ A)
  ⊢inv (ʲ[_] {A = A} a) {≜} =
    (seq₁ A
      (inv₁ A (⊢inv₀-λ A {≜ = ≜}))
      (⊢idn₀-ρ A))

  ʲ[_↦_]
    : ∀ {r}..{ℓ₀ ℓ₁}
    → (X : 𝔘 r ℓ₀)
    → {A : 𝔘 r ℓ₁}
    → (a : A ▸)
    → Fun₀ X A
  ʲ[ X ↦ a ] = ʲ[ a ]
