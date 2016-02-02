{-# OPTIONS --without-K #-}

module Groupoids.Ordinary.Monoidal.Exponential where

open import Groupoids.Common
open import Groupoids.Ordinary.Construction.Opposite
open import Groupoids.Ordinary.Homomorphism
open import Groupoids.Ordinary.Universe.Boot

open ⇒₀ public
  using (_⇒₀_)
  using (_⇔₀_)

module ⊢ where
  -- FIXME: these should be isomorphisms

  op⇒
    : ∀ ..{ℓ₀ ℓ₁}
    → {A : 𝔘 1 ℓ₀}
    → {B : 𝔘 1 ℓ₁}
    → Fun₀ (Op (A ⇒₀ B)) (Op A ⇒₀ Op B)
  ap₀₀ (ap₀₀ op⇒ F) = ap₀₀ F
  ap₀₁ (ap₀₀ op⇒ F) = ap₀₁ F
  ap₀₂ (ap₀₀ op⇒ F) = ap₀₂ F
  ⇒₀.⊢idn (ap₀₀ op⇒ F) = ⇒₀.⊢idn F
  ⇒₀.⊢seq (ap₀₀ op⇒ F) = ⇒₀.⊢seq F
  ⇒₀.⊢inv (ap₀₀ op⇒ F) = ⇒₀.⊢inv F
  ap₁₀ (ap₀₁ op⇒ α) = ap₁₀ α
  ap₁₁ (ap₀₁ (op⇒ {B = B}) α) f = inv₁ B (ap₁₁ α f)
  ap₀₂ op⇒ = T.⇒.idn
  ⇒₀.⊢idn (op⇒ {A = A}{B}) = ι λ _ → idn₁ B
  ⇒₀.⊢seq (op⇒ {A = A}{B}) = ι λ _ → idn₁ B
  ⇒₀.⊢inv (op⇒ {A = A}{B}) {()}

  op⇐
    : ∀ ..{ℓ₀ ℓ₁}
    → {A : 𝔘 1 ℓ₀}
    → {B : 𝔘 1 ℓ₁}
    → Fun₀ (Op A ⇒₀ Op B) (Op (A ⇒₀ B))
  ap₀₀ (ap₀₀ op⇐ F) = ap₀₀ F
  ap₀₁ (ap₀₀ op⇐ F) = ap₀₁ F
  ap₀₂ (ap₀₀ op⇐ F) = ap₀₂ F
  ⇒₀.⊢idn (ap₀₀ op⇐ F) = ⇒₀.⊢idn F
  ⇒₀.⊢seq (ap₀₀ op⇐ F) = ⇒₀.⊢seq F
  ⇒₀.⊢inv (ap₀₀ op⇐ F) = ⇒₀.⊢inv F
  ap₁₀ (ap₀₁ op⇐ α) = ap₁₀ α
  ap₁₁ (ap₀₁ (op⇐ {B = B}) α) f = inv₁ B (ap₁₁ α f)
  ap₀₂ op⇐ = T.⇒.idn
  ⇒₀.⊢idn (op⇐ {A = A}{B}) = ι λ _ → idn₁ B
  ⇒₀.⊢seq (op⇐ {A = A}{B}) = ι λ _ → idn₁ B
  ⇒₀.⊢inv (op⇐ {A = A}{B}) {()}
