{-# OPTIONS --without-K #-}

module Groupoids.Ordinary.Monoidal.Exponential where

open import Groupoids.Common
open import Groupoids.Ordinary.Construction.Opposite
open import Groupoids.Ordinary.Morphism.Hom
open import Groupoids.Ordinary.Universe.Boot

open ⇒₀ public
  using (_⇒₀_)
  using (_⇔₀_)

module ⇒ where
  module ⊢ where
    -- FIXME: these should be isomorphisms

    op⇒
      : ∀ {r}..{ℓ₀ ℓ₁}
      → {A : 𝔘 r ℓ₀}
      → {B : 𝔘 r ℓ₁}
      → Hom₀ Op[ A ⇒₀ B ] (Op[ A ] ⇒₀ Op[ B ])
    ap₀₀ (ap₀₀ op⇒ F) = ap₀₀ F
    ap₀₁ (ap₀₀ op⇒ F) = ap₀₁ F
    ap₀₂ (ap₀₀ op⇒ F) = ap₀₂ F
    ⇒₀.⊢idn (ap₀₀ op⇒ F) = ⇒₀.⊢idn F
    ⇒₀.⊢seq (ap₀₀ op⇒ F) = ⇒₀.⊢seq F
    ⇒₀.⊢inv (ap₀₀ op⇒ F) = ⇒₀.⊢inv F
    ap₁₀ (ap₀₁ op⇒ α) = ap₁₀ α
    ap₁₁ (ap₀₁ (op⇒ {B = B}) α) f = inv₁ B (ap₁₁ α f)
    ap₀₂ op⇒ = T.⇒.idn
    ⇒₀.⊢idn (op⇒ {B = B}) = ι λ _ → idn₁ B
    ⇒₀.⊢seq (op⇒ {B = B}) = ι λ _ → idn₁ B
    ⇒₀.⊢inv (op⇒ {B = B}) {T.≡.idn} =  ι λ _ → idn₁ B

    op⇐
      : ∀ {r}..{ℓ₀ ℓ₁}
      → {A : 𝔘 r ℓ₀}
      → {B : 𝔘 r ℓ₁}
      → Hom₀ (Op[ A ] ⇒₀ Op[ B ]) Op[ A ⇒₀ B ]
    ap₀₀ (ap₀₀ op⇐ F) = ap₀₀ F
    ap₀₁ (ap₀₀ op⇐ F) = ap₀₁ F
    ap₀₂ (ap₀₀ op⇐ F) = ap₀₂ F
    ⇒₀.⊢idn (ap₀₀ op⇐ F) = ⇒₀.⊢idn F
    ⇒₀.⊢seq (ap₀₀ op⇐ F) = ⇒₀.⊢seq F
    ⇒₀.⊢inv (ap₀₀ op⇐ F) = ⇒₀.⊢inv F
    ap₁₀ (ap₀₁ op⇐ α) = ap₁₀ α
    ap₁₁ (ap₀₁ (op⇐ {B = B}) α) f = inv₁ B (ap₁₁ α f)
    ap₀₂ op⇐ = T.⇒.idn
    ⇒₀.⊢idn (op⇐ {B = B}) = ι λ _ → idn₁ B
    ⇒₀.⊢seq (op⇐ {B = B}) = ι λ _ → idn₁ B
    ⇒₀.⊢inv (op⇐ {B = B}) {T.≡.idn} = ι λ _ → idn₁ B
