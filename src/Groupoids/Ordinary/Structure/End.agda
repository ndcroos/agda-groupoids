{-# OPTIONS --without-K #-}

module Groupoids.Ordinary.Structure.End where

open import Groupoids.Basis
open import Groupoids.Ordinary.Ambient.Cosmos.Tensor.Product.Indexed
open import Groupoids.Ordinary.Ambient.Morphism.Hom
open import Groupoids.Ordinary.Ambient.Universe
open import Groupoids.Ordinary.Structure.Dinatural
open import Groupoids.Ordinary.Structure.Profunctor
open import Groupoids.Ordinary.Structure.Wedge

module ∫↓ where
  record End {r}..{ℓ₀ ℓ₁}
    {A : 𝔘 r ℓ₀}
    {V : 𝔘 r ℓ₁}
    (F : ¬Hom₀[ V ] A A)
    : Set (lsuc (ℓ₀ ⊔ ℓ₁))
    where
    no-eta-equality
    field
      obj : V ▸
      map : ¬Δ F obj
  open End

  ∫↓
    : ∀ {r}..{ℓ₀ ℓ₁}
    → {A : 𝔘 1 ℓ₀}
    → (F : ¬Hom₀[ «Std» r (lsuc (ℓ₀ ⊔ ℓ₁)) ] A A)
    → End F
  obj (∫↓ F) =
    Π.[ _ ∋ x ] ap₀₀ F (x , x)
  ap₀₀ (⇏₁.ap₁δ₀ (map (∫↓ F)) a) k =
    k {a}
  ap₀₁ (⇏₁.ap₁δ₀ (map (∫↓ F)) a) α =
    α {a}
  ap₀₂ (⇏₁.ap₁δ₀ (map (∫↓ F)) a) 𝔣 =
    𝔣 {a}
  ⇒₀.⊢idn (⇏₁.ap₁δ₀ (map (∫↓ F)) a) =
    idn₁ (ap₀₀ F (a , a))
  ⇒₀.⊢seq (⇏₁.ap₁δ₀ (map (∫↓ F)) a) =
    idn₁ (ap₀₀ F (a , a))
  ⇒₀.⊢inv (⇏₁.ap₁δ₀ (map (∫↓ F)) a) =
    idn₁ (ap₀₀ F (a , a))
  ⇏₁.ap₁δ₁ (map (∫↓ F)) k =
    *
    -- FIXME: generalize to «Cat»
