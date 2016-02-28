{-# OPTIONS --without-K #-}

module Groupoids.Ordinary.Structure.Dinatural where

open import Groupoids.Basis
open import Groupoids.Ordinary.Groupoid.Opposite
open import Groupoids.Ordinary.Ambient.Cosmos.Tensor.Product
open import Groupoids.Ordinary.Ambient.Morphism.Hom
open import Groupoids.Ordinary.Ambient.Universe.Boot
open import Groupoids.Ordinary.Structure.Profunctor

module ⇏₁ where
  record ¬Hom₁ {n r}..{ℓ₀ ℓ₁}
    {A : 𝔘 n r ℓ₀}
    {V : 𝔘 n r ℓ₁}
    (F G : ¬Hom₀[ V ] A A)
    : Set (lsuc (ℓ₀ ⊔ ℓ₁))
    where
    no-eta-equality
    open 𝔘
    open ⇒₀
    field
      ap₁δ₀
        : (a : A ▸)
        → (V ▸ 1 ⊢ ap₀₀ F (a , a) ↝ ap₀₀ G (a , a))
      ap₁δ₁
        : {x y : A ▸}
        → (f : A ▸ 1 ⊢ x ↝ y)
        → (V ▸ 2 ⊢ (seq₀ V
                    (ap₀₁ F (f , idn₀ A))
                    (seq₀ V
                      (ap₁δ₀ x)
                      (ap₀₁ G (idn₀ A , f))))
                 ↝ (seq₀ V
                     (ap₀₁ F (idn₀ A , f))
                     (seq₀ V
                       (ap₁δ₀ y)
                       (ap₀₁ G (f , idn₀ A)))))
  open ¬Hom₁ public
open ⇏₁ public
  using (¬Hom₁)
