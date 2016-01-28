{-# OPTIONS --without-K #-}

module Groupoids.Core.Groupoid.Ordinary.Construction.Core where

open import Groupoids.Common
open import Groupoids.Core.Groupoid.Ordinary.Isomorphism
open import Groupoids.Core.Groupoid.Ordinary.Universe.Boot

module _ where
  open ≅

  [_]/≅
    : ∀ {n r}..{ℓ}
    → (A : 𝔘 1+[ n ] r ℓ)
    → 𝔘 1+[ n ] 0 _
  ● ([ [ A ]/≅ ]) = ● [ A ]
  ● (⇇ ([ [ A ]/≅ ]) a b) = A ⊢ a ≅ b
  ● (⇇ (⇇ ([ [ A ]/≅ ]) a b) f g) = A ▸ 2 ⊢ » f ↝ » g
  ⇇ (⇇ (⇇ ([ [ A ]/≅ ]) _ _) _ _) _ _ = 𝔊.𝟙↑
  ↻ (⇇ (⇇ ([ [ A ]/≅ ]) _ _) _ _) = *
  ↻ (⇇ ([ [ A ]/≅ ]) a b) = ↻ (A ▸ 1 ⊩ a ↝ b)
  ↻ ([ [ A ]/≅ ]) = idn A
  idn₀ [ A ]/≅ = idn A
  seq₀ [ A ]/≅ = seq A
  inv₀ [ A ]/≅ f = inv A f
  seq₀* [ A ]/≅ = seq₀* A
  inv₀* [ A ]/≅ {f = f}{g = g} α =
    (seq₁ A
      (inv₁ A
        (⊢ρ₀ A))
      (seq₁ A
        (seq₀*ρ A
          (inv₁ A
            (⊢»« g)))
        (seq₁ A
          (⊢α₀ A)
          (seq₁ A
            (seq₀* A
              (seq₁ A
                (seq₀*ρ A
                  (inv₁ A α))
                (⊢«» f))
              (idn₁ A))
            (⊢λ₀ A)))))
  ⊢λ₀ [ A ]/≅ = ⊢λ₀ A
  ⊢ρ₀ [ A ]/≅ = ⊢ρ₀ A
  ⊢α₀ [ A ]/≅ = ⊢α₀ A
  ⊢λ₀⁻¹ [ A ]/≅ {f = f} = ⊢«» f
  ⊢ρ₀⁻¹ [ A ]/≅ {f = f} = ⊢»« f
  idn₁ [ A ]/≅ = idn₁ A
  seq₁ [ A ]/≅ = seq₁ A
  inv₁ [ A ]/≅ = inv₁ A
