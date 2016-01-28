{-# OPTIONS --without-K #-}

module Groupoids.Ordinary.Construction.Core where

open import Groupoids.Common
open import Groupoids.Ordinary.Isomorphism
open import Groupoids.Ordinary.Universe.Boot
open ≅

core
  : ∀ {n r}..{ℓ}
  → (A : 𝔘 1+[ n ] r ℓ)
  → 𝔘 1+[ n ] 0 _
● ([ core A ]) = ● [ A ]
● (⇇ ([ core A ]) a b) = A ⊢ a ≅ b
● (⇇ (⇇ ([ core A ]) a b) f g) = A ▸ 2 ⊢ » f ↝ » g
⇇ (⇇ (⇇ ([ core A ]) _ _) _ _) _ _ = 𝔊.𝟙↑
↻ (⇇ (⇇ ([ core A ]) _ _) _ _) = *
↻ (⇇ ([ core A ]) a b) = ↻ (A ▸ 1 ⊩ a ↝ b)
↻ ([ core A ]) = idn A
seq₀ (core A) = seq A
inv₀ (core A) f = inv A f
seq₀* (core A) = seq₀* A
inv₀* (core A) {f = f}{g = g} α =
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
⊢λ₀ (core A) = ⊢λ₀ A
⊢ρ₀ (core A) = ⊢ρ₀ A
⊢α₀ (core A) = ⊢α₀ A
⊢λ₀⁻¹ (core A) {f = f} = ⊢«» f
⊢ρ₀⁻¹ (core A) {f = f} = ⊢»« f
idn₁ (core A) = idn₁ A
seq₁ (core A) = seq₁ A
inv₁ (core A) = inv₁ A

[_]/≅ = core
{-# DISPLAY core = [_]/≅ #-}
