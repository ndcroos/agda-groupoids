{-# OPTIONS --without-K #-}

module Groupoids.Ordinary.Groupoid.Core where

open import Groupoids.Basis
open import Groupoids.Ordinary.Ambient.Morphism.Iso
open import Groupoids.Ordinary.Ambient.Universe.Boot
open ≅

core
  : ∀ {n r}..{ℓ}
  → (A : 𝔘 n r ℓ)
  → 𝔘 n 0 _
● ([ core A ]) = ● [ A ]
● (⇇ ([ core A ]) a b) = A ⊢ a ≅ b
● (⇇ (⇇ ([ core A ]) a b) f g) = A ▸ 2 ⊢ » f ↝ » g
⇇ (⇇ (⇇ ([ core A ]) _ _) _ _) _ _ = 𝔊.𝟙↑
idn₀ (core A) = idn A
seq₀ (core A) = seq A
inv₀ (core A) f = inv A f
seq₀* (core A) = seq₀* A
inv₀* (core A) {f = f}{g = g} α =
  (seq₁ A
    (inv₁ A
      (⊢idn₀-ρ A))
    (seq₁ A
      (seq₀*-ρ A
        (inv₁ A
          (⊢»« g)))
      (seq₁ A
        (⊢seq₀-α A)
        (seq₁ A
          (seq₀* A
            (seq₁ A
              (seq₀*-ρ A
                (inv₁ A α))
              (⊢«» f))
            (idn₁ A))
          (⊢idn₀-λ A)))))
⊢idn₀-λ (core A) = ⊢idn₀-λ A
⊢idn₀-ρ (core A) = ⊢idn₀-ρ A
⊢seq₀-α (core A) = ⊢seq₀-α A
⊢inv₀-λ (core A) {f = f} = ⊢«» f
⊢inv₀-ρ (core A) {f = f} = ⊢»« f
idn₁ (core A) = idn₁ A
seq₁ (core A) = seq₁ A
inv₁ (core A) = inv₁ A

[_]/≅ = core
{-# DISPLAY core = [_]/≅ #-}
