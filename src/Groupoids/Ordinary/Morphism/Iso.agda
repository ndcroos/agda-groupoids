{-# OPTIONS --without-K #-}

module Groupoids.Ordinary.Morphism.Iso where

open import Groupoids.Common
open import Groupoids.Ordinary.Universe.Boot

module ≅ where
  infix 0 Iso

  record Iso {r}..{ℓ} (A : 𝔘 r ℓ) (a b : A ▸) : Set ℓ where
    no-eta-equality
    field
      » : A ▸ 1 ⊢ a ↝ b
      « : A ▸ 1 ⊢ b ↝ a
      ⊢»« : A ▸ 2 ⊢ seq₀ A » « ↝ idn₀ A
      ⊢«» : A ▸ 2 ⊢ seq₀ A « » ↝ idn₀ A

    »[_] = »
    «[_] = «

    {-# DISPLAY » f = »[ f ] #-}
    {-# DISPLAY « f = «[ f ] #-}
  open Iso public

  syntax Iso A f g = A ⊢ f ≅ g

  module _ {r}..{ℓ} (A : 𝔘 r ℓ) where
    idn
      : ∀ {a}
      → A ⊢ a ≅ a
    » idn = idn₀ A
    « idn = idn₀ A
    ⊢»« idn = ⊢idn₀-λ A
    ⊢«» idn = ⊢idn₀-ρ A

    seq
      : ∀ {a b c}
      → (f : A ⊢ a ≅ b)
      → (g : A ⊢ b ≅ c)
      → A ⊢ a ≅ c
    » (seq f g) =
      (seq₀ A »[ f ] »[ g ])
    « (seq f g) =
      (seq₀ A «[ g ] «[ f ])
    ⊢»« (seq f g) =
      (seq₁ A
        (⊢seq₀-α A)
        (seq₁ A
          (seq₀*-λ A
            (seq₁ A
              (inv₁ A
                (⊢seq₀-α A))
            (seq₁ A
              (seq₀*-ρ A
                (⊢»« g))
            (⊢idn₀-ρ A))))
          (⊢»« f)))
    ⊢«» (seq f g) =
      seq₁ A
        (⊢seq₀-α A)
        (seq₁ A
          (seq₀*-λ A
            (seq₁ A
              (inv₁ A
                (⊢seq₀-α A))
              (seq₁ A
                (seq₀*-ρ A
                  (⊢«» f))
                (⊢idn₀-ρ A))))
          (⊢«» g))

    inv
      : ∀ {a b}
      → (f : A ⊢ a ≅ b)
      → A ⊢ b ≅ a
    » (inv f) = « f
    « (inv f) = » f
    ⊢»« (inv f) = ⊢«» f
    ⊢«» (inv f) = ⊢»« f

open ≅ public
  using (Iso)
