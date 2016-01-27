{-# OPTIONS --without-K #-}

module Groupoids.Core.Groupoid.Ordinary.Isomorphism where

open import Groupoids.Common
open import Groupoids.Core.Groupoid.Ordinary.Universe.Boot

module ≅ where
  infix 0 _⊢_≅_

  record _⊢_≅_ {n r}..{ℓ} (A : 𝔘 n r ℓ) (a b : A ▸) : Set ℓ where
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
  open _⊢_≅_ public

  module _ {n r}..{ℓ} (A : 𝔘 n r ℓ) where
    idn
      : ∀ {a}
      → A ⊢ a ≅ a
    » idn = idn₀ A
    « idn = idn₀ A
    ⊢»« idn = ⊢λ₀ A
    ⊢«» idn = ⊢ρ₀ A

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
        (⊢α₀ A)
        (seq₁ A
          (seq₀*λ A
            (seq₁ A
              (inv₁ A
                (⊢α₀ A))
            (seq₁ A
              (seq₀*ρ A
                (⊢»« g))
            (⊢ρ₀ A))))
          (⊢»« f)))
    ⊢«» (seq f g) =
      seq₁ A
        (⊢α₀ A)
        (seq₁ A
          (seq₀*λ A
            (seq₁ A
              (inv₁ A
                (⊢α₀ A))
              (seq₁ A
                (seq₀*ρ A
                  (⊢«» f))
                (⊢ρ₀ A))))
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
  using (_⊢_≅_)
