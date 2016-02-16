{-# OPTIONS --without-K #-}

module Groupoids.Ordinary.Morphism.Hom.Boot where

open import Groupoids.Common
open import Groupoids.Ordinary.Universe.Boot

module ⇒₀ where
  record Hom₀ {r}..{ℓ₀ ℓ₁}
    (A : 𝔘 r ℓ₀)
    (B : 𝔘 r ℓ₁)
    : Set (lsuc (ℓ₀ ⊔ ℓ₁))
    where
    no-eta-equality
    field
      ap₀₀
        : A ▸ → B ▸
      ap₀₁
        : {a b : A ▸}
        → (f : A ▸ 1 ⊢ a ↝ b)
        → B ▸ 1 ⊢ ap₀₀ a ↝ ap₀₀ b
      ap₀₂
        : {a b : A ▸}
        → {f₀ f₁ : A ▸ 1 ⊢ a ↝ b}
        → (α : A ▸ 2 ⊢ f₀ ↝ f₁)
        → B ▸ 2 ⊢ ap₀₁ f₀ ↝ ap₀₁ f₁
    field
      ⊢idn
        : {a : A ▸}
        → B ▸ 2 ⊢ ap₀₁ (idn₀ A {a}) ↝ idn₀ B {ap₀₀ a}
      ⊢seq
        : {a b c : A ▸}
        → {f : A ▸ 1 ⊢ a ↝ b}
        → {g : A ▸ 1 ⊢ b ↝ c}
        → B ▸ 2 ⊢ ap₀₁ (seq₀ A f g) ↝ seq₀ B (ap₀₁ f) (ap₀₁ g)
      ⊢inv
        : {≜ : r T.≡ ze}
        → {a b : A ▸}
        → {f : A ▸ 1 ⊢ a ↝ b}
        → B ▸ 2 ⊢ ap₀₁ (inv₀ A f {≜}) ↝ inv₀ B (ap₀₁ f) {≜}

  open Hom₀ public

  module _ where
    open Hom₀

    {-# DISPLAY ap₀₀ F a = F ⊙ a #-}
    {-# DISPLAY ap₀₁ F f = F ⊙ f #-}

  idn
    : ∀ {r}..{ℓ}
    → {A : 𝔘 r ℓ}
    → Hom₀ A A
  ap₀₀ idn a = a
  ap₀₁ idn f = f
  ap₀₂ idn α = α
  ⊢idn (idn {A = A}) = idn₁ A
  ⊢seq (idn {A = A}) = idn₁ A
  ⊢inv (idn {A = A}) = idn₁ A

  seq
    : ∀ {r}..{ℓ₀ ℓ₁ ℓ₂}
    → {A : 𝔘 r ℓ₀}
    → {B : 𝔘 r ℓ₁}
    → {C : 𝔘 r ℓ₂}
    → Hom₀ A B
    → Hom₀ B C
    → Hom₀ A C
  ap₀₀ (seq F G) a = ap₀₀ G (ap₀₀ F a)
  ap₀₁ (seq F G) f = ap₀₁ G (ap₀₁ F f)
  ap₀₂ (seq F G) α = ap₀₂ G (ap₀₂ F α)
  ⊢idn (seq {C = C} F G) =
    (seq₁ C
      (ap₀₂ G
        (⊢idn F))
      (⊢idn G))
  ⊢seq (seq {C = C} F G) =
    (seq₁ C
      (ap₀₂ G
        (⊢seq F))
      (⊢seq G))
  ⊢inv (seq {C = C} F G) {≜} =
    (seq₁ C
      (ap₀₂ G (⊢inv F {≜}))
      (⊢inv G {≜}))

  cmp
    : ∀ {r}..{ℓ₀ ℓ₁ ℓ₂}
    → {A : 𝔘 r ℓ₀}
    → {B : 𝔘 r ℓ₁}
    → {C : 𝔘 r ℓ₂}
    → Hom₀ B C
    → Hom₀ A B
    → Hom₀ A C
  cmp G F = seq F G

open ⇒₀ public
  using (Hom₀)
  using (ap₀₀)
  using (ap₀₁)
  using (ap₀₂)

module ⇒₁ where
  record Hom₁ {r}..{ℓ₀ ℓ₁}
    {A : 𝔘 r ℓ₀}
    {B : 𝔘 r ℓ₁}
    (F G : Hom₀ A B)
    : Set (lsuc (ℓ₀ ⊔ ℓ₁))
    where
    no-eta-equality
    open 𝔘
    open ⇒₀
    field
      ap₁₀
        : (a : A ▸)
        → B ▸ 1 ⊢ ap₀₀ F a ↝ ap₀₀ G a
      ap₁₁
        : {a b : A ▸}
        → (f : A ▸ 1 ⊢ a ↝ b)
        → B ▸ 2 ⊢ cmp₀ B (ap₁₀ b) (ap₀₁ F f) ↝ cmp₀ B (ap₀₁ G f) (ap₁₀ a)

  open Hom₁ public

  module _ where
    open Hom₁

    {-# DISPLAY ap₁₀ α a = α ⊙ a #-}
    {-# DISPLAY ap₁₁ α f = α ⊙ f #-}

  idn
    : ∀ {r}..{ℓ₀ ℓ₁}
    → {A : 𝔘 r ℓ₀}
    → {B : 𝔘 r ℓ₁}
    → {F : Hom₀ A B}
    → Hom₁ F F
  ap₁₀ (idn {B = B}) a =
    (idn₀ B)
  ap₁₁ (idn {B = B}{F = F}) f =
    (seq₁ B
      (⊢idn₀-ρ B)
      (inv₁ B (⊢idn₀-λ B)))

  seq
    : ∀ {r}..{ℓ₀ ℓ₁}
    → {A : 𝔘 r ℓ₀}
    → {B : 𝔘 r ℓ₁}
    → {F G H : Hom₀ A B}
    → (α : Hom₁ F G)
    → (β : Hom₁ G H)
    → Hom₁ F H
  ap₁₀ (seq {B = B} α β) a =
    (seq₀ B
      (ap₁₀ α a)
      (ap₁₀ β a))
  ap₁₁ (seq {B = B} α β) f =
    (seq₁ B
      (⊢seq₀-α B)
      (seq₁ B
        (seq₀*-λ B (ap₁₁ α f))
        (seq₁ B
          (inv₁ B (⊢seq₀-α B))
          (seq₁ B
            (seq₀*-ρ B (ap₁₁ β f))
            (⊢seq₀-α B)))))

  inv
    : ∀ {r}..{ℓ₀ ℓ₁}
    → {A : 𝔘 r ℓ₀}
    → {B : 𝔘 r ℓ₁}
    → {F G : Hom₀ A B}
    → (α : Hom₁ F G)
    → {≜ : r T.≡ 0}
    → Hom₁ G F
  ap₁₀ (inv {B = B} α {T.≡.idn}) a =
    inv₀ B (ap₁₀ α a) {T.≡.idn}
  ap₁₁ (inv {B = B}{F}{G} α {T.≡.idn}) {a}{b} f =
    (seq₁ B
      (seq₀*-λ B
        (seq₁ B
          (inv₁ B
            (⊢idn₀-λ B))
          (seq₀*-λ B
            (inv₁ B
              (⊢inv₀-λ B {f = ap₁₀ α a} {≜ = T.≡.idn})))))
      (seq₁ B
        (seq₀*-λ B
          (seq₁ B
            (inv₁ B
              (⊢seq₀-α B))
            (seq₀*-ρ B
              (inv₁ B
                (ap₁₁ α f)))))
        (seq₁ B
          (inv₁ B
            (⊢seq₀-α B))
          (seq₀*-ρ B
            (seq₁ B
              (inv₁ B
                (⊢seq₀-α B))
              (seq₁ B
                (seq₀*-ρ B
                  (⊢inv₀-ρ B))
                (⊢idn₀-ρ B)))))))

  cmp
    : ∀ {r}..{ℓ₀ ℓ₁}
    → {A : 𝔘 r ℓ₀}
    → {B : 𝔘 r ℓ₁}
    → {F G H : Hom₀ A B}
    → (β : Hom₁ G H)
    → (α : Hom₁ F G)
    → Hom₁ F H
  cmp β α = seq α β

open ⇒₁ public
  using (Hom₁)
  using (ap₁₀)
  using (ap₁₁)
