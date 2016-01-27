{-# OPTIONS --without-K #-}

module Groupoids.Core.Groupoid.Ordinary.Homomorphism.Boot where

open import Groupoids.Common
open import Groupoids.Core.Groupoid.Ordinary.Universe.Boot

module ⇒₀ where
  record Fun₀ {n r}..{ℓ₀ ℓ₁}
    (A : 𝔘 n r ℓ₀)
    (B : 𝔘 n r ℓ₁)
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

  open Fun₀ public

  module _ where
    open Fun₀

    {-# DISPLAY ap₀₀ F a = F ⊙ a #-}
    {-# DISPLAY ap₀₁ F f = F ⊙ f #-}

  idn
    : ∀ {n r}..{ℓ}
    → {A : 𝔘 n r ℓ}
    → Fun₀ A A
  ap₀₀ idn a = a
  ap₀₁ idn f = f
  ap₀₂ idn α = α
  ⊢idn (idn {A = A}) = idn₁ A
  ⊢seq (idn {A = A}) = idn₁ A

  seq
    : ∀ {n r}..{ℓ₀ ℓ₁ ℓ₂}
    → {A : 𝔘 n r ℓ₀}
    → {B : 𝔘 n r ℓ₁}
    → {C : 𝔘 n r ℓ₂}
    → Fun₀ A B
    → Fun₀ B C
    → Fun₀ A C
  ap₀₀ (seq F G) a = ap₀₀ G (ap₀₀ F a)
  ap₀₁ (seq F G) f = ap₀₁ G (ap₀₁ F f)
  ap₀₂ (seq F G) α = ap₀₂ G (ap₀₂ F α)
  ⊢idn (seq {C = C} F G) =
    (seq₁ C
      (ap₀₂ G
        (⊢idn F))
      (⊢idn G))
  ⊢seq (seq {C = C} G F) =
    (seq₁ C
      (ap₀₂ F
        (⊢seq G))
      (⊢seq F))

  cmp
    : ∀ {n r}..{ℓ₀ ℓ₁ ℓ₂}
    → {A : 𝔘 n r ℓ₀}
    → {B : 𝔘 n r ℓ₁}
    → {C : 𝔘 n r ℓ₂}
    → Fun₀ B C
    → Fun₀ A B
    → Fun₀ A C
  cmp G F = seq F G

open ⇒₀ public
  using (Fun₀)
  using (ap₀₀)
  using (ap₀₁)
  using (ap₀₂)

module ⇒₁ where
  record Fun₁ {n r}..{ℓ₀ ℓ₁}
    {A : 𝔘 n r ℓ₀}
    {B : 𝔘 n r ℓ₁}
    (F G : Fun₀ A B)
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

  open Fun₁ public

  module _ where
    open Fun₁

    {-# DISPLAY ap₁₀ α a = α ⊙ a #-}
    {-# DISPLAY ap₁₁ α f = α ⊙ f #-}

  idn
    : ∀ {n r}..{ℓ₀ ℓ₁}
    → {A : 𝔘 n r ℓ₀}
    → {B : 𝔘 n r ℓ₁}
    → {F : Fun₀ A B}
    → Fun₁ F F
  ap₁₀ (idn {B = B}) a =
    (idn₀ B)
  ap₁₁ (idn {B = B}{F = F}) f =
    (seq₁ B
      (⊢ρ₀ B)
      (inv₁ B (⊢λ₀ B)))

  seq
    : ∀ {n r}..{ℓ₀ ℓ₁}
    → {A : 𝔘 n r ℓ₀}
    → {B : 𝔘 n r ℓ₁}
    → {F G H : Fun₀ A B}
    → (α : Fun₁ F G)
    → (β : Fun₁ G H)
    → Fun₁ F H
  ap₁₀ (seq {B = B} α β) a =
    (seq₀ B
      (ap₁₀ α a)
      (ap₁₀ β a))
  ap₁₁ (seq {B = B} α β) f =
    (seq₁ B
      (⊢α₀ B)
      (seq₁ B
        (seq₀*λ B (ap₁₁ α f))
        (seq₁ B
          (inv₁ B (⊢α₀ B))
          (seq₁ B
            (seq₀*ρ B (ap₁₁ β f))
            (⊢α₀ B)))))

  inv
    : ∀ {n r}..{ℓ₀ ℓ₁}
    → {A : 𝔘 n r ℓ₀}
    → {B : 𝔘 n r ℓ₁}
    → {F G : Fun₀ A B}
    → (α : Fun₁ F G)
    → {≜ : r T.≡ 0}
    → Fun₁ G F
  ap₁₀ (inv {B = B} α {T.≡.idn}) a =
    inv₀ B (ap₁₀ α a) {T.≡.idn}
  ap₁₁ (inv {B = B}{F}{G} α {T.≡.idn}) {a}{b} f =
    (seq₁ B
      (seq₀*λ B
        (seq₁ B
          (inv₁ B
            (⊢λ₀ B))
          (seq₀*λ B
            (inv₁ B
              (⊢λ₀⁻¹ B {f = ap₁₀ α a} {≜ = T.≡.idn})))))
      (seq₁ B
        (seq₀*λ B
          (seq₁ B
            (inv₁ B
              (⊢α₀ B))
            (seq₀*ρ B
              (inv₁ B
                (ap₁₁ α f)))))
        (seq₁ B
          (inv₁ B
            (⊢α₀ B))
          (seq₀*ρ B
            (seq₁ B
              (inv₁ B
                (⊢α₀ B))
              (seq₁ B
                (seq₀*ρ B
                  (⊢ρ₀⁻¹ B))
                (⊢ρ₀ B)))))))

  cmp
    : ∀ {n r}..{ℓ₀ ℓ₁}
    → {A : 𝔘 n r ℓ₀}
    → {B : 𝔘 n r ℓ₁}
    → {F G H : Fun₀ A B}
    → (β : Fun₁ G H)
    → (α : Fun₁ F G)
    → Fun₁ F H
  cmp β α = seq α β

open ⇒₁ public
  using (Fun₁)
  using (ap₁₀)
  using (ap₁₁)
