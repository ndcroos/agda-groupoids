{-# OPTIONS --without-K #-}

module Groupoids.Groupoid where

open import Globular
open 𝔊
  hiding (_▸_)

infix 0 ⊢_
infix 1 _↝_
infixr 3 _⊙_

pattern ⊢_ x = x

-- miscellaneous utilities

nat∞ : ∀ {n} → Fin n → ℕ∞
nat∞ (ze) = ze
nat∞ (su i) = su (ℕ∞.ι (nat∞ i))

-- display utilities

record Display : Set where
  no-eta-equality

_↝_ : Display
_↝_ = record {}

_⊙_ : Display
_⊙_ = record {}

-- At higher edges, displaying the globular quiver A makes the goals harder to
-- read. We can hide it with the following display rules. For example:
--
-- f : node (edge A a b)
--
-- will be displayed as:
--
-- f : ⊢ a ↝ b
--
-- Similarly, for a quiver map F : Map A B, the following term
--
-- f : edge A a b
-- ap· (ap* F) f : edge B (ap· F a) (ap· F b)
--
-- will be displayed as
--
-- * F · f : ⊢ F · a ↝ F · b

module _ where
  open Gph
  {-# DISPLAY ● A = ⊢ A #-}
  {-# DISPLAY ⇇ A a b = a ↝ b #-}

module _ where
  open Map
  {-# DISPLAY ap* F = * F #-}

module Cell {n r}..{ℓ} (A : Gph n r ℓ) where
  infix 0 _⊢_↝_

  · : Set _
  · = cell A 0

  _⊢_↝_ : (i : Nat) → Glob A i [·]
  _⊢_↝_ = cell A

pattern 1+ n =     su (ℕ∞.ι n)
pattern 2+ n = 1+ (su (ℕ∞.ι n))

module Alg where
  record Alg n (r : Fin 2) ..ℓ : Set (lsuc ℓ) where
    no-eta-equality
    infix 3 [_]
    field
      [_] : Gph (2+ n) (nat∞ r) ℓ
    complex = [_]
    field
      lvl : Type complex (2+ n)
    open Gph public
    open Cell complex
    field
      idn₀
        : {a : ·}
        → 1 ⊢ a ↝ a
      seq₀
        : {a b c : ·}
        → (f : 1 ⊢ a ↝ b)
        → (g : 1 ⊢ b ↝ c)
        → 1 ⊢ a ↝ c
      inv₀
        : {a b : ·}
        → (f : 1 ⊢ a ↝ b)
        → {≜ : r T.≡ ze}
        → 1 ⊢ b ↝ a
    field
      seq₀*
        : {a b c : ·}
        → {f₀ f₁ : 1 ⊢ a ↝ b}
        → {g₀ g₁ : 1 ⊢ b ↝ c}
        → (α : 2 ⊢ f₀ ↝ f₁)
        → (β : 2 ⊢ g₀ ↝ g₁)
        → 2 ⊢ seq₀ f₀ g₀ ↝ seq₀ f₁ g₁
      inv₀*
        : {a b : ·}
        → {f g : 1 ⊢ a ↝ b}
        → (α : 2 ⊢ f ↝ g)
        → {≜ : r T.≡ ze}
        → 2 ⊢ inv₀ f {≜} ↝ inv₀ g {≜}
    field
      ⊢λ₀
        : {a b : ·}
        → {f : 1 ⊢ a ↝ b}
        → 2 ⊢ seq₀ idn₀ f ↝ f
      ⊢ρ₀
        : {a b : ·}
        → {f : 1 ⊢ a ↝ b}
        → 2 ⊢ seq₀ f idn₀ ↝ f
      ⊢α₀
        : {a b c d : ·}
        → {f : 1 ⊢ a ↝ b}
        → {g : 1 ⊢ b ↝ c}
        → {h : 1 ⊢ c ↝ d}
        → 2 ⊢ seq₀ f (seq₀ g h) ↝ seq₀ (seq₀ f g) h
      ⊢λ₀⁻¹
        : {a b : ·}
        → {f : 1 ⊢ a ↝ b}
        → {≜ : r T.≡ ze}
        → 2 ⊢ seq₀ (inv₀ f {≜}) f ↝ idn₀
      ⊢ρ₀⁻¹
        : {a b : ·}
        → {f : 1 ⊢ a ↝ b}
        → {≜ : r T.≡ ze}
        → 2 ⊢ seq₀ f (inv₀ f {≜}) ↝ idn₀
    field
      idn₁
        : {a b : ·}
        → {f : 1 ⊢ a ↝ b}
        → 2 ⊢ f ↝ f
      seq₁
        : {a b : ·}
        → {f g h : 1 ⊢ a ↝ b}
        → (α : 2 ⊢ f ↝ g)
        → (β : 2 ⊢ g ↝ h)
        → 2 ⊢ f ↝ h
      inv₁
        : {a b : ·}
        → {f g : 1 ⊢ a ↝ b}
        → (α : 2 ⊢ f ↝ g)
        → 2 ⊢ g ↝ f

    seq₀*λ
      : {a b c : ·}
      → {f₀ f₁ : 1 ⊢ a ↝ b}
      → {g : 1 ⊢ b ↝ c}
      → (α : 2 ⊢ f₀ ↝ f₁)
      → 2 ⊢ seq₀ f₀ g ↝ seq₀ f₁ g
    seq₀*λ α = seq₀* α idn₁

    seq₀*ρ
      : {a b c : ·}
      → {f : 1 ⊢ a ↝ b}
      → {g₀ g₁ : 1 ⊢ b ↝ c}
      → (β : 2 ⊢ g₀ ↝ g₁)
      → 2 ⊢ seq₀ f g₀ ↝ seq₀ f g₁
    seq₀*ρ β = seq₀* idn₁ β

    cmp₀
      : {a b c : ·}
      → (g : 1 ⊢ b ↝ c)
      → (f : 1 ⊢ a ↝ b)
      → 1 ⊢ a ↝ c
    cmp₀ g f = seq₀ f g

    cmp₁
      : {a b : ·}
      → {f g h : 1 ⊢ a ↝ b}
      → (β : 2 ⊢ g ↝ h)
      → (α : 2 ⊢ f ↝ g)
      → 2 ⊢ f ↝ h
    cmp₁ β α = seq₁ α β

    cmp₀*
      : {a b c : ·}
      → {f₀ f₁ : 1 ⊢ a ↝ b}
      → {g₀ g₁ : 1 ⊢ b ↝ c}
      → (β : 2 ⊢ g₀ ↝ g₁)
      → (α : 2 ⊢ f₀ ↝ f₁)
      → 2 ⊢ cmp₀ g₀ f₀ ↝ cmp₀ g₁ f₁
    cmp₀* β α = seq₀* α β

    cmp₀*λ
      : {a b c : ·}
      → {f₀ f₁ : 1 ⊢ a ↝ b}
      → {g : 1 ⊢ b ↝ c}
      → (α : 2 ⊢ f₀ ↝ f₁)
      → 2 ⊢ cmp₀ g f₀ ↝ cmp₀ g f₁
    cmp₀*λ α = cmp₀* idn₁ α

    cmp₀*ρ
      : {a b c : ·}
      → {f : 1 ⊢ a ↝ b}
      → {g₀ g₁ : 1 ⊢ b ↝ c}
      → (β : 2 ⊢ g₀ ↝ g₁)
      → 2 ⊢ cmp₀ g₀ f ↝ cmp₀ g₁ f
    cmp₀*ρ β = cmp₀* β idn₁

    infix 0 _▸
    infix 0 _▸_⊢_↝_

    _▸ : Set _
    _▸ = cell complex 0

    _▸_⊢_↝_ : (i : Nat) → Glob complex i [·]
    _▸_⊢_↝_ = cell complex

    _▸_⊩_↝_ : (i : Nat) → Glob complex i [*]
    _▸_⊩_↝_ = quiver complex

    {-# DISPLAY cell A i a b = A ▸ i ⊢ a ↝ b #-}
    {-# DISPLAY cell A 0 = A ▸ #-}

  open Alg public

  -- display rules for category operations

  module _ where
    infix 2 _⟓*_
    infix 2 _⟓_
    infix 2 _⟔_
    infix 4 _⁻¹

    _⟓_ : Display
    _⟓_ = record {}

    _⟔_ : Display
    _⟔_ = record {}

    _⁻¹ : Display
    _⁻¹ = record {}

    _⟓*_ : Display
    _⟓*_ = record {}

    _⁻¹* : Display
    _⁻¹* = record {}

    open Alg
    open Cell

    {-# DISPLAY · A = A ▸ #-}
    {-# DISPLAY _⊢_↝_ A i a b = A ▸ i ⊢ a ↝ b #-}
    {-# DISPLAY _⊢_↝_ A i {a}{b} f g = A ▸ i ⊢ f ↝ g #-}
    {-# DISPLAY _⊢_↝_ A i {a}{b}{f}{g} α β = A ▸ i ⊢ α ↝ β #-}

    {-# DISPLAY idn₀ A = ↻ #-}
    {-# DISPLAY idn₁ A = ↻ #-}

    {-# DISPLAY seq₀ A f g = f ⟓ g #-}
    {-# DISPLAY seq₁ A α β = α ⟓ β #-}

    {-# DISPLAY cmp₀ A g f = g ⟔ f #-}
    {-# DISPLAY cmp₁ A β α = β ⟔ α #-}

    {-# DISPLAY inv₀ A f = f ⁻¹ #-}
    {-# DISPLAY inv₁ A α = α ⁻¹ #-}

    {-# DISPLAY seq₀* A β α = α ⟓* β #-}
    {-# DISPLAY inv₀* A α = α ⁻¹* #-}

open Alg
  hiding (module Alg)

module ⇒₀ where
  open Alg

  record Fun₀ {n r}..{ℓ₀ ℓ₁}
    (A : Alg n r ℓ₀)
    (B : Alg n r ℓ₁)
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
    → {A : Alg n r ℓ}
    → Fun₀ A A
  ap₀₀ idn a = a
  ap₀₁ idn f = f
  ap₀₂ idn α = α
  ⊢idn (idn {A = A}) = idn₁ A
  ⊢seq (idn {A = A}) = idn₁ A

  seq
    : ∀ {n r}..{ℓ₀ ℓ₁ ℓ₂}
    → {A : Alg n r ℓ₀}
    → {B : Alg n r ℓ₁}
    → {C : Alg n r ℓ₂}
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
    → {A : Alg n r ℓ₀}
    → {B : Alg n r ℓ₁}
    → {C : Alg n r ℓ₂}
    → Fun₀ B C
    → Fun₀ A B
    → Fun₀ A C
  cmp G F = seq F G

open ⇒₀
  using (Fun₀)
  using (ap₀₀)
  using (ap₀₁)
  using (ap₀₂)

module ⇒₁ where
  record Fun₁ {n r}..{ℓ₀ ℓ₁}
    {A : Alg n r ℓ₀}
    {B : Alg n r ℓ₁}
    (F G : Fun₀ A B)
    : Set (lsuc (ℓ₀ ⊔ ℓ₁))
    where
    no-eta-equality
    open Alg
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
    → {A : Alg n r ℓ₀}
    → {B : Alg n r ℓ₁}
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
    → {A : Alg n r ℓ₀}
    → {B : Alg n r ℓ₁}
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
    → {A : Alg n r ℓ₀}
    → {B : Alg n r ℓ₁}
    → {F G : Fun₀ A B}
    → (α : Fun₁ F G)
    → {≜ : r T.≡ ze}
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
    → {A : Alg n r ℓ₀}
    → {B : Alg n r ℓ₁}
    → {F G H : Fun₀ A B}
    → (β : Fun₁ G H)
    → (α : Fun₁ F G)
    → Fun₁ F H
  cmp β α = seq α β

open ⇒₁
  using (Fun₁)
  using (ap₁₀)
  using (ap₁₁)

module ≅ where
  infix 0 _⊢_≅_

  record _⊢_≅_ {n r}..{ℓ} (A : Alg n r ℓ) (a b : A ▸) : Set ℓ where
    no-eta-equality
    field
      ↝⇒ : A ▸ 1 ⊢ a ↝ b
      ↝⇐ : A ▸ 1 ⊢ b ↝ a
      ⊢⇒⇐ : A ▸ 2 ⊢ seq₀ A ↝⇒ ↝⇐ ↝ idn₀ A
      ⊢⇐⇒ : A ▸ 2 ⊢ seq₀ A ↝⇐ ↝⇒ ↝ idn₀ A
  open _⊢_≅_ public

  module _ {n r}..{ℓ} (A : Alg n r ℓ) where
    idn
      : ∀ {a}
      → A ⊢ a ≅ a
    ↝⇒ idn = idn₀ A
    ↝⇐ idn = idn₀ A
    ⊢⇒⇐ idn = ⊢λ₀ A
    ⊢⇐⇒ idn = ⊢ρ₀ A

    seq
      : ∀ {a b c}
      → (f : A ⊢ a ≅ b)
      → (g : A ⊢ b ≅ c)
      → A ⊢ a ≅ c
    ↝⇒ (seq f g) =
      (seq₀ A (↝⇒ f) (↝⇒ g))
    ↝⇐ (seq f g) =
      (seq₀ A (↝⇐ g) (↝⇐ f))
    ⊢⇒⇐ (seq f g) =
      (seq₁ A
        (⊢α₀ A)
        (seq₁ A
          (seq₀*λ A
            (seq₁ A
              (inv₁ A
                (⊢α₀ A))
            (seq₁ A
              (seq₀*ρ A
                (⊢⇒⇐ g))
            (⊢ρ₀ A))))
          (⊢⇒⇐ f)))
    ⊢⇐⇒ (seq f g) =
      seq₁ A
        (⊢α₀ A)
        (seq₁ A
          (seq₀*λ A
            (seq₁ A
              (inv₁ A
                (⊢α₀ A))
              (seq₁ A
                (seq₀*ρ A
                  (⊢⇐⇒ f))
                (⊢ρ₀ A))))
          (⊢⇐⇒ g))

    inv
      : ∀ {a b}
      → (f : A ⊢ a ≅ b)
      → A ⊢ b ≅ a
    ↝⇒ (inv f) = ↝⇐ f
    ↝⇐ (inv f) = ↝⇒ f
    ⊢⇒⇐ (inv f) = ⊢⇐⇒ f
    ⊢⇐⇒ (inv f) = ⊢⇒⇐ f

open ≅
  using (_⊢_≅_)



Std : ∀ ..ℓ → Set _
Std ℓ = Alg 0 ze ℓ

Gpd : ∀ ..ℓ → Set _
Gpd ℓ = Alg 1 ze ℓ

Cat : ∀ ..ℓ → Set _
Cat ℓ = Alg 1 (su ze) ℓ

open Gph
open Alg

open T
  renaming (ι to ι_)
  using ()
open T.⊔⇑
  using (π)

-- core of a category

module _ where
  open ≅

  -- 𝟙 is contractible in all dimensions

  mutual
    𝟙-n : ∀ {n r i}..{ℓ} → Type {n = n}{r} (𝟙↑ {ℓ = ℓ}) i
    𝟙-n {i = ze} = ∀↝·
    𝟙-n {i = su i} = su ([𝟙-n] i)

    [𝟙-n] : ∀ {n r} i..{ℓ} → [Type] {n = n}{r} (𝟙↑ {ℓ = ℓ}) ([ℕ∞].π i)
    [Type].π ([𝟙-n] i) = 𝟙-n

  -- the core is the maximal subgroupoid of A (which may be empty)

  ≅[_]
    : ∀ {n r}..{ℓ}
    → (A : Alg (1+ n) r ℓ)
    → Alg (1+ n) ze _
  ● [ ≅[ A ] ] = ● [ A ]
  ● (⇇ [ ≅[ A ] ] a b) = A ⊢ a ≅ b
  ● (⇇ (⇇ [ ≅[ A ] ] a b) f g) = A ▸ 2 ⊢ ↝⇒ f ↝ ↝⇒ g
  ⇇ (⇇ (⇇ [ ≅[ A ] ] _ _) _ _) _ _ = 𝟙↑
  ↻ (⇇ (⇇ [ ≅[ A ] ] _ _) _ _) = *
  ↻ (⇇ [ ≅[ A ] ] a b) = ↻ (A ▸ 1 ⊩ a ↝ b)
  ↻ [ ≅[ A ] ] = idn A
  lvl ≅[ A ] = ⇈ ⇈ ⇈ 𝟙-n
  idn₀ ≅[ A ] = idn A
  seq₀ ≅[ A ] = seq A
  inv₀ ≅[ A ] f = inv A f
  seq₀* ≅[ A ] = seq₀* A
  inv₀* ≅[ A ] {f = f}{g = g} α =
    -- we take only the isos so we can construct any inverse
    (seq₁ A
      (inv₁ A
        (⊢ρ₀ A))
      (seq₁ A
        (seq₀*ρ A
          (inv₁ A
            (⊢⇒⇐ g)))
        (seq₁ A
          (⊢α₀ A)
          (seq₁ A
            (seq₀* A
              (seq₁ A
                (seq₀*ρ A
                  (inv₁ A α))
                (⊢⇐⇒ f))
              (idn₁ A))
            (⊢λ₀ A)))))
  ⊢λ₀ ≅[ A ] = ⊢λ₀ A
  ⊢ρ₀ ≅[ A ] = ⊢ρ₀ A
  ⊢α₀ ≅[ A ] = ⊢α₀ A
  ⊢λ₀⁻¹ ≅[ A ] {f = f} = ⊢⇐⇒ f
  ⊢ρ₀⁻¹ ≅[ A ] {f = f} = ⊢⇒⇐ f
  idn₁ ≅[ A ] = idn₁ A
  seq₁ ≅[ A ] = seq₁ A
  inv₁ ≅[ A ] = inv₁ A

-- functor category

infix 1 _⇒₀_
_⇒₀_
  : ∀ {n r}..{ℓ₀ ℓ₁}
  → (A : Alg n r ℓ₀)
  → (B : Alg n r ℓ₁)
  → Alg 1 r _
● [ A ⇒₀ B ] = Fun₀ A B
● (⇇ [ A ⇒₀ B ] F G) = Fun₁ F G
● (⇇ (⇇ [ A ⇒₀ B ] F G) α β) = T.⊔⇑ _ ((a : A ▸) → B ▸ 2 ⊢ ap₁₀ α a ↝ ap₁₀ β a)
⇇ (⇇ (⇇ [ A ⇒₀ B ] _ _) _ _) _ _ = 𝟙↑
↻ (⇇ (⇇ [ A ⇒₀ B ] _ _) _ _) = *
↻ (⇇ [ A ⇒₀ B ] F G) {α} = T.ι λ a → ↻ (B ▸ 1 ⊩ ap₀₀ F a ↝ ap₀₀ G a)
↻ [ A ⇒₀ B ] = ⇒₁.idn
lvl (A ⇒₀ B) = ⇈ ⇈ ⇈ ∀↝·
idn₀ (A ⇒₀ B) = ⇒₁.idn
seq₀ (A ⇒₀ B) = ⇒₁.seq
inv₀ (A ⇒₀ B) α {≜} = ⇒₁.inv α {≜}
seq₀* (A ⇒₀ B) (ι φ) (ι ψ) = T.ι λ a → seq₀* B (φ a) (ψ a)
inv₀* (A ⇒₀ B) (ι ψ) {≜ = T.≡.idn} = T.ι λ a → inv₀* B (ψ a)
⊢λ₀ (A ⇒₀ B) = T.ι λ a → ⊢λ₀ B
⊢ρ₀ (A ⇒₀ B) = T.ι λ a → ⊢ρ₀ B
⊢α₀ (A ⇒₀ B) = T.ι λ a → ⊢α₀ B
⊢λ₀⁻¹ (A ⇒₀ B) {≜ = T.≡.idn} = T.ι λ a → ⊢λ₀⁻¹ B
⊢ρ₀⁻¹ (A ⇒₀ B) {≜ = T.≡.idn} = T.ι λ a → ⊢ρ₀⁻¹ B
idn₁ (A ⇒₀ B) = ι λ a → idn₁ B
seq₁ (A ⇒₀ B) (ι φ) (ι ψ) = ι λ a → seq₁ B (φ a) (ψ a)
inv₁ (A ⇒₀ B) (ι φ) = ι λ a → inv₁ B (φ a)

-- functor groupoid

infix 1 _⇔₀_
_⇔₀_
  : ∀ {n r}..{ℓ₀ ℓ₁}
  → (A : Alg n r ℓ₀)
  → (B : Alg n r ℓ₁)
  → Gpd _
A ⇔₀ B = ≅[ A ⇒₀ B ]

module «alg» where
  open ≅

  «seq₀*»
    : ∀ {r}..{ℓ}
    → {A B C : Alg 1 r ℓ}
    → {F₀ F₁ : Fun₀ A B}
    → {G₀ G₁ : Fun₀ B C}
    → A ⇒₀ B ⊢ F₀ ≅ F₁
    → B ⇒₀ C ⊢ G₀ ≅ G₁
    → A ⇒₀ C ⊢ ⇒₀.seq F₀ G₀ ≅ ⇒₀.seq F₁ G₁
  ap₁₀ (↝⇒ («seq₀*» {C = C}{F₁ = F₁}{G₀ = G₀} α β)) a =
    seq₀ C (ap₀₁ G₀ (ap₁₀ (↝⇒ α) a)) (ap₁₀ (↝⇒ β) (ap₀₀ F₁ a))
  ap₁₁ (↝⇒ («seq₀*» {C = C}{F₁ = F₁}{G₀ = G₀} α β)) f =
    (seq₁ C
      (⊢α₀ C)
      (seq₁ C
        (seq₀*λ C
          (seq₁ C
            (inv₁ C (⇒₀.⊢seq G₀))
            (seq₁ C
              (ap₀₂ G₀ (ap₁₁ (↝⇒ α) f))
              (⇒₀.⊢seq G₀))))
        (seq₁ C
          (inv₁ C (⊢α₀ C))
          (seq₁ C
            (seq₀*ρ C
              (ap₁₁ (↝⇒ β) (ap₀₁ F₁ f)))
            (⊢α₀ C)))))
  ap₁₀ (↝⇐ («seq₀*» {C = C}{F₀ = F₀}{G₁ = G₁} α β)) a =
    seq₀ C (ap₀₁ G₁ (ap₁₀ (↝⇐ α) a)) (ap₁₀ (↝⇐ β) (ap₀₀ F₀ a))
  ap₁₁ (↝⇐ («seq₀*» {C = C}{F₀ = F₀}{G₁ = G₁} α β)) f =
    (seq₁ C
      (⊢α₀ C)
      (seq₁ C
        (seq₀*λ C
          (seq₁ C
            (inv₁ C (⇒₀.⊢seq G₁))
            (seq₁ C
              (ap₀₂ G₁ (ap₁₁ (↝⇐ α) f))
              (⇒₀.⊢seq G₁))))
        (seq₁ C
          (inv₁ C (⊢α₀ C))
          (seq₁ C
            (seq₀*ρ C
              (ap₁₁ (↝⇐ β) (ap₀₁ F₀ f)))
            (⊢α₀ C)))))
  ⊢⇒⇐ («seq₀*» {C = C}{F₀ = F₀}{G₁ = G₁} α β) = ι λ a →
    seq₁ C
      (seq₀*λ C
        (ap₁₁ (↝⇒ β) (ap₁₀ (↝⇒ α) a)))
      (seq₁ C
        (inv₁ C (⊢α₀ C))
        (seq₁ C
          (seq₀*ρ C
            (seq₁ C
              (⊢α₀ C)
              (seq₁ C
                (seq₀*λ C
                  (seq₁ C
                    (inv₁ C (⇒₀.⊢seq G₁))
                    (seq₁ C
                      (ap₀₂ G₁ (π (⊢⇒⇐ α) a))
                      (⇒₀.⊢idn G₁))))
                (⊢λ₀ C))))
          (π (⊢⇒⇐ β) (ap₀₀ F₀ a))))
  ⊢⇐⇒ («seq₀*» {C = C}{F₁ = F₁}{G₀ = G₀} α β) = ι λ a →
    seq₁ C
      (seq₀*λ C
        (ap₁₁ (↝⇐ β) (ap₁₀ (↝⇐ α) a)))
      (seq₁ C
        (inv₁ C (⊢α₀ C))
        (seq₁ C
          (seq₀*ρ C
            (seq₁ C
              (⊢α₀ C)
              (seq₁ C
                (seq₀*λ C
                  (seq₁ C
                    (inv₁ C (⇒₀.⊢seq G₀))
                    (seq₁ C
                      (ap₀₂ G₀ (π (⊢⇐⇒ α) a))
                      (⇒₀.⊢idn G₀))))
                (⊢λ₀ C))))
          (π (⊢⇐⇒ β) (ap₀₀ F₁ a))))

  «⊢λ₀»
    : ∀ {r}..{ℓ}
    → {A B : Alg 1 r ℓ}
    → {F : Fun₀ A B}
    → A ⇒₀ B ⊢ ⇒₀.seq ⇒₀.idn F ≅ F
  ap₁₀ (↝⇒ («⊢λ₀» {B = B})) a =
    idn₀ B
  ap₁₁ (↝⇒ («⊢λ₀» {B = B})) f =
    (seq₁ B
      (⊢ρ₀ B)
      (inv₁ B (⊢λ₀ B)))
  ap₁₀ (↝⇐ («⊢λ₀» {B = B})) a =
    idn₀ B
  ap₁₁ (↝⇐ («⊢λ₀» {B = B})) f =
    (seq₁ B
      (⊢ρ₀ B)
      (inv₁ B (⊢λ₀ B)))
  ⊢⇒⇐ («⊢λ₀» {B = B}) = ι λ a →
    ⊢λ₀ B
  ⊢⇐⇒ («⊢λ₀» {B = B}) = ι λ a →
    ⊢λ₀ B

  «⊢ρ₀»
    : ∀ {r}..{ℓ}
    → {A B : Alg 1 r ℓ}
    → {F : Fun₀ A B}
    → A ⇒₀ B ⊢ ⇒₀.seq F ⇒₀.idn ≅ F
  ap₁₀ (↝⇒ («⊢ρ₀» {B = B})) a =
    idn₀ B
  ap₁₁ (↝⇒ («⊢ρ₀» {B = B})) f =
    (seq₁ B
      (⊢ρ₀ B)
      (inv₁ B (⊢λ₀ B)))
  ap₁₀ (↝⇐ («⊢ρ₀» {B = B})) a =
    idn₀ B
  ap₁₁ (↝⇐ («⊢ρ₀» {B = B})) f =
    (seq₁ B
      (⊢ρ₀ B)
      (inv₁ B (⊢λ₀ B)))
  ⊢⇒⇐ («⊢ρ₀» {B = B}) = ι λ a →
    ⊢λ₀ B
  ⊢⇐⇒ («⊢ρ₀» {B = B}) = ι λ a →
    ⊢λ₀ B

  «⊢α₀»
    : ∀ {r}..{ℓ}
    → {A B C D : Alg 1 r ℓ}
    → {F : Fun₀ A B}
    → {G : Fun₀ B C}
    → {H : Fun₀ C D}
    → A ⇒₀ D ⊢ ⇒₀.seq F (⇒₀.seq G H) ≅ ⇒₀.seq (⇒₀.seq F G) H
  ap₁₀ (↝⇒ («⊢α₀» {D = D})) a =
    idn₀ D
  ap₁₁ (↝⇒ («⊢α₀» {D = D})) {a}{b} f =
    seq₁ D
      (⊢ρ₀ D)
      (inv₁ D (⊢λ₀ D))
  ap₁₀ (↝⇐ («⊢α₀» {D = D})) a =
    idn₀ D
  ap₁₁ (↝⇐ («⊢α₀» {D = D})) {a}{b} f =
    seq₁ D
      (⊢ρ₀ D)
      (inv₁ D (⊢λ₀ D))
  ⊢⇒⇐ («⊢α₀» {D = D}) = ι λ a →
    ⊢λ₀ D
  ⊢⇐⇒ («⊢α₀» {D = D}) = ι λ a →
    ⊢λ₀ D

  -- category of algebras

  «cat»
    : ∀ (r : Fin 2)..ℓ
    → Alg 2 (su ze) _
  ● [ «cat» r ℓ ] = Alg 1 r ℓ
  ⇇ [ «cat» r ℓ ] A B = [ A ⇔₀ B ]
  ↻ [ «cat» r ℓ ] = ⇒₀.idn
  lvl («cat» r ℓ) = ⇈ ⇈ ⇈ ⇈ ∀↝·
  idn₀ («cat» r ℓ) = ⇒₀.idn
  seq₀ («cat» r ℓ) = ⇒₀.seq
  inv₀ («cat» r ℓ) F {≜ = ()}
  seq₀* («cat» r ℓ) = «seq₀*»
  inv₀* («cat» r ℓ) α {≜ = ()}
  ⊢λ₀ («cat» r ℓ) = «⊢λ₀»
  ⊢ρ₀ («cat» r ℓ) = «⊢ρ₀»
  ⊢α₀ («cat» r ℓ) = «⊢α₀»
  ⊢λ₀⁻¹ («cat» r ℓ) {≜ = ()}
  ⊢ρ₀⁻¹ («cat» r ℓ) {≜ = ()}
  idn₁ («cat» r ℓ) {A}{B} = ≅.idn (A ⇒₀ B)
  seq₁ («cat» r ℓ) {A}{B} = ≅.seq (A ⇒₀ B)
  inv₁ («cat» r ℓ) {A}{B} = ≅.inv (A ⇒₀ B)

  -- groupoid of algebras

  «gpd»
    : ∀ (r : Fin 2) ..ℓ
    → Alg 2 ze _
  «gpd» r ℓ = ≅[ «cat» r ℓ ]
