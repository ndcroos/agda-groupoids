{-# OPTIONS --without-K #-}

module Groupoids.Ordinary.Ambient.Cosmos.Tensor.Coproduct where

open import Groupoids.Basis
open import Groupoids.Ordinary.Ambient.Morphism.Hom
open import Groupoids.Ordinary.Ambient.Universe.Boot
  hiding ([_])
open import Groupoids.Ordinary.Groupoid.Opposite

module ⊕ where
  infix 0 _⊕_

  _⊕_
    : ∀ {r}..{ℓ₀ ℓ₁}
    → (A : 𝔘 r ℓ₀)
    → (B : 𝔘 r ℓ₁)
    → 𝔘 r _
  𝔘.[ A ⊕ B ] = 𝔘.[ A ] 𝔊.⊕ 𝔘.[ B ]
  idn₀ (A ⊕ B) {T.⊕.inl a₀} =
    ι (idn₀ A)
  idn₀ (A ⊕ B) {T.⊕.inr b₀} =
    ι (idn₀ B)
  seq₀ (A ⊕ B) {T.⊕.inl a₀}{T.⊕.inl a₁}{T.⊕.inl a₂} (ι f) (ι g) =
    ι (seq₀ A f g)
  seq₀ (A ⊕ B) {T.⊕.inl a₀}{T.⊕.inl a₁}{T.⊕.inr b₂} f  ()
  seq₀ (A ⊕ B) {T.⊕.inl a₀}{T.⊕.inr b₁}{T.⊕.inl a₂} () ()
  seq₀ (A ⊕ B) {T.⊕.inl a₀}{T.⊕.inr b₁}{T.⊕.inr b₂} () g
  seq₀ (A ⊕ B) {T.⊕.inr b₀}{T.⊕.inl a₁}{T.⊕.inl a₂} () g
  seq₀ (A ⊕ B) {T.⊕.inr b₀}{T.⊕.inl a₁}{T.⊕.inr b₂} () ()
  seq₀ (A ⊕ B) {T.⊕.inr b₀}{T.⊕.inr b₁}{T.⊕.inl a₂} f  ()
  seq₀ (A ⊕ B) {T.⊕.inr b₀}{T.⊕.inr b₁}{T.⊕.inr b₂} (ι f) (ι g) =
    ι (seq₀ B f g)
  inv₀ (A ⊕ B) {T.⊕.inl a₀}{T.⊕.inl a₁} (ι f) {≜} =
    ι (inv₀ A f {≜})
  inv₀ (A ⊕ B) {T.⊕.inl a₀}{T.⊕.inr b₁} ()
  inv₀ (A ⊕ B) {T.⊕.inr b₀}{T.⊕.inl a₁} ()
  inv₀ (A ⊕ B) {T.⊕.inr b₀}{T.⊕.inr b₁} (ι f) {≜} =
    ι (inv₀ B f {≜})
  seq₀* (A ⊕ B) {T.⊕.inl a₀}{T.⊕.inl a₁}{T.⊕.inl a₂}{f₀}{f₁}{g₀}{g₁} (ι α₀) (ι α₁) =
    ι (seq₀* A α₀ α₁)
  seq₀* (A ⊕ B) {T.⊕.inl a₀}{T.⊕.inl a₁}{T.⊕.inr b₂}{f₀}{f₁}{()}{()}
  seq₀* (A ⊕ B) {T.⊕.inl a₀}{T.⊕.inr b₁}{T.⊕.inl a₂}{()}{()}{()}{()}
  seq₀* (A ⊕ B) {T.⊕.inl a₀}{T.⊕.inr b₁}{T.⊕.inr b₂}{()}{()}{g₀}{g₁}
  seq₀* (A ⊕ B) {T.⊕.inr b₀}{T.⊕.inl a₁}{T.⊕.inl a₂}{()}{()}{g₀}{g₁}
  seq₀* (A ⊕ B) {T.⊕.inr b₀}{T.⊕.inl a₁}{T.⊕.inr b₂}{()}{()}{()}{()}
  seq₀* (A ⊕ B) {T.⊕.inr b₀}{T.⊕.inr b₁}{T.⊕.inl a₂}{f₀}{f₁}{()}{()}
  seq₀* (A ⊕ B) {T.⊕.inr b₀}{T.⊕.inr b₁}{T.⊕.inr b₂}{f₀}{f₁}{g₀}{g₁} (ι β₀) (ι β₁) =
    ι (seq₀* B β₀ β₁)
  inv₀* (A ⊕ B) {T.⊕.inl a₀}{T.⊕.inl a₁} (ι α) {≜} =
    ι (inv₀* A α {≜})
  inv₀* (A ⊕ B) {T.⊕.inl a₀}{T.⊕.inr b₁}{()}{()}
  inv₀* (A ⊕ B) {T.⊕.inr b₀}{T.⊕.inl a₁}{()}{()}
  inv₀* (A ⊕ B) {T.⊕.inr b₀}{T.⊕.inr b₁} (ι β) {≜} =
    ι (inv₀* B β {≜})
  ⊢idn₀-λ (A ⊕ B) {T.⊕.inl a₀}{T.⊕.inl a₁} =
    ι (⊢idn₀-λ A)
  ⊢idn₀-λ (A ⊕ B) {T.⊕.inl a₀}{T.⊕.inr b₁}{()}
  ⊢idn₀-λ (A ⊕ B) {T.⊕.inr b₀}{T.⊕.inl a₁}{()}
  ⊢idn₀-λ (A ⊕ B) {T.⊕.inr b₀}{T.⊕.inr b₁} =
    ι (⊢idn₀-λ B)
  ⊢idn₀-ρ (A ⊕ B) {T.⊕.inl a₀}{T.⊕.inl a₁} =
    ι (⊢idn₀-ρ A)
  ⊢idn₀-ρ (A ⊕ B) {T.⊕.inl a₀}{T.⊕.inr b₁}{()}
  ⊢idn₀-ρ (A ⊕ B) {T.⊕.inr b₀}{T.⊕.inl a₁}{()}
  ⊢idn₀-ρ (A ⊕ B) {T.⊕.inr b₀}{T.⊕.inr b₁} =
    ι (⊢idn₀-ρ B)
  ⊢seq₀-α (A ⊕ B) {T.⊕.inl a₀}{T.⊕.inl a₁}{T.⊕.inl a₂}{T.⊕.inl a₃}{f}{g}{h} =
    ι (⊢seq₀-α A)
  ⊢seq₀-α (A ⊕ B) {T.⊕.inl a₀}{T.⊕.inl a₁}{T.⊕.inl a₂}{T.⊕.inr b₃}{f}{g}{()}
  ⊢seq₀-α (A ⊕ B) {T.⊕.inl a₀}{T.⊕.inl a₁}{T.⊕.inr b₂}{T.⊕.inl a₃}{f}{()}{()}
  ⊢seq₀-α (A ⊕ B) {T.⊕.inl a₀}{T.⊕.inl a₁}{T.⊕.inr b₂}{T.⊕.inr b₃}{f}{()}{h}
  ⊢seq₀-α (A ⊕ B) {T.⊕.inl a₀}{T.⊕.inr b₁}{T.⊕.inl a₂}{T.⊕.inl a₃}{()}{()}{h}
  ⊢seq₀-α (A ⊕ B) {T.⊕.inl a₀}{T.⊕.inr b₁}{T.⊕.inl a₂}{T.⊕.inr b₃}{()}{()}{()}
  ⊢seq₀-α (A ⊕ B) {T.⊕.inl a₀}{T.⊕.inr b₁}{T.⊕.inr b₂}{T.⊕.inl a₃}{()}{g}{()}
  ⊢seq₀-α (A ⊕ B) {T.⊕.inl a₀}{T.⊕.inr b₁}{T.⊕.inr b₂}{T.⊕.inr b₃}{()}{g}{h}
  ⊢seq₀-α (A ⊕ B) {T.⊕.inr b₀}{T.⊕.inl a₁}{T.⊕.inl a₂}{T.⊕.inl a₃}{()}{g}{h}
  ⊢seq₀-α (A ⊕ B) {T.⊕.inr b₀}{T.⊕.inl a₁}{T.⊕.inl a₂}{T.⊕.inr b₃}{()}{g}{()}
  ⊢seq₀-α (A ⊕ B) {T.⊕.inr b₀}{T.⊕.inl a₁}{T.⊕.inr b₂}{T.⊕.inl a₃}{()}{()}{()}
  ⊢seq₀-α (A ⊕ B) {T.⊕.inr b₀}{T.⊕.inl a₁}{T.⊕.inr b₂}{T.⊕.inr b₃}{()}{()}{h}
  ⊢seq₀-α (A ⊕ B) {T.⊕.inr b₀}{T.⊕.inr b₁}{T.⊕.inl a₂}{T.⊕.inl a₃}{f}{()}{h}
  ⊢seq₀-α (A ⊕ B) {T.⊕.inr b₀}{T.⊕.inr b₁}{T.⊕.inl a₂}{T.⊕.inr b₃}{f}{()}{()}
  ⊢seq₀-α (A ⊕ B) {T.⊕.inr b₀}{T.⊕.inr b₁}{T.⊕.inr b₂}{T.⊕.inl a₃}{f}{g}{()}
  ⊢seq₀-α (A ⊕ B) {T.⊕.inr b₀}{T.⊕.inr b₁}{T.⊕.inr b₂}{T.⊕.inr b₃}{f}{g}{h} =
    ι (⊢seq₀-α B)
  ⊢inv₀-λ (A ⊕ B) {T.⊕.inl a₀}{T.⊕.inl a₁}{≜ = ≜} =
    ι (⊢inv₀-λ A)
  ⊢inv₀-λ (A ⊕ B) {T.⊕.inl a₀}{T.⊕.inr b₁}{()}
  ⊢inv₀-λ (A ⊕ B) {T.⊕.inr b₀}{T.⊕.inl a₁}{()}
  ⊢inv₀-λ (A ⊕ B) {T.⊕.inr b₀}{T.⊕.inr b₁}{≜ = ≜} =
    ι (⊢inv₀-λ B)
  ⊢inv₀-ρ (A ⊕ B) {T.⊕.inl a₀}{T.⊕.inl a₁}{≜ = ≜} =
    ι (⊢inv₀-ρ A)
  ⊢inv₀-ρ (A ⊕ B) {T.⊕.inl a₀}{T.⊕.inr b₁}{()}
  ⊢inv₀-ρ (A ⊕ B) {T.⊕.inr b₀}{T.⊕.inl a₁}{()}
  ⊢inv₀-ρ (A ⊕ B) {T.⊕.inr b₀}{T.⊕.inr b₁}{≜ = ≜} =
    ι (⊢inv₀-ρ B)
  idn₁ (A ⊕ B) {T.⊕.inl a₀}{T.⊕.inl a₁} =
    ι (idn₁ A)
  idn₁ (A ⊕ B) {T.⊕.inl a₀}{T.⊕.inr b₁}{()}
  idn₁ (A ⊕ B) {T.⊕.inr b₀}{T.⊕.inl a₁}{()}
  idn₁ (A ⊕ B) {T.⊕.inr b₀}{T.⊕.inr b₁} =
    ι (idn₁ B)
  seq₁ (A ⊕ B) {T.⊕.inl a₀}{T.⊕.inl a₁} (ι α₀) (ι α₁) =
    ι (seq₁ A α₀ α₁)
  seq₁ (A ⊕ B) {T.⊕.inl a₀}{T.⊕.inr b₁}{()}{()}{()}
  seq₁ (A ⊕ B) {T.⊕.inr b₀}{T.⊕.inl a₁}{()}{()}{()}
  seq₁ (A ⊕ B) {T.⊕.inr b₀}{T.⊕.inr b₁} (ι β₀) (ι β₁) =
    ι (seq₁ B β₀ β₁)
  inv₁ (A ⊕ B) {T.⊕.inl a₀}{T.⊕.inl a₁} (ι α) =
    ι (inv₁ A α)
  inv₁ (A ⊕ B) {T.⊕.inl a₀}{T.⊕.inr b₁}{()}{()}
  inv₁ (A ⊕ B) {T.⊕.inr b₀}{T.⊕.inl a₁}{()}{()}
  inv₁ (A ⊕ B) {T.⊕.inr b₀}{T.⊕.inr b₁} (ι β) =
    ι (inv₁ B β)

  inl
    : ∀ {r}..{ℓ₀ ℓ₁}
    → {A : 𝔘 r ℓ₀}
    → {B : 𝔘 r ℓ₁}
    → Hom₀ A (A ⊕ B)
  ap₀₀ inl = T.⊕.inl
  ap₀₁ inl = ι
  ap₀₂ inl = ι
  ⇒₀.⊢idn (inl {A = A}) = ι (idn₁ A)
  ⇒₀.⊢seq (inl {A = A}) = ι (idn₁ A)
  ⇒₀.⊢inv (inl {A = A}) = ι (idn₁ A)

  inr
    : ∀ {r}..{ℓ₀ ℓ₁}
    → {A : 𝔘 r ℓ₀}
    → {B : 𝔘 r ℓ₁}
    → Hom₀ B (A ⊕ B)
  ap₀₀ inr = T.⊕.inr
  ap₀₁ inr = ι
  ap₀₂ inr = ι
  ⇒₀.⊢idn (inr {B = B}) = ι (idn₁ B)
  ⇒₀.⊢seq (inr {B = B}) = ι (idn₁ B)
  ⇒₀.⊢inv (inr {B = B}) = ι (idn₁ B)

  [_,_]
    : ∀ {r}..{ℓ₀ ℓ₁ ℓ₂}
    → {A : 𝔘 r ℓ₀}
    → {B : 𝔘 r ℓ₁}
    → {X : 𝔘 r ℓ₂}
    → (F : Hom₀ A X)
    → (G : Hom₀ B X)
    → Hom₀ (A ⊕ B) X
  ap₀₀ [ F , G ] =
    T.⊕.[ ap₀₀ F , ap₀₀ G ]
  ap₀₁ [ F , G ] {T.⊕.inl a₀}{T.⊕.inl a₁} (ι f) =
    ap₀₁ F f
  ap₀₁ [ F , G ] {T.⊕.inl a₀}{T.⊕.inr b₁} ()
  ap₀₁ [ F , G ] {T.⊕.inr b₀}{T.⊕.inl a₁} ()
  ap₀₁ [ F , G ] {T.⊕.inr b₀}{T.⊕.inr b₁} (ι g) =
    ap₀₁ G g
  ap₀₂ [ F , G ] {T.⊕.inl a₀}{T.⊕.inl a₁} (ι α) =
    ap₀₂ F α
  ap₀₂ [ F , G ] {T.⊕.inl a₀}{T.⊕.inr b₁} {()}{()}
  ap₀₂ [ F , G ] {T.⊕.inr b₀}{T.⊕.inl a₁} {()}{()}
  ap₀₂ [ F , G ] {T.⊕.inr b₀}{T.⊕.inr b₁} (ι β) =
    ap₀₂ G β
  ⇒₀.⊢idn [ F , G ] {T.⊕.inl a} =
    ⇒₀.⊢idn F
  ⇒₀.⊢idn [ F , G ] {T.⊕.inr b} =
    ⇒₀.⊢idn G
  ⇒₀.⊢seq [ F , G ] {T.⊕.inl a₀}{T.⊕.inl a₁}{T.⊕.inl a₂} {f₀}{f₁} =
    ⇒₀.⊢seq F
  ⇒₀.⊢seq [ F , G ] {T.⊕.inl a₀}{T.⊕.inl a₁}{T.⊕.inr b₂} {f₀}{()}
  ⇒₀.⊢seq [ F , G ] {T.⊕.inl a₀}{T.⊕.inr b₁}{T.⊕.inl a₂} {()}{()}
  ⇒₀.⊢seq [ F , G ] {T.⊕.inl a₀}{T.⊕.inr b₁}{T.⊕.inr b₂} {()}{g₁}
  ⇒₀.⊢seq [ F , G ] {T.⊕.inr b₀}{T.⊕.inl a₁}{T.⊕.inl a₂} {()}{f₁}
  ⇒₀.⊢seq [ F , G ] {T.⊕.inr b₀}{T.⊕.inl a₁}{T.⊕.inr b₂} {()}{()}
  ⇒₀.⊢seq [ F , G ] {T.⊕.inr b₀}{T.⊕.inr b₁}{T.⊕.inl a₂} {g₀}{()}
  ⇒₀.⊢seq [ F , G ] {T.⊕.inr b₀}{T.⊕.inr b₁}{T.⊕.inr b₂} {g₀}{g₁} =
    ⇒₀.⊢seq G
  ⇒₀.⊢inv [ F , G ] {≜} {T.⊕.inl a₀}{T.⊕.inl a₁} =
    ⇒₀.⊢inv F {≜}
  ⇒₀.⊢inv [ F , G ] {≜} {T.⊕.inl a₀}{T.⊕.inr b₁} {()}
  ⇒₀.⊢inv [ F , G ] {≜} {T.⊕.inr b₀}{T.⊕.inl a₁} {()}
  ⇒₀.⊢inv [ F , G ] {≜} {T.⊕.inr b₀}{T.⊕.inr b₁} =
    ⇒₀.⊢inv G {≜}

  [_⊕_]
    : ∀ {r}..{ℓ₀ ℓ₁ ℓ₂ ℓ₃}
    → {A : 𝔘 r ℓ₀}
    → {B : 𝔘 r ℓ₁}
    → {X : 𝔘 r ℓ₂}
    → {Y : 𝔘 r ℓ₃}
    → (F : Hom₀ A X)
    → (G : Hom₀ B Y)
    → Hom₀ (A ⊕ B) (X ⊕ Y)
  [ F ⊕ G ] = [ ⇒₀.seq F inl , ⇒₀.seq G inr ]

  module ⊢ where
    -- FIXME: these should be isomorphisms

    op⇒
      : ∀ {r}..{ℓ₀ ℓ₁}
      → {A : 𝔘 r ℓ₀}
      → {B : 𝔘 r ℓ₁}
      → Hom₀ Op[ A ⊕ B ] (Op[ A ] ⊕ Op[ B ])
    ap₀₀ op⇒ = T.⇒.idn
    ap₀₁ op⇒ {T.⊕.inl a₀}{T.⊕.inl a₁} = T.⇒.idn
    ap₀₁ op⇒ {T.⊕.inl a₀}{T.⊕.inr b₁} = T.⇒.idn
    ap₀₁ op⇒ {T.⊕.inr b₀}{T.⊕.inl a₁} = T.⇒.idn
    ap₀₁ op⇒ {T.⊕.inr b₀}{T.⊕.inr b₁} = T.⇒.idn
    ap₀₂ op⇒ {T.⊕.inl a₀}{T.⊕.inl a₁} = T.⇒.idn
    ap₀₂ op⇒ {T.⊕.inl a₀}{T.⊕.inr b₁} = T.⇒.idn
    ap₀₂ op⇒ {T.⊕.inr b₀}{T.⊕.inl a₁} = T.⇒.idn
    ap₀₂ op⇒ {T.⊕.inr b₀}{T.⊕.inr b₁} = T.⇒.idn
    ⇒₀.⊢idn (op⇒ {A = A}{B}) {T.⊕.inl a} = ι (idn₁ A)
    ⇒₀.⊢idn (op⇒ {A = A}{B}) {T.⊕.inr b} = ι (idn₁ B)
    ⇒₀.⊢seq (op⇒ {A = A}{B}) {T.⊕.inl a₀}{T.⊕.inl a₁}{T.⊕.inl a₂} {f}{g} = ι (idn₁ A)
    ⇒₀.⊢seq (op⇒ {A = A}{B}) {T.⊕.inl a₀}{T.⊕.inl a₁}{T.⊕.inr b₂} {f}{()}
    ⇒₀.⊢seq (op⇒ {A = A}{B}) {T.⊕.inl a₀}{T.⊕.inr b₁}{T.⊕.inl a₂} {()}{()}
    ⇒₀.⊢seq (op⇒ {A = A}{B}) {T.⊕.inl a₀}{T.⊕.inr b₁}{T.⊕.inr b₂} {()}{g}
    ⇒₀.⊢seq (op⇒ {A = A}{B}) {T.⊕.inr b₀}{T.⊕.inl a₁}{T.⊕.inl a₂} {()}{g}
    ⇒₀.⊢seq (op⇒ {A = A}{B}) {T.⊕.inr b₀}{T.⊕.inl a₁}{T.⊕.inr b₂} {()}{()}
    ⇒₀.⊢seq (op⇒ {A = A}{B}) {T.⊕.inr b₀}{T.⊕.inr b₁}{T.⊕.inl a₂} {f}{()}
    ⇒₀.⊢seq (op⇒ {A = A}{B}) {T.⊕.inr b₀}{T.⊕.inr b₁}{T.⊕.inr b₂} {f}{g} = ι (idn₁ B)
    ⇒₀.⊢inv (op⇒ {A = A}{B}) {≜}{T.⊕.inl a₀}{T.⊕.inl a₁} {f} = ι (idn₁ A)
    ⇒₀.⊢inv (op⇒ {A = A}{B}) {≜}{T.⊕.inl a₀}{T.⊕.inr b₁} {()}
    ⇒₀.⊢inv (op⇒ {A = A}{B}) {≜}{T.⊕.inr b₀}{T.⊕.inl a₁} {()}
    ⇒₀.⊢inv (op⇒ {A = A}{B}) {≜}{T.⊕.inr b₀}{T.⊕.inr a₁} {f} = ι (idn₁ B)

    op⇐
      : ∀ {r}..{ℓ₀ ℓ₁}
      → {A : 𝔘 r ℓ₀}
      → {B : 𝔘 r ℓ₁}
      → Hom₀ (Op[ A ] ⊕ Op[ B ]) Op[ A ⊕ B ]
    ap₀₀ op⇐ = T.⇒.idn
    ap₀₁ op⇐ {T.⊕.inl a₀}{T.⊕.inl a₁} = T.⇒.idn
    ap₀₁ op⇐ {T.⊕.inl a₀}{T.⊕.inr b₁} = T.⇒.idn
    ap₀₁ op⇐ {T.⊕.inr b₀}{T.⊕.inl a₁} = T.⇒.idn
    ap₀₁ op⇐ {T.⊕.inr b₀}{T.⊕.inr b₁} = T.⇒.idn
    ap₀₂ op⇐ {T.⊕.inl a₀}{T.⊕.inl a₁} = T.⇒.idn
    ap₀₂ op⇐ {T.⊕.inl a₀}{T.⊕.inr b₁} = T.⇒.idn
    ap₀₂ op⇐ {T.⊕.inr b₀}{T.⊕.inl a₁} = T.⇒.idn
    ap₀₂ op⇐ {T.⊕.inr b₀}{T.⊕.inr b₁} = T.⇒.idn
    ⇒₀.⊢idn (op⇐ {A = A}{B}) {T.⊕.inl a} = ι (idn₁ A)
    ⇒₀.⊢idn (op⇐ {A = A}{B}) {T.⊕.inr b} = ι (idn₁ B)
    ⇒₀.⊢seq (op⇐ {A = A}{B}) {T.⊕.inl a₀}{T.⊕.inl a₁}{T.⊕.inl a₂} {f}{g} = ι (idn₁ A)
    ⇒₀.⊢seq (op⇐ {A = A}{B}) {T.⊕.inl a₀}{T.⊕.inl a₁}{T.⊕.inr b₂} {f}{()}
    ⇒₀.⊢seq (op⇐ {A = A}{B}) {T.⊕.inl a₀}{T.⊕.inr b₁}{T.⊕.inl a₂} {()}{()}
    ⇒₀.⊢seq (op⇐ {A = A}{B}) {T.⊕.inl a₀}{T.⊕.inr b₁}{T.⊕.inr b₂} {()}{g}
    ⇒₀.⊢seq (op⇐ {A = A}{B}) {T.⊕.inr b₀}{T.⊕.inl a₁}{T.⊕.inl a₂} {()}{g}
    ⇒₀.⊢seq (op⇐ {A = A}{B}) {T.⊕.inr b₀}{T.⊕.inl a₁}{T.⊕.inr b₂} {()}{()}
    ⇒₀.⊢seq (op⇐ {A = A}{B}) {T.⊕.inr b₀}{T.⊕.inr b₁}{T.⊕.inl a₂} {f}{()}
    ⇒₀.⊢seq (op⇐ {A = A}{B}) {T.⊕.inr b₀}{T.⊕.inr b₁}{T.⊕.inr b₂} {f}{g} = ι (idn₁ B)
    ⇒₀.⊢inv (op⇐ {A = A}{B}) {≜}{T.⊕.inl a₀}{T.⊕.inl a₁} {f} = ι (idn₁ A)
    ⇒₀.⊢inv (op⇐ {A = A}{B}) {≜}{T.⊕.inl a₀}{T.⊕.inr b₁} {()}
    ⇒₀.⊢inv (op⇐ {A = A}{B}) {≜}{T.⊕.inr b₀}{T.⊕.inl a₁} {()}
    ⇒₀.⊢inv (op⇐ {A = A}{B}) {≜}{T.⊕.inr b₀}{T.⊕.inr a₁} {f} = ι (idn₁ B)

open ⊕ public
  using (_⊕_)
