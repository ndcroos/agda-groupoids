{-# OPTIONS --without-K #-}

module Groupoids.Ordinary.Ambient.Cosmos.Tensor.Product where

open import Groupoids.Basis
open import Groupoids.Ordinary.Ambient.Morphism.Hom
open import Groupoids.Ordinary.Ambient.Universe.Boot
open import Groupoids.Ordinary.Groupoid.Opposite

module ⊗ where
  infix 2 _⊗_

  _⊗_
    : ∀ {r}..{ℓ₀ ℓ₁}
    → (A : 𝔘 r ℓ₀)
    → (B : 𝔘 r ℓ₁)
    → 𝔘 r _
  [ A ⊗ B ] = [ A ] 𝔊.⊗ [ B ]
  idn₀ (A ⊗ B) =
    idn₀ A , idn₀ B
  seq₀ (A ⊗ B) (f₀ , g₀) (f₁ , g₁) =
    seq₀ A f₀ f₁ , seq₀ B g₀ g₁
  inv₀ (A ⊗ B) (f , g) {≜} =
    inv₀ A f {≜} , inv₀ B g {≜}
  seq₀* (A ⊗ B) (α₀ , β₀)(α₁ , β₁) =
    seq₀* A α₀ α₁ , seq₀* B β₀ β₁
  inv₀* (A ⊗ B) (α , β) {≜} =
    inv₀* A α {≜} , inv₀* B β {≜}
  ⊢idn₀-λ (A ⊗ B) =
    ⊢idn₀-λ A , ⊢idn₀-λ B
  ⊢idn₀-ρ (A ⊗ B) =
    ⊢idn₀-ρ A , ⊢idn₀-ρ B
  ⊢seq₀-α (A ⊗ B) =
    ⊢seq₀-α A , ⊢seq₀-α B
  ⊢inv₀-λ (A ⊗ B) {≜ = ≜} =
    ⊢inv₀-λ A {≜ = ≜} , ⊢inv₀-λ B {≜ = ≜}
  ⊢inv₀-ρ (A ⊗ B) {≜ = ≜} =
    ⊢inv₀-ρ A {≜ = ≜} , ⊢inv₀-ρ B {≜ = ≜}
  idn₁ (A ⊗ B) =
    idn₁ A , idn₁ B
  seq₁ (A ⊗ B) (α₀ , β₀)(α₁ , β₁) =
    seq₁ A α₀ α₁ , seq₁ B β₀ β₁
  inv₁ (A ⊗ B) (α , β) =
    inv₁ A α , inv₁ B β

  fst
    : ∀ {r}..{ℓ₀ ℓ₁}
    → {A : 𝔘 r ℓ₀}
    → {B : 𝔘 r ℓ₁}
    → Hom₀ (A ⊗ B) A
  ap₀₀ fst = T.⊗.fst
  ap₀₁ fst = T.⊗.fst
  ap₀₂ fst = T.⊗.fst
  ⇒₀.⊢idn (fst {A = A}) = idn₁ A
  ⇒₀.⊢seq (fst {A = A}) = idn₁ A
  ⇒₀.⊢inv (fst {A = A}) = idn₁ A

  snd
    : ∀ {r}..{ℓ₀ ℓ₁}
    → {A : 𝔘 r ℓ₀}
    → {B : 𝔘 r ℓ₁}
    → Hom₀ (A ⊗ B) B
  ap₀₀ snd = T.⊗.snd
  ap₀₁ snd = T.⊗.snd
  ap₀₂ snd = T.⊗.snd
  ⇒₀.⊢idn (snd {B = B}) = idn₁ B
  ⇒₀.⊢seq (snd {B = B}) = idn₁ B
  ⇒₀.⊢inv (snd {B = B}) = idn₁ B

  ⟨_,_⟩
    : ∀ {r}..{ℓ₀ ℓ₁ ℓ₂}
    → {A : 𝔘 r ℓ₀}
    → {B : 𝔘 r ℓ₁}
    → {X : 𝔘 r ℓ₂}
    → (F : Hom₀ X A)
    → (G : Hom₀ X B)
    → Hom₀ X (A ⊗ B)
  ap₀₀ ⟨ F , G ⟩ =
    T.⊗.⟨ ap₀₀ F , ap₀₀ G ⟩
  ap₀₁ ⟨ F , G ⟩ =
    T.⊗.⟨ ap₀₁ F , ap₀₁ G ⟩
  ap₀₂ ⟨ F , G ⟩ =
    T.⊗.⟨ ap₀₂ F , ap₀₂ G ⟩
  ⇒₀.⊢idn ⟨ F , G ⟩ =
    ⇒₀.⊢idn F , ⇒₀.⊢idn G
  ⇒₀.⊢seq ⟨ F , G ⟩ =
    ⇒₀.⊢seq F , ⇒₀.⊢seq G
  ⇒₀.⊢inv ⟨ F , G ⟩ {≜} =
    ⇒₀.⊢inv F {≜} , ⇒₀.⊢inv G {≜}

  ⟨_⊗_⟩
    : ∀ {r}..{ℓ₀ ℓ₁ ℓ₂ ℓ₃}
    → {A : 𝔘 r ℓ₀}
    → {B : 𝔘 r ℓ₁}
    → {X : 𝔘 r ℓ₂}
    → {Y : 𝔘 r ℓ₃}
    → (F : Hom₀ X A)
    → (G : Hom₀ Y B)
    → Hom₀ (X ⊗ Y) (A ⊗ B)
  ⟨ F ⊗ G ⟩ = ⟨ ⇒₀.seq fst F , ⇒₀.seq snd G ⟩

  module ⊢ where
    -- FIXME: these should be isomorphisms

    op⇒
      : ∀ {r}..{ℓ₀ ℓ₁}
      → {A : 𝔘 r ℓ₀}
      → {B : 𝔘 r ℓ₁}
      → Hom₀ Op[ A ⊗ B ] (Op[ A ] ⊗ Op[ B ])
    ap₀₀ op⇒ = T.⇒.idn
    ap₀₁ op⇒ = T.⇒.idn
    ap₀₂ op⇒ = T.⇒.idn
    ⇒₀.⊢idn (op⇒ {A = A}{B}) = idn₁ A , idn₁ B
    ⇒₀.⊢seq (op⇒ {A = A}{B}) = idn₁ A , idn₁ B
    ⇒₀.⊢inv (op⇒ {A = A}{B}) = idn₁ A , idn₁ B

    op⇐
      : ∀ {r}..{ℓ₀ ℓ₁}
      → {A : 𝔘 r ℓ₀}
      → {B : 𝔘 r ℓ₁}
      → Hom₀ (Op[ A ] ⊗ Op[ B ]) Op[ A ⊗ B ]
    ap₀₀ op⇐ = T.⇒.idn
    ap₀₁ op⇐ = T.⇒.idn
    ap₀₂ op⇐ = T.⇒.idn
    ⇒₀.⊢idn (op⇐ {A = A}{B}) = idn₁ A , idn₁ B
    ⇒₀.⊢seq (op⇐ {A = A}{B}) = idn₁ A , idn₁ B
    ⇒₀.⊢inv (op⇐ {A = A}{B}) = idn₁ A , idn₁ B

open ⊗ public
  using (_⊗_)
