{-# OPTIONS --without-K #-}

module Groupoids.Ordinary.Construction.Arrow where

open import Groupoids.Common
open import Groupoids.Ordinary.Construction.Comma
open import Groupoids.Ordinary.Monoidal.Tensor.Product
open import Groupoids.Ordinary.Morphism.Fib
open import Groupoids.Ordinary.Morphism.Hom.Boot
open import Groupoids.Ordinary.Morphism.Iso
open import Groupoids.Ordinary.Universe.Boot

module Arrow where
  ⇇∐[_]
    : ∀ {r}..{ℓ}
    → (A : 𝔘 r ℓ)
    → 𝔘 r _
  ⇇∐[ A ] = ⇒₀.idn {A = A} ↓ ⇒₀.idn {A = A}

  nodes
    : ∀ {r}..{ℓ}
    → (A : 𝔘 r ℓ)
    → Hom₀ ⇇∐[ A ] (A ⊗ A)
  ap₀₀ (nodes A) =
    T.Σ.fst
  ap₀₁ (nodes A) =
    T.Σ.fst
  ap₀₂ (nodes A) =
    T.⊔⇑.π
  ⇒₀.⊢idn (nodes A) =
    idn₁ A , idn₁ A
  ⇒₀.⊢seq (nodes A) =
    idn₁ A , idn₁ A
  ⇒₀.⊢inv (nodes A) =
    idn₁ A , idn₁ A

  private
    module Arrow where
      dom
        : ∀ {r}..{ℓ}
        → (A : 𝔘 r ℓ)
        → Hom₀ ⇇∐[ A ] A
      dom A = ⇒₀.seq (nodes A) ⊗.fst

      cod
        : ∀ {r}..{ℓ}
        → (A : 𝔘 r ℓ)
        → Hom₀ ⇇∐[ A ] A
      cod A = ⇒₀.seq (nodes A) ⊗.snd

  module _ where
    open Cartesian
    open Fib
    open Lifted
    open Refined

    dom-fib
      : ∀ {r}..{ℓ}
      → (A : 𝔘 r ℓ)
      → Fibration (Arrow.dom A)
    dom (lift (dom-fib A) {b}{e = ((σ , τ) T.▸ e)} f) =
      (b , τ) T.▸ (seq₀ A f e)
    map (lift (dom-fib A) f) =
      (f , idn₀ A) T.▸ (inv₁ A (⊢idn₀-ρ A))
    lhs (edge (car (lift (dom-fib A) f)) (horn img dia coh)) =
      (img , T.snd (T.Σ.fst dia)) T.▸
      (seq₁ A
        (⊢seq₀-α A)
        (seq₁ A
          (seq₀*-λ A coh)
          (T.Σ.snd dia)))
    coh-seq (edge (car (lift (dom-fib A) f)) (horn img dia coh)) =
      ι (inv₁ A coh , inv₁ A (⊢idn₀-ρ A))
    coh-img (edge (car (lift (dom-fib A) f)) (horn img dia coh)) =
      idn₁ A
    unique (edge (car (lift (dom-fib A) f)) (horn img dia coh)) #lhs #seq #img =
      ι (#img , inv₁ A (seq₁ A (T.⊗.snd (T.⊔⇑.π #seq)) (⊢idn₀-ρ A)))
    coe (lift (dom-fib A) f) =
      ≅.idn A
    coh (lift (dom-fib A) f) =
      ⊢idn₀-λ A

  open Arrow public
open Arrow public
  using (⇇∐[_])
