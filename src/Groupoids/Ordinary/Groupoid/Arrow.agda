{-# OPTIONS --without-K #-}

module Groupoids.Ordinary.Groupoid.Arrow where

open import Groupoids.Basis
open import Groupoids.Ordinary.Groupoid.Comma
open import Groupoids.Ordinary.Groupoid.Opposite
open import Groupoids.Ordinary.Ambient.Morphism.Hom.Boot
open import Groupoids.Ordinary.Ambient.Morphism.Iso
open import Groupoids.Ordinary.Ambient.Universe.Boot
open import Groupoids.Ordinary.Structure.Fibration

module Arrow where
  ⇇∐[_]
    : ∀ {r}..{ℓ}
    → (A : 𝔘 r ℓ)
    → 𝔘 r _
  ⇇∐[ A ] = ⇒₀.idn {A = A} ↓ ⇒₀.idn {A = A}

  private
    module Arrow
      {r}
      ..{ℓ}
      (A : 𝔘 r ℓ)
      where
        dom : Hom₀ ⇇∐[ A ] A
        dom = Comma.dom ⇒₀.idn ⇒₀.idn

        cod : Hom₀ ⇇∐[ A ] A
        cod = Comma.cod ⇒₀.idn ⇒₀.idn

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
      (b , τ) T.▸
      (seq₀ A f e)
    map (lift (dom-fib A) f) =
      (f , idn₀ A) T.▸
      (inv₁ A (⊢idn₀-ρ A))
    lhs (edge (car (lift (dom-fib A) f)) (horn img dia coh)) =
      (img , T.snd (T.Σ.fst dia)) T.▸
      (seq₁ A
        (⊢seq₀-α A)
        (seq₁ A
          (seq₀*-λ A coh)
          (T.Σ.snd dia)))
    coh-seq (edge (car (lift (dom-fib A) f)) 𝔥) =
      ι (inv₁ A (Horn.coh 𝔥) , inv₁ A (⊢idn₀-ρ A))
    coh-img (edge (car (lift (dom-fib A) f)) 𝔥) =
      idn₁ A
    unique (edge (car (lift (dom-fib A) f)) 𝔥) #lhs #seq #img =
      ι (#img , inv₁ A (seq₁ A (T.⊗.snd (T.⊔⇑.π #seq)) (⊢idn₀-ρ A)))
    coe (lift (dom-fib A) f) =
      ≅.idn A
    coh (lift (dom-fib A) f) =
      ⊢idn₀-λ A

    cod-opfib
      : ∀ {r}..{ℓ}
      → (A : 𝔘 r ℓ)
      → Opfibration (Arrow.cod A)
    dom (lift (cod-opfib A) {b}{e = ((σ , τ) T.▸ e)} f) =
      (σ , b) T.▸
      (cmp₀ A f e)
    map (lift (cod-opfib A) f) =
      (idn₀ A , f) T.▸
      (⊢idn₀-λ A)
    lhs (edge (car (lift (cod-opfib A) f)) (horn img dia coh)) =
      (T.⊗.fst (T.Σ.fst dia) , img) T.▸
      (inv₁ A
        (seq₁ A
          (inv₁ A (⊢seq₀-α A))
          (seq₁ A
            (seq₀*-ρ A coh)
            (inv₁ A (T.Σ.snd dia)))))
    coh-seq (edge (car (lift (cod-opfib A) f)) 𝔥) =
      ι (inv₁ A (⊢idn₀-λ A) , inv₁ A (Horn.coh 𝔥))
    coh-img (edge (car (lift (cod-opfib A) f)) 𝔥) =
      idn₁ A
    unique (edge (car (lift (cod-opfib A) f)) 𝔥) #lhs #seq #img =
      ι (inv₁ A (seq₁ A (T.⊗.fst (T.⊔⇑.π #seq)) (⊢idn₀-λ A)) , #img)
    coe (lift (cod-opfib A) f) =
      ≅.idn Op[ A ]
    coh (lift (cod-opfib A) f) =
      ⊢idn₀-ρ A

  open Arrow public
open Arrow public
  using (⇇∐[_])
