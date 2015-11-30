{-# OPTIONS --without-K #-}

module Setoid.Fam where

open import Agda.Primitive
private
  module G where
    open import Groupoid public
      hiding (module Map)
    module I where
      module SETOID where
        open import Groupoid.Instances.SETOID public
    module Map where
      open Groupoid.Map public
      open import Groupoid.Presheaf public
import Setoid as S
open import Type as T
  using (_,_)

record Fam₀
  ..{ℓ₀ᵒ ℓ₀ʰ}
  (I : S.t G.Dir.≈ ℓ₀ᵒ ℓ₀ʰ)
  ..(ℓ₁ᵒ ℓ₁ʰ : _)
    : Set ((ℓ₀ᵒ ⊔ ℓ₀ʰ) ⊔ lsuc (ℓ₁ᵒ ⊔ ℓ₁ʰ)) where
  no-eta-equality
  field
    fam : G.S↑C I G.Map.⇏₀ᵗ G.I.SETOID.c ℓ₁ᵒ ℓ₁ʰ

  fib : ∀ i → S.t S.Dir.≈ ℓ₁ᵒ ℓ₁ʰ
  fib i = G.Map._$₀_ fam i

  coe
    : ∀ {i₀ i₁}
    → (ρ : S.homᵗ I (i₀ , i₁))
    → fib i₁ S.Map.⇒₀ᵗ fib i₀
  coe ρ = G.Map._$₁_ fam ρ

  field
    irr
      : ∀ {i₀ i₁}
      → (ρ₀ ρ₁ : S.homᵗ I (i₀ , i₁))
      → coe ρ₀ S.Map.⇒₁ coe ρ₁

  fib₀ : ∀ i → Set ℓ₁ᵒ
  fib₀ i = S.obj (fib i)

  coe₀
    : ∀ {i₀ i₁}
    → (ρ : S.homᵗ I (i₀ , i₁))
    → (fib₀ i₁ → fib₀ i₀)
  coe₀ ρ ψ = coe ρ S.Map.$₀ ψ

  coe₁
    : ∀ {i₀ i₁} {ψ₀ ψ₁ : fib₀ i₁}
    → (ρ : S.homᵗ I (i₀ , i₁))
    → (σ : S.homᵗ (fib i₁) (ψ₀ , ψ₁))
    → S.homᵗ (fib i₀) (coe₀ ρ ψ₀ , coe₀ ρ ψ₁)
  coe₁ ρ σ = coe ρ S.Map.$₁ σ

  irr₀
    : ∀ {i₀ i₁} {ψ : fib₀ i₁}
    → (ρ₀ ρ₁ : S.homᵗ I (i₀ , i₁))
    → S.homᵗ (fib i₀) (coe₀ ρ₀ ψ , coe₀ ρ₁ ψ)
  irr₀ ρ₀ ρ₁ = S.Map.com₁ (irr ρ₀ ρ₁)

  coh-idn
    : ∀ {i}
    → (ρ : S.homᵗ I (i , i))
    → {ψ : fib₀ i}
    → S.homᵗ (fib i) (coe₀ ρ ψ , ψ)
  coh-idn ρ {ψ} =
    S.cmpᵗ (fib _) (S.Map.com₁ (G.Map.idn fam) {ψ} , irr₀ _ _)

  coh-cmp
    : ∀ {i₀ i₁ i₂}
    → (ρ : S.homᵗ I (i₂ , i₀))
    → (ρ₁ : S.homᵗ I (i₂ , i₁))
    → (ρ₀ : S.homᵗ I (i₁ , i₀))
    → {ψ : fib₀ i₀}
    → S.homᵗ (fib i₂) (coe₀ ρ ψ , (coe₀ ρ₁ T.Map.∘ coe₀ ρ₀) ψ)
  coh-cmp ρ ρ₁ ρ₀ {ψ} =
    S.cmpᵗ (fib _) (S.Map.com₁ (G.Map.cmp fam ρ₁ ρ₀) {ψ} , irr₀ _ _)

record Fam₁
  ..{ℓ₀₀ᵒ ℓ₀₀ʰ ℓ₀₁ᵒ ℓ₀₁ʰ ℓ₁₀ᵒ ℓ₁₀ʰ ℓ₁₁ᵒ ℓ₁₁ʰ}
  {I₀ : S.t S.Dir.≈ ℓ₀₀ᵒ ℓ₀₀ʰ}
  {I₁ : S.t S.Dir.≈ ℓ₁₀ᵒ ℓ₁₀ʰ}
  (Ψ₀ : Fam₀ I₀ ℓ₀₁ᵒ ℓ₀₁ʰ)
  (Ψ₁ : Fam₀ I₁ ℓ₁₁ᵒ ℓ₁₁ʰ)
    : Set (((ℓ₀₀ᵒ ⊔ ℓ₀₀ʰ) ⊔ (ℓ₀₁ᵒ ⊔ ℓ₀₁ʰ))
         ⊔ ((ℓ₁₀ᵒ ⊔ ℓ₁₀ʰ) ⊔ (ℓ₁₁ᵒ ⊔ ℓ₁₁ʰ))) where
  no-eta-equality
  field
    idx
      : I₀ S.Map.⇒₀ᵗ I₁
    fib
      : (open Fam₀)
      → ∀ i
      → fib Ψ₀ i S.Map.⇒₀ᵗ fib Ψ₁ (idx S.Map.$₀ i)
    coh
      : (open S.Map)
      → (open Fam₀ hiding (fib))
      → ∀ {i₀ i₁}
      → (ρ : S.homᵗ I₀ (i₀ , i₁))
      → (fib i₀ ∘₀ coe Ψ₀ ρ) ⇒₁ (coe Ψ₁ (idx $₁ ρ) ∘₀ fib i₁)

∐
  : ∀ ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ}
  → (A : S.t S.Dir.≈ ℓ₀ᵒ ℓ₀ʰ)
  → (B : Fam₀ A ℓ₁ᵒ ℓ₁ʰ)
  → S.t S.Dir.≈ _ _
S.obj (∐ A B) =
  let open Fam₀ in
  T.Ten.∐ (S.obj A) (fib₀ B)
S.homᵗ (∐ A B) ((a₀ , b₀) , (a₁ , b₁)) =
  let open Fam₀ in
  T.Ten.∐ (S.homᵗ A (a₁ , a₀)) λ σ →
    S.homᵗ (fib B a₁) (coe₀ B σ b₀ , b₁)
S.idnᵗ (∐ A B) {a , b} _ =
  let open Fam₀ in
  S.idnᵗ A _ , coh-idn B (S.idnᵗ A _)
S.cmpᵗ (∐ A B) ((qᵃ , qᵇ) , (pᵃ , pᵇ)) =
  let open Fam₀ in
  S.cmpᵗ A (pᵃ , qᵃ)
  , S.cmpᵗ (fib B _)
    ( S.cmpᵗ (fib B _) (qᵇ , coe₁ B qᵃ pᵇ)
    , coh-cmp B (S.cmpᵗ A (pᵃ , qᵃ)) qᵃ pᵃ
    )
S.invᵗ (∐ A B) (pᵃ , pᵇ) =
  let open Fam₀ in
  S.invᵗ A pᵃ
  , S.cmpᵗ (fib B _)
    ( S.cmpᵗ (fib B _)
        ( coh-idn B (S.idnᵗ A T.*)
        , S.invᵗ (fib B _)
          (S.cmpᵗ (fib B _)
            ( coh-cmp B
              (S.cmpᵗ A (pᵃ , S.invᵗ A pᵃ))
                (S.invᵗ A pᵃ) pᵃ
            , irr₀ B _ _
            )
          )
        )
    , S.invᵗ (fib B _) (coe₁ B (S.invᵗ A pᵃ) pᵇ)
    )
