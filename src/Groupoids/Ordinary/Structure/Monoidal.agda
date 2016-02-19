{-# OPTIONS --without-K #-}

module Groupoids.Ordinary.Structure.Monoidal where

open import Groupoids.Basis
open import Groupoids.Ordinary.Ambient.Cosmos.Diagonal
open import Groupoids.Ordinary.Ambient.Cosmos.Tensor.Product
open import Groupoids.Ordinary.Ambient.Cosmos.Unit.Terminal
open import Groupoids.Ordinary.Ambient.Morphism.Hom
open import Groupoids.Ordinary.Ambient.Morphism.Iso
open import Groupoids.Ordinary.Ambient.Universe
open import Groupoids.Ordinary.Groupoid.Opposite

module Monoidal where
  open Iso
  open ⊗
    using (⟨_,_⟩)
    using (⟨_⊗_⟩)

  record Monoidal {r}..{ℓ} (A : 𝔘 r ℓ) : Set (lsuc ℓ) where
    no-eta-equality
    field
      one : A ▸
      ten : Hom₀ (A ⊗ A) A

    𝟙₀ = one

    _⊛₀_
      : (x y : A ▸)
      → A ▸
    _⊛₀_ x y = ap₀₀ ten (x , y)

    _⊛₁_
      : {x₀ x₁ y₀ y₁ : A ▸}
      → (f : A ▸ 1 ⊢ x₀ ↝ x₁)
      → (g : A ▸ 1 ⊢ y₀ ↝ y₁)
      → A ▸ 1 ⊢ x₀ ⊛₀ y₀ ↝ x₁ ⊛₀ y₁
    _⊛₁_ f g = ap₀₁ ten (f , g)

    _⊛₂_
      : {x₀ x₁ y₀ y₁ : A ▸}
      → {f₀ f₁ : A ▸ 1 ⊢ x₀ ↝ x₁}
      → {g₀ g₁ : A ▸ 1 ⊢ y₀ ↝ y₁}
      → (α : A ▸ 2 ⊢ f₀ ↝ f₁)
      → (β : A ▸ 2 ⊢ g₀ ↝ g₁)
      → A ▸ 2 ⊢ f₀ ⊛₁ g₀ ↝ f₁ ⊛₁ g₁
    _⊛₂_ α β = ap₀₂ ten (α , β)

    field
      ≅λ
        : A ⇒₀ A
        ⊢ ⟨ Δ.ʲ[ 𝟙₀ ] , ↻₀ ⟩ ⟓₀ ten
        ≅ ↻₀
      ≅ρ
        : A ⇒₀ A
        ⊢ ⟨ ↻₀ , Δ.ʲ[ 𝟙₀ ] ⟩ ⟓₀ ten
        ≅ ↻₀
      ≅α
        : A ⊗ A ⊗ A ⇒₀ A
        ⊢ ⟨ ↻₀ ⊗ ten ⟩ ⟓₀ ten
        ≅ ⟨ ten ⊗ ↻₀ ⟩ ⟓₀ ten ⟔₀ ⊗.⊢.α⇐

    λ₀ : {x : A ▸} → _
    λ₀ {x} = ap₁₀ (» ≅λ) x

    ρ₀ : {x : A ▸} → _
    ρ₀ {x} = ap₁₀ (» ≅ρ) x

    α₀ : {x y z : A ▸} → _
    α₀ {x}{y}{z} = ap₁₀ (» ≅α) (x , y , z)

    field
      ⊢tri
        : {x y : A ▸} →
        ● (⇇ (⇇ [ A ] (x ⊛₀ (𝟙₀ ⊛₀ y)) (x ⊛₀ y))
          (seq₀ A α₀ (ρ₀ ⊛₁ idn₀ A))
          (idn₀ A ⊛₁ λ₀))
      ⊢pnt
        : {w x y z : A ▸} →
        ● (⇇ (⇇ [ A ] (w ⊛₀ (x ⊛₀ (y ⊛₀ z))) (((w ⊛₀ x) ⊛₀ y) ⊛₀ z))
          (seq₀ A α₀ α₀)
          (seq₀ A
            (idn₀ A ⊛₁ α₀)
            (seq₀ A α₀ (α₀ ⊛₁ idn₀ A))))

  module _ where
    open Monoidal
    {-# DISPLAY one A = 𝟙 #-}
    {-# DISPLAY ten A = ⊛ #-}
    {-# DISPLAY _⊛₀_ A = _⊛_ #-}
    {-# DISPLAY _⊛₁_ A = _⊛_ #-}
    {-# DISPLAY _⊛₂_ A = _⊛_ #-}

  record Monoid {r}..{ℓ}
    {A : 𝔘 r ℓ}
    (Ψ : Monoidal A)
    : Set ℓ
    where
    no-eta-equality
    open Monoidal Ψ
    field
      mon : A ▸
    field
      mul : A ▸ 1 ⊢ mon ⊛₀ mon ↝ mon
      nil : A ▸ 1 ⊢ 𝟙₀ ↝ mon
    field
      ⊢α : A ▸ 2 ⊢ seq₀ A α₀ (seq₀ A (mul ⊛₁ idn₀ A) mul) ↝ seq₀ A (idn₀ A ⊛₁ mul) mul
      ⊢λ : A ▸ 2 ⊢ seq₀ A (nil ⊛₁ idn₀ A) mul ↝ λ₀
      ⊢ρ : A ▸ 2 ⊢ seq₀ A (idn₀ A ⊛₁ nil) mul ↝ ρ₀

  Comonoid
    : ∀ {r}..{ℓ}
    → {A : 𝔘 r ℓ}
    → (Ψ : Monoidal Op[ A ])
    → Set ℓ
  Comonoid = Monoid

  module Endo ..{ℓ} (A : 𝔘 1 ℓ) where
    Endo : 𝔘 1 (lsuc ℓ)
    Endo = A ⇒₀ A

    private
      module Endo where
        one : Hom₀ A A
        one = ↻₀

        ten : Hom₀ ((A ⇒₀ A) ⊗ (A ⇒₀ A)) (A ⇒₀ A)
        ap₀₀ ten (F , G) =
          F ⟓₀ G
        ap₀₁ ten (α , β) =
          seq₀*→ α β
        ap₀₂ ten
          {F₀ , G₀}{F₁ , G₁}
          {α₀ , β₀}{α₁ , β₁}
          (ι 𝔣 , ι 𝔤)
          =
          ι λ a → seq₀* A (ap₀₂ G₀ (𝔣 a)) (𝔤 (ap₀₀ F₁ a))
        ⇒₀.⊢idn ten {F , G} =
          ι λ a → seq₁ A (seq₀*-λ A (⇒₀.⊢idn G)) (⊢idn₀-λ A)
        ⇒₀.⊢seq ten
          {F₀ , G₀}{F₁ , G₁}{F₂ , G₂}
          {α₀ , β₀}{α₁ , β₁}
          =
          ι λ a →
            (seq₁ A
              (seq₀*-λ A (⇒₀.⊢seq G₀))
              (seq₁ A
                (inv₁ A (⊢seq₀-α A))
                (seq₁ A
                  (seq₀*-ρ A
                    (seq₁ A
                      (⊢seq₀-α A)
                      (seq₁ A
                        (seq₀*-λ A (ap₁₁ β₀ (ap₁₀ α₁ a)))
                        (inv₁ A (⊢seq₀-α A)))))
                  (⊢seq₀-α A))))
        ⇒₀.⊢inv ten {≜ = ()}

    open Monoid
    open Monoidal

    endo : Monoidal Endo
    one endo =
      Endo.one
    ten endo =
      Endo.ten
    ap₁₀ (» (≅λ endo)) F =
      » (⊢idn₀-λ («Cat» _ _))
    ap₁₁ (» (≅λ endo)) {F}{G} α =
      ι λ a →
        (seq₁ A
          (⊢idn₀-ρ A)
          (seq₀*-λ A (⇒₀.⊢idn F)))
    ap₁₀ (« (≅λ endo)) F =
      « (⊢idn₀-λ («Cat» _ _))
    ap₁₁ (« (≅λ endo)) {F}{G} α =
      ι λ a →
        (seq₁ A
          (⊢idn₀-ρ A)
          (inv₁ A
            (seq₁ A
              (⊢idn₀-λ A)
              (seq₁ A
                (seq₀*-λ A (⇒₀.⊢idn F))
                (⊢idn₀-λ A)))))
    ⊢»« (≅λ endo) =
      ι λ F →
      ι λ a →
        ⊢idn₀-λ A
    ⊢«» (≅λ endo) =
      ι λ F →
      ι λ a →
        ⊢idn₀-λ A
    ap₁₀ (» (≅ρ endo)) F =
      » (⊢idn₀-ρ («Cat» _ _))
    ap₁₁ (» (≅ρ endo)) {F}{G} α =
      ι λ a →
        (seq₁ A
          (⊢idn₀-ρ A)
          (seq₁ A
            (⊢idn₀-ρ A)
            (inv₁ A (⊢idn₀-λ A))))
    ap₁₀ (« (≅ρ endo)) F =
      « (⊢idn₀-ρ («Cat» _ _))
    ap₁₁ (« (≅ρ endo)) {F}{G} α =
      ι λ a →
        (inv₁ A
          (⊢idn₀-λ A))
    ⊢»« (≅ρ endo) =
      ι λ F →
      ι λ a →
        ⊢idn₀-λ A
    ⊢«» (≅ρ endo) =
      ι λ F →
      ι λ a →
        ⊢idn₀-λ A
    ap₁₀ (» (≅α endo)) (F , G , H) =
      » (⊢seq₀-α («Cat» _ _))
    ap₁₁ (» (≅α endo))
      {F₀ , G₀ , H₀}
      {F₁ , G₁ , H₁}
      (α , β , γ)
      =
      ι λ a →
        (seq₁ A
          (⊢idn₀-ρ A)
          (inv₁ A
            (seq₁ A
              (⊢idn₀-λ A)
              (seq₁ A
                (seq₀*-λ A (⇒₀.⊢seq H₀))
                (inv₁ A (⊢seq₀-α A))))))
    ap₁₀ (« (≅α endo)) (F , G , H) =
      « (⊢seq₀-α («Cat» _ _))
    ap₁₁ (« (≅α endo))
      {F₀ , G₀ , H₀}
      {F₁ , G₁ , H₁}
      (α , β , γ)
      =
      ι λ a →
        (seq₁ A
          (⊢idn₀-ρ A))
          (inv₁ A
            (seq₁ A
              (⊢idn₀-λ A)
              (seq₁ A
                (⊢seq₀-α A)
                (seq₀*-λ A
                  (inv₁ A
                    (⇒₀.⊢seq H₀))))))
    ⊢»« (≅α endo) =
      ι λ F →
      ι λ a →
        ⊢idn₀-λ A
    ⊢«» (≅α endo) =
      ι λ F →
      ι λ a →
        ⊢idn₀-λ A
    ⊢tri endo {F}{G} =
      ι λ a →
        ⊢idn₀-λ A
    ⊢pnt endo {F}{G}{H}{K} =
      ι λ a →
      (inv₁ A
        (seq₀* A
          (seq₁ A
            (⊢idn₀-ρ A)
            (⇒₀.⊢idn (K ⟔₀ H ⟔₀ G)))
          (seq₁ A
            (⊢idn₀-λ A)
            (seq₁ A
              (⊢idn₀-ρ A)
              (⇒₀.⊢idn K)))))
  open Endo

  Monad : ∀ ..{ℓ} (A : 𝔘 1 ℓ) → Set (lsuc ℓ)
  Monad A = Monoid (endo A)

  open Monoid public
  open Monoidal public
open Monoidal public
  hiding (module Monoidal)
  using (Monoidal)
  using (Monoid)
