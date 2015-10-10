{-# OPTIONS --without-K #-}

module Setoid.Core.Homotopy where

open import Agda.Primitive
import Setoid.Core.Base as S
import Setoid.Core.Discrete as Discrete
import Setoid.Core.Hom.Boot as Π
import Setoid.Core.Terminal as 𝟙
open import Type as T
  using (_,_)

infixr 0 _⇒₁_

record _⇒₁_
  {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ}
  {A : S.t d ℓ₀ᵒ ℓ₀ʰ}
  {B : S.t d ℓ₁ᵒ ℓ₁ʰ}
  (F G : A Π.⇒₀ᵗ B)
    : Set (ℓ₀ᵒ ⊔ ℓ₁ʰ) where
  no-eta-equality
  field
    .com₁
      : ∀ {a}
      → S.homᵗ B (F Π.$₀ a , G Π.$₀ a)
open _⇒₁_ public

.com₁ᵗ′
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ}
  → {A : S.t d ℓ₀ᵒ ℓ₀ʰ}
  → {B : S.t d ℓ₁ᵒ ℓ₁ʰ}
  → {F G : A Π.⇒₀ᵗ B}
  → ∀ {a} (α : F ⇒₁ G)
  → S.homᵗ B (F Π.$₀ a , G Π.$₀ a)
com₁ᵗ′ α = com₁ α

idnᵗ
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ}
  → {A : S.t d ℓ₀ᵒ ℓ₀ʰ}
  → {B : S.t d ℓ₁ᵒ ℓ₁ʰ}
  → (F : A Π.⇒₀ᵗ B)
  → T.𝟙.t T.Π.⇒₀ (F ⇒₁ F)
com₁ (idnᵗ {B = B} F x) = S.idnᵗ B x

cmpᵗ
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ}
  → {A : S.t d ℓ₀ᵒ ℓ₀ʰ}
  → {B : S.t d ℓ₁ᵒ ℓ₁ʰ}
  → {F G H : A Π.⇒₀ᵗ B}
  → (G ⇒₁ H) T.∐.⊗ (F ⇒₁ G)
  → F ⇒₁ H
com₁ (cmpᵗ {B = B} (β , α)) =
  S.cmpᵗ B (com₁ β , com₁ α)

invᵗ
  : ∀ ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ}
  → {A : S.t S.Dir.≈ ℓ₀ᵒ ℓ₀ʰ}
  → {B : S.t S.Dir.≈ ℓ₁ᵒ ℓ₁ʰ}
  → {F G : A Π.⇒₀ᵗ B}
  → (F ⇒₁ G) T.Π.⇒₀ (G ⇒₁ F)
com₁ (invᵗ {B = B} α) = S.invᵗ B (com₁ α)

cmpᵗ-w₀
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ ℓ₂ᵒ ℓ₂ʰ }
  → {A : S.t d ℓ₀ᵒ ℓ₀ʰ}
  → {B : S.t d ℓ₁ᵒ ℓ₁ʰ}
  → {C : S.t d ℓ₂ᵒ ℓ₂ʰ}
  → {F G : A Π.⇒₀ᵗ B}
  → (Hα : (B Π.⇒₀ᵗ C) T.∐.⊗ (F ⇒₁ G))
  → (T.∐.π₀ Hα Π.∘ᵗ F) ⇒₁ (T.∐.π₀ Hα Π.∘ᵗ G)
com₁ (cmpᵗ-w₀ (H , α)) = H Π.$₁ com₁ α

cmpᵗ-w₁
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ ℓ₂ᵒ ℓ₂ʰ}
  → {A : S.t d ℓ₀ᵒ ℓ₀ʰ}
  → {B : S.t d ℓ₁ᵒ ℓ₁ʰ}
  → {C : S.t d ℓ₂ᵒ ℓ₂ʰ}
  → {G H : B Π.⇒₀ᵗ C}
  → (βF : (G ⇒₁ H) T.∐.⊗ (A Π.⇒₀ᵗ B))
  → (G Π.∘ᵗ T.∐.π₁ βF) ⇒₁ (H Π.∘ᵗ T.∐.π₁ βF)
com₁ (cmpᵗ-w₁ (β , F)) = com₁ β

cmpᵗ-h₀
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ ℓ₂ᵒ ℓ₂ʰ}
  → {A : S.t d ℓ₀ᵒ ℓ₀ʰ}
  → {B : S.t d ℓ₁ᵒ ℓ₁ʰ}
  → {C : S.t d ℓ₂ᵒ ℓ₂ʰ}
  → {F G : A Π.⇒₀ᵗ B}
  → {H K : B Π.⇒₀ᵗ C}
  → (βα : (H ⇒₁ K) T.∐.⊗ (F ⇒₁ G))
  → (H Π.∘ᵗ F) ⇒₁ (K Π.∘ᵗ G)
com₁ (cmpᵗ-h₀ {C = C} {K = K} (β , α)) =
  S.cmpᵗ C (K Π.$₁ com₁ α , com₁ β)

cmpᵗ-h₁
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ ℓ₂ᵒ ℓ₂ʰ}
  → {A : S.t d ℓ₀ᵒ ℓ₀ʰ}
  → {B : S.t d ℓ₁ᵒ ℓ₁ʰ}
  → {C : S.t d ℓ₂ᵒ ℓ₂ʰ}
  → {F G : A Π.⇒₀ᵗ B}
  → {H K : B Π.⇒₀ᵗ C}
  → (βα : (H ⇒₁ K) T.∐.⊗ (F ⇒₁ G))
  → (H Π.∘ᵗ F) ⇒₁ (K Π.∘ᵗ G)
com₁ (cmpᵗ-h₁ {C = C} {H = H} (β , α)) =
  S.cmpᵗ C (com₁ β , H Π.$₁ com₁ α)