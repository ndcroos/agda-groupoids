{-# OPTIONS --without-K #-}

module Groupoids.Ordinary.Construction.Comma where

open import Groupoids.Common
open import Groupoids.Ordinary.Homomorphism.Boot
open import Groupoids.Ordinary.Universe.Boot

module Comma where
  open Fun₀

  _↓_
    : ∀ {n r}..{ℓ₀ ℓ₁ ℓ₂}
    → {A : 𝔘 n r ℓ₀}
    → {B : 𝔘 n r ℓ₁}
    → {V : 𝔘 n r ℓ₂}
    → (F : Fun₀ A V)
    → (G : Fun₀ B V)
    → 𝔘 n r _
  ● [ _↓_ {A = A}{B}{V} F G ]
    =
    T.Σ ((A ▸) T.⊗ (B ▸)) λ { (a , b) →
      V ▸ 1 ⊢ ap₀₀ F a ↝ ap₀₀ G b
    }
  ● (⇇ [ _↓_ {A = A}{B}{V} F G ]
    ((a₀ , b₀) T.▸ f₀)
    ((a₁ , b₁) T.▸ f₁))
    =
    T.Σ ((A ▸ 1 ⊢ a₀ ↝ a₁) T.⊗ (B ▸ 1 ⊢ b₀ ↝ b₁)) λ { (g , h) →
      V ▸ 2 ⊢ seq₀ V (ap₀₁ F g) f₁ ↝ seq₀ V f₀ (ap₀₁ G h)
    }
  ● (⇇ (⇇ [ _↓_ {ℓ₂ = ℓ₂}{A = A}{B}{V} F G ]
    ((a₀ , b₀) T.▸ f₀)
    ((a₁ , b₁) T.▸ f₁))
    ((α₀ , β₀) T.▸ φ)
    ((α₁ , β₁) T.▸ ψ))
    =
    T.⊔⇑ ℓ₂ ((A ▸ 2 ⊢ α₀ ↝ α₁) T.⊗ (B ▸ 2 ⊢ β₀ ↝ β₁))
  ⇇ (⇇ (⇇ [ F ↓ G ]
    ((a₀ , b₀) T.▸ f₀)
    ((a₁ , b₁) T.▸ f₁))
    ((α₀ , β₀) T.▸ φ)
    ((α₁ , β₁) T.▸ ψ))
    _
    _
    =
    𝔊.𝟙↑
  ↻ (⇇ (⇇ [ F ↓ G ]
    ((a₀ , b₀) T.▸ f₀)
    ((a₁ , b₁) T.▸ f₁))
    ((α₀ , β₀) T.▸ φ)
    ((α₁ , β₁) T.▸ ψ))
    =
    *
  ↻ (⇇ [ _↓_ {A = A}{B} F G ]
    ((a₀ , b₀) T.▸ f₀)
    ((a₁ , b₁) T.▸ f₁))
    {_}
    {(α , β) T.▸ φ}
    =
    ι (idn₁ A , idn₁ B)
  ↻ [ _↓_ {A = A}{B}{V} F G ]
    {_}
    {(a₀ , b₀) T.▸ f₀}
    =
    (idn₀ A , idn₀ B) T.▸
    (seq₁ V
      (seq₀*-λ V (⊢idn F))
      (seq₁ V
        (⊢idn₀-λ V)
        (inv₁ V
          (seq₁ V
            (seq₀*-ρ V (⊢idn G))
            (⊢idn₀-ρ V)))))
  seq₀ (_↓_ {A = A}{B}{V} F G)
    {(a₀ , b₀) T.▸ f₀}{(a₁ , b₁) T.▸ f₁}{(a₂ , b₂) T.▸ f₂}
    ((α₀ , β₀) T.▸ φ)((α₁ , β₁) T.▸ ψ)
    =
    (seq₀ A α₀ α₁ , seq₀ B β₀ β₁) T.▸
    (seq₁ V
      (seq₀*-λ V (⊢seq F))
      (seq₁ V
        (inv₁ V (⊢seq₀-α V))
        (seq₁ V
          (seq₀*-ρ V ψ)
          (seq₁ V
            (⊢seq₀-α V)
            (seq₁ V
              (seq₀*-λ V φ)
              (seq₁ V
                (inv₁ V (⊢seq₀-α V))
                (seq₀*-ρ V (inv₁ V (⊢seq G)))))))))
  inv₀ (_↓_ {A = A}{B}{V} F G)
    -- {(a₀ , b₀) T.▸ f₀}{(a₁ , b₁) T.▸ f₁}
    ((α₀ , β₀) T.▸ φ)
    {≜}
    =
    (inv₀ A α₀ {≜} , inv₀ B β₀ {≜}) T.▸
    seq₁ V
      (inv₁ V (⊢idn₀-ρ V))
      (seq₁ V
        (seq₀*-ρ V (inv₁ V (⊢inv₀-ρ V {f = ap₀₁ G β₀})))
        (seq₁ V
          (inv₁ V (⊢seq₀-α V))
          (seq₁ V
            (seq₀*-ρ V
              (seq₁ V
                (⊢seq₀-α V)
                (seq₀*-λ V (inv₁ V φ))))
            (seq₁ V
              (⊢seq₀-α V)
              (seq₁ V
                (seq₀*-λ V
                  (seq₁ V
                    (⊢seq₀-α V)
                    (seq₁ V
                      (seq₀*-λ V
                        (seq₁ V
                          (inv₁ V (⊢seq F))
                          (seq₁ V
                            (ap₀₂ F (⊢inv₀-λ A))
                            (⊢idn F))))
                      (⊢idn₀-λ V))))
                (seq₀*-ρ V (inv₁ V (⊢inv G))))))))
  seq₀* (_↓_ {A = A}{B}{V} F G)
    -- {(a₀ , b₀) T.▸ f₀}{(a₁ , b₁) T.▸ f₁}{(a₂ , b₂) T.▸ f₂}
    -- {(α₀₀ , β₀₀) T.▸ φ₀}{(α₀₁ , β₀₁) T.▸ ψ₀}{(α₁₀ , β₁₀) T.▸ φ₁}{(α₁₁ , β₁₁) T.▸ ψ₁}
    (ι (Φ₀ , Ψ₀))(ι (Φ₁ , Ψ₁))
    =
    ι (seq₀* A Φ₀ Φ₁ , seq₀* B Ψ₀ Ψ₁)
  inv₀* (_↓_ {A = A}{B}{V} F G)
    -- {(a₀ , b₀) T.▸ f₀}{(a₁ , b₁) T.▸ f₁}
    -- {(α₀ , β₀) T.▸ φ}{(α₁ , β₁) T.▸ ψ}
    (ι (Φ , Ψ))
    =
    ι (inv₀* A Φ , inv₀* B Ψ)
  ⊢idn₀-λ (_↓_ {A = A}{B}{V} F G)
    -- {(a₀ , b₀) T.▸ f₀}{(a₁ , b₁) T.▸ f₁}
    -- {(α , β) T.▸ φ}
    =
    ι (⊢idn₀-λ A , ⊢idn₀-λ B)
  ⊢idn₀-ρ (_↓_ {A = A}{B}{V} F G)
    -- {(a₀ , b₀) T.▸ f₀}{(a₁ , b₁) T.▸ f₁}
    -- {(α , β) T.▸ φ}
    =
    ι (⊢idn₀-ρ A , ⊢idn₀-ρ B)
  ⊢seq₀-α (_↓_ {A = A}{B}{V} F G)
    -- {(a₀ , b₀) T.▸ f₀}{(a₁ , b₁) T.▸ f₁}{(a₂ , b₂) T.▸ f₂}{(a₃ , b₃) T.▸ f₃}
    -- {(α₀ , β₀) T.▸ φ₀}{(α₁ , β₁) T.▸ φ₁}{(α₂ , β₂) T.▸ φ₂}
    =
    ι (⊢seq₀-α A , ⊢seq₀-α B)
  ⊢inv₀-λ (_↓_ {A = A}{B}{V} F G)
    -- {(a₀ , b₀) T.▸ f₀}{(a₁ , b₁) T.▸ f₁}
    -- {(α , β) T.▸ φ}
    {≜ = ≜}
    =
    ι (⊢inv₀-λ A {≜ = ≜} , ⊢inv₀-λ B {≜ = ≜})
  ⊢inv₀-ρ (_↓_ {A = A}{B}{V} F G)
    -- {(a₀ , b₀) T.▸ f₀}{(a₁ , b₁) T.▸ f₁}
    -- {(α , β) T.▸ φ}
    {≜ = ≜}
    =
    ι (⊢inv₀-ρ A {≜ = ≜} , ⊢inv₀-ρ B {≜ = ≜})
  idn₁ (_↓_ {A = A}{B}{V} F G)
    -- {(a₀ , b₀) T.▸ f₀}{(a₁ , b₁) T.▸ f₁}
    -- {(α , β) T.▸ φ}
    =
    ι (idn₁ A , idn₁ B)
  seq₁ (_↓_ {A = A}{B}{V} F G)
    -- {(a₀ , b₀) T.▸ f₀}{(a₁ , b₁) T.▸ f₁}
    -- {(α₀ , β₀) T.▸ φ₀}{(α₁ , β₁) T.▸ φ₁}{(α₂ , β₂) T.▸ φ₂}
    (ι (Φ₀ , Ψ₀))
    (ι (Φ₁ , Ψ₁))
    =
    ι (seq₁ A Φ₀ Φ₁ , seq₁ B Ψ₀ Ψ₁)
  inv₁ (_↓_ {A = A}{B}{V} F G)
    -- {(a₀ , b₀) T.▸ f₀}{(a₁ , b₁) T.▸ f₁}
    -- {(α₀ , β₀) T.▸ φ₀}{(α₁ , β₁) T.▸ φ₁}
    (ι (Φ , Ψ))
    =
    ι (inv₁ A Φ , inv₁ B Ψ)

open Comma public
  using (_↓_)
