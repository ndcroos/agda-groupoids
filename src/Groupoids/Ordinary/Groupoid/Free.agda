{-# OPTIONS --without-K #-}

module Groupoids.Ordinary.Groupoid.Free where

open import Groupoids.Basis
open import Groupoids.Ordinary.Ambient.Universe.Boot
open import Prelude.Natural

module Free {n} (A : 𝔘 n 1 lzero) where

  infixl 1 _▸_
  infixl 5 _++_

  data Path (σ : ● [ A ]) : (τ : ● [ A ]) → Set where
    []
      : Path σ σ
    _▸_
      : ∀ {τ₀ τ₁}
      → (π : Path σ τ₀)
      → (f : ● (⇇ [ A ] τ₀ τ₁))
      → Path σ τ₁

  _++_
    : ∀ {σ τ₀ τ₁}
    → Path σ τ₀
    → Path τ₀ τ₁
    → Path σ τ₁
  π₁ ++ []  = π₁
  π₁ ++ (π₀ ▸ f) = (π₁ ++ π₀) ▸ f

  path-⊢idn₀-λ
    : ∀ {σ τ}
    → {π : Path σ τ}
    → [] ++ π T.≡ π
  path-⊢idn₀-λ {π = []} = T.≡.idn
  path-⊢idn₀-λ {π = π ▸ f} = T.≡.ap¹ (λ x → x ▸ f) path-⊢idn₀-λ

  path-⊢idn₀-ρ
    : ∀ {σ τ}
    → {π : Path σ τ}
    → π ++ [] T.≡ π
  path-⊢idn₀-ρ = T.≡.idn

  path-⊢seq₀-α
    : ∀ {σ τ₀ τ₁ τ₂}
    → {π₀ : Path σ  τ₀}
    → {π₁ : Path τ₀ τ₁}
    → {π₂ : Path τ₁ τ₂}
    → π₀ ++ (π₁ ++ π₂) T.≡ (π₀ ++ π₁) ++ π₂
  path-⊢seq₀-α {π₂ = []} = T.≡.idn
  path-⊢seq₀-α {π₂ = π₂ ▸ f} = T.≡.ap¹ (λ x → x ▸ f) (path-⊢seq₀-α {π₂ = π₂})

  Free : 𝔘 n 1 lzero
  ● [ Free ] = ● [ A ]
  ● (⇇ [ Free ] x y) = Path x y
  ⇇ (⇇ [ Free ] x y) π₀ π₁ = 𝔊.ℼ[ π₀ T.≡ π₁ ]
  idn₀ Free = []
  seq₀ Free = _++_
  inv₀ Free f {≜ = ()}
  seq₀* Free T.refl T.refl = T.≡.idn
  inv₀* Free α {≜ = ()}
  ⊢idn₀-λ Free = path-⊢idn₀-λ
  ⊢idn₀-ρ Free = path-⊢idn₀-ρ
  ⊢seq₀-α Free {f = π₀}{π₁}{π₂} = path-⊢seq₀-α {π₀ = π₀}{π₁}{π₂}
  ⊢inv₀-λ Free {≜ = ()}
  ⊢inv₀-ρ Free {≜ = ()}
  idn₁ Free = T.≡.idn
  seq₁ Free T.≡.idn T.≡.idn = T.≡.idn
  inv₁ Free T.≡.idn = T.≡.idn
