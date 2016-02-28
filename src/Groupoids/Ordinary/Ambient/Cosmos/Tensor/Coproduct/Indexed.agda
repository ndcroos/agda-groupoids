module Groupoids.Ordinary.Ambient.Cosmos.Tensor.Coproduct.Indexed where

open import Groupoids.Basis
open import Groupoids.Ordinary.Ambient.Cosmos.Tensor.Coproduct
open import Groupoids.Ordinary.Ambient.Morphism.Hom.Boot
open import Groupoids.Ordinary.Ambient.Universe.Boot

module Σ where
  infix 0 Σ

  Σ : ∀ {n r}..{ℓ₀ ℓ₁}
    → (I : Set ℓ₀)
    → (A : I → 𝔘 n r ℓ₁)
    → 𝔘 n r _
  [ Σ I A ] =
    𝔊.Σ.[ I ∋ i ] [ A i ]
  idn₀ (Σ I A)
    {i T.▸ a}
    =
    T.≡.idn 𝔊.▸ idn₀ (A i)
  seq₀ (Σ I A)
    {i T.▸ a}{.i T.▸ b}{.i T.▸ c}
    (T.≡.idn 𝔊.▸ f) (T.≡.idn T.▸ g)
    =
    T.≡.idn 𝔊.▸ seq₀ (A i) f g
  inv₀ (Σ I A)
    {i T.▸ a}{.i T.▸ b}
    (T.≡.idn 𝔊.▸ f)
    {≜}
    =
    T.≡.idn 𝔊.▸ inv₀ (A i) f {≜}
  seq₀* (Σ I A)
    {i T.▸ a}{.i T.▸ b}{.i T.▸ c}
    {T.≡.idn 𝔊.▸ f₀}{T.≡.idn 𝔊.▸ f₁}{T.≡.idn 𝔊.▸ g₀}{T.≡.idn 𝔊.▸ g₁}
    (T.≡.idn 𝔊.▸ α)(T.≡.idn 𝔊.▸ β)
    =
    T.≡.idn 𝔊.▸ seq₀* (A i) α β
  inv₀* (Σ I A)
    {i T.▸ a}{.i T.▸ b}
    {T.≡.idn 𝔊.▸ f}{T.≡.idn 𝔊.▸ g}
    (T.≡.idn 𝔊.▸ α)
    {≜}
    =
    T.≡.idn 𝔊.▸ inv₀* (A i) α {≜}
  ⊢idn₀-λ (Σ I A)
    {i T.▸ a}{.i T.▸ b}
    {T.≡.idn 𝔊.▸ f}
    =
    T.≡.idn 𝔊.▸ ⊢idn₀-λ (A i)
  ⊢idn₀-ρ (Σ I A)
    {i T.▸ a}{.i T.▸ b}
    {T.≡.idn 𝔊.▸ f}
    =
    T.≡.idn 𝔊.▸ ⊢idn₀-ρ (A i)
  ⊢seq₀-α (Σ I A)
    {i T.▸ a}{.i T.▸ b}{.i T.▸ c}{.i T.▸ d}
    {T.≡.idn 𝔊.▸ f}{T.≡.idn 𝔊.▸ g}{T.≡.idn 𝔊.▸ h}
    =
    T.≡.idn 𝔊.▸ ⊢seq₀-α (A i)
  ⊢inv₀-λ (Σ I A)
    {i T.▸ a}{.i T.▸ b}
    {T.≡.idn 𝔊.▸ f}
    {≜ = ≜}
    =
    T.≡.idn 𝔊.▸ ⊢inv₀-λ (A i) {≜ = ≜}
  ⊢inv₀-ρ (Σ I A)
    {i T.▸ a}{.i T.▸ b}
    {T.≡.idn 𝔊.▸ f}
    {≜ = ≜}
    =
    T.≡.idn 𝔊.▸ ⊢inv₀-ρ (A i) {≜ = ≜}
  idn₁ (Σ I A)
    {i T.▸ a}{.i T.▸ b}
    {T.≡.idn 𝔊.▸ f}
    =
    T.≡.idn 𝔊.▸ idn₁ (A i)
  seq₁ (Σ I A)
    {i T.▸ a}{.i T.▸ b}
    {T.≡.idn 𝔊.▸ f}{T.≡.idn 𝔊.▸ g}{T.≡.idn 𝔊.▸ h}
    (T.≡.idn 𝔊.▸ α)(T.≡.idn 𝔊.▸ β)
    =
    T.≡.idn 𝔊.▸ seq₁ (A i) α β
  inv₁ (Σ I A)
    {i T.▸ a}{.i T.▸ b}
    {T.≡.idn 𝔊.▸ f}{T.≡.idn 𝔊.▸ g}
    (T.≡.idn 𝔊.▸ α)
    =
    T.≡.idn 𝔊.▸ inv₁ (A i) α

  syntax Σ I (λ i → A) = [ I ∋ i ] A

open Σ public
  using (Σ)
