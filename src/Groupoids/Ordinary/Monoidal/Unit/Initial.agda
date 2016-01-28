{-# OPTIONS --without-K #-}

module Groupoids.Ordinary.Monoidal.Unit.Initial where

open import Groupoids.Common
open import Groupoids.Ordinary.Universe.Boot

module 𝟘 where
  𝟘↑
    : ∀ {n r}..{ℓ}
    → 𝔘 n r ℓ
  [ 𝟘↑ ] = 𝔊.𝟘↑
  seq₀ 𝟘↑ {()}
  inv₀ 𝟘↑ {()}
  seq₀* 𝟘↑ {()}
  inv₀* 𝟘↑ {()}
  ⊢λ₀ 𝟘↑ {()}
  ⊢ρ₀ 𝟘↑ {()}
  ⊢α₀ 𝟘↑ {()}
  ⊢λ₀⁻¹ 𝟘↑ {()}
  ⊢ρ₀⁻¹ 𝟘↑ {()}
  idn₁ 𝟘↑ {()}
  seq₁ 𝟘↑ {()}
  inv₁ 𝟘↑ {()}

  𝟘
    : ∀ {n r}
    → 𝔘 n r lzero
  𝟘 = 𝟘↑

open 𝟘 public
