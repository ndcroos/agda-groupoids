{-# OPTIONS --without-K #-}

module Groupoids.Ordinary.Ambient.Cosmos.Unit.Terminal where

open import Groupoids.Basis
open import Groupoids.Ordinary.Ambient.Universe.Boot

module 𝟙 where
  𝟙↑
    : ∀ {r}..{ℓ}
    → 𝔘 r ℓ
  [ 𝟙↑ ] = 𝔊.𝟙↑
  idn₀ 𝟙↑ = _
  seq₀ 𝟙↑ = _
  inv₀ 𝟙↑ = _
  seq₀* 𝟙↑ = _
  inv₀* 𝟙↑ = _
  ⊢idn₀-λ 𝟙↑ = _
  ⊢idn₀-ρ 𝟙↑ = _
  ⊢seq₀-α 𝟙↑ = _
  ⊢inv₀-λ 𝟙↑ = _
  ⊢inv₀-ρ 𝟙↑ = _
  idn₁ 𝟙↑ = _
  seq₁ 𝟙↑ = _
  inv₁ 𝟙↑ = _

  𝟙
    : ∀ {r}
    → 𝔘 r lzero
  𝟙 = 𝟙↑

open 𝟙 public
