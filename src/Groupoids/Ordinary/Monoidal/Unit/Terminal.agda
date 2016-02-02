{-# OPTIONS --without-K #-}

module Groupoids.Ordinary.Monoidal.Unit.Terminal where

open import Groupoids.Common
open import Groupoids.Ordinary.Universe.Boot

module 𝟙 where
  𝟙↑
    : ∀ {r}..{ℓ}
    → 𝔘 r ℓ
  𝟙↑ = record { [_] = 𝔊.𝟙↑ }

  𝟙
    : ∀ {r}
    → 𝔘 r lzero
  𝟙 = 𝟙↑

open 𝟙 public
