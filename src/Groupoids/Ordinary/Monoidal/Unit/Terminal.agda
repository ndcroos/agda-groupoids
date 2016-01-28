{-# OPTIONS --without-K #-}

module Groupoids.Ordinary.Monoidal.Unit.Terminal where

open import Groupoids.Common
open import Groupoids.Ordinary.Universe.Boot

module 𝟙 where
  𝟙↑
    : ∀ {n r}..{ℓ}
    → 𝔘 n r ℓ
  𝟙↑ = record { [_] = 𝔊.𝟙↑ }

  𝟙
    : ∀ {n r}
    → 𝔘 n r lzero
  𝟙 = 𝟙↑

open 𝟙 public
