{-# OPTIONS --without-K #-}

module Groupoids.Core.Groupoid.Ordinary.Universe where

open import Groupoids.Common

module 𝔘 where
  open import Groupoids.Core.Groupoid.Ordinary.Universe.Boot public

  Std : ∀ ..ℓ → Set _
  Std ℓ = 𝔘 0 ze ℓ

  Gpd : ∀ ..ℓ → Set _
  Gpd ℓ = 𝔘 1 ze ℓ

  Cat : ∀ ..ℓ → Set _
  Cat ℓ = 𝔘 1 (su ze) ℓ

open 𝔘 public
