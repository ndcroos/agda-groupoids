{-# OPTIONS --without-K #-}

module Groupoids.Core.Groupoid.Ordinary.Universe where

open import Groupoids.Common

module 𝔘 where
  open import Groupoids.Core.Groupoid.Ordinary.Universe.Boot public

  Std : ∀ ..ℓ → Set _
  Std ℓ = 𝔘 0 0 ℓ

  Gpd : ∀ ..ℓ → Set _
  Gpd ℓ = 𝔘 1 0 ℓ

  Cat : ∀ ..ℓ → Set _
  Cat ℓ = 𝔘 1 1 ℓ

open 𝔘 public
