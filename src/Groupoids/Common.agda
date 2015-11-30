{-# OPTIONS --without-K #-}

module Groupoids.Common where

open import Agda.Primitive

module Dir where
  data t : Set where
    ≤ ≈ : t

  el
    : ∀ ..{ℓ}
    → {Φ : t → Set ℓ}
    → (d : t)
    → (`≤ : Φ ≤)
    → (`≈ : Φ ≈)
    → Φ d
  el ≤ `≤ `≈ = `≤
  el ≈ `≤ `≈ = `≈
