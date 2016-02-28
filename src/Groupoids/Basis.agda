{-# OPTIONS --without-K #-}

module Groupoids.Basis where

open import Globular.Common public
  hiding (_▸_)
open import Globular public

open T public
  using (ι) -- ⊔⇑

module ℕ where
  open import Prelude.Natural
  open Nat public
    renaming (Nat to ℕ)
open ℕ public
  using (ℕ)

pattern 1+[_] n = su (ℕ∞.ι n)
pattern 2+[_] n = 1+[ su (ℕ∞.ι n) ]

infix 2 _⟓*_
infix 2 _⟓_
infix 2 _⟔_
infix 4 _⁻¹

_⁻¹ = #display
_⁻¹* = #display
_⊛_ = #display
_⟓*_ = #display
_⟓_ = #display
_⟔_ = #display
↻ = #display
⊛ = #display
