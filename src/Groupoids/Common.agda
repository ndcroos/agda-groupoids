{-# OPTIONS --without-K #-}

module Groupoids.Common where

open import Globular.Common public
  hiding (_▸_)
open import Globular public

pattern 1+ n =     su (ℕ∞.ι n)
pattern 2+ n = 1+ (su (ℕ∞.ι n))
