{-# OPTIONS --without-K #-}

module Groupoids.Basis where

open import Globular.Common public
  hiding (_▸_)
open import Globular public

open T public
  using (ι) -- ⊔⇑

pattern 1+[_] n = su (ℕ∞.ι n)
pattern 2+[_] n = 1+[ su (ℕ∞.ι n) ]
