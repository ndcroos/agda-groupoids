{-# OPTIONS --without-K #-}

module Groupoids.Common where

open import Globular.Common public
  hiding (_▸_)
open import Globular public

open T public
  using (ι) -- ⊔⇑

infixr 3 _⊙_

pattern 1+[_] n = su (ℕ∞.ι n)
pattern 2+[_] n = 1+[ su (ℕ∞.ι n) ]

_⊙_ : Display
_⊙_ = record {}
