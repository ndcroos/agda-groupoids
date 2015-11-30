{-# OPTIONS --without-K #-}

module Groupoids.Ambient.Preorder.Base where

open import Agda.Primitive
open import Groupoids.Common

module S where
  open import Groupoids.Setoid public

module t where
  open S.t {Dir.≤} public
open t public

t : ∀ ..(ℓᵒ ℓʰ : _) → Set _
t = S.t Dir.≤
