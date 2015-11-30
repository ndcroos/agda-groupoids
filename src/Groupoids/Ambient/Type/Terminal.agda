{-# OPTIONS --without-K #-}

module Groupoids.Ambient.Type.Terminal where

open import Agda.Primitive

record t ..{ℓ} : Set ℓ where
  constructor *

t⁰ : Set₀
t⁰ = t {lzero}
