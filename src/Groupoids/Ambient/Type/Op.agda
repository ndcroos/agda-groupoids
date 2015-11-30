{-# OPTIONS --without-K #-}

module Groupoids.Ambient.Type.Op where

import Groupoids.Ambient.Type.Base as T

t : ∀ ..{ℓᵒ} → T.t ℓᵒ → T.t ℓᵒ
t A = A
