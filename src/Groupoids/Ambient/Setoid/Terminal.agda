{-# OPTIONS --without-K #-}

module Groupoids.Ambient.Setoid.Terminal where

open import Agda.Primitive
import Groupoids.Ambient.Setoid.Base as S
import Groupoids.Type as T

s : ∀ {d} ..{ℓᵒ ℓʰ} → S.t d ℓᵒ ℓʰ
S.obj s = T.𝟙.t
S.homᵗ s = T.Map.elm T.𝟙.t
S.idnᵗ s = _
S.cmpᵗ s = _
S.invᵗ (s {S.Dir.≤}) = _
S.invᵗ (s {S.Dir.≈}) = _

s⁰ : ∀ {d} → S.t d lzero lzero
s⁰ = s
