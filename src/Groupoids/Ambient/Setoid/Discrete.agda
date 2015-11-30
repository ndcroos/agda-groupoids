{-# OPTIONS --without-K #-}

module Groupoids.Ambient.Setoid.Discrete where

open import Agda.Primitive
import Groupoids.Ambient.Setoid.Base as S
open import Groupoids.Type as T
  using (_,_)

s : ∀ {d} ..{ℓᵒ}
  → (A : T.t ℓᵒ)
  → S.t d _ _
S.obj (s A) =
  A
S.homᵗ (s A) =
  λ {(a , b) → a T.≡.t b}
S.idnᵗ (s A) =
  T.≡.idn
S.cmpᵗ (s A) =
  T.≡.cmp
S.invᵗ (s {S.Dir.≤} A) =
  _
S.invᵗ (s {S.Dir.≈} A) =
  T.≡.inv
