{-# OPTIONS --without-K #-}

module Groupoids.Groupoid.Instances.SETOID where

open import Agda.Primitive
private
  module G where
    open import Groupoids.Groupoid public
    module ≅ where
      open import Groupoids.Groupoid.Iso public
import Groupoids.Setoid as S
open import Groupoids.Type as T
  using (_,_)

c : ..(ℓᵒ ℓʰ : _) → G.t S.Dir.≤ _ _ _
G.obj (c ℓᵒ ℓʰ) =
  S.t S.Dir.≈ ℓᵒ ℓʰ
G.homˢ (c _ _) =
  λ {(a , b) → a S.Map.⇒₀ˢ b}
G.idnˢ (c _ _) =
  S.Map.idn₀ˢ
G.cmpˢ (c _ _) =
  S.Map.cmp₀ˢ
S.Map.com₁ (G.idn-lhs (c _ _) {b = B} _) =
  S.idnᵗ B _
S.Map.com₁ (G.idn-rhs (c _ _) {b = B} _) =
  S.idnᵗ B _
S.Map.com₁ (G.cmp-ass (c _ _) {d = D} _ _ _) =
  S.idnᵗ D _
G.invˢ (c _ _) =
  _
G.inv-lhs (c _ _) =
  _
G.inv-rhs (c _ _) =
  _

g : ∀ d ..(ℓᵒ ℓʰ : _) → G.t d _ _ _
g d ℓᵒ ℓʰ = G.≅.g d (c ℓᵒ ℓʰ)
