{-# OPTIONS --without-K #-}

module Groupoids.Category.Iso where

open import Agda.Primitive
import Groupoids.Category as C
import Groupoids.Groupoid as G
import Groupoids.Setoid as S
open import Groupoids.Type as T
  using (_,_)
import Groupoids.Groupoid.Iso as GI

t : ∀ ..{ℓᵒ ℓˢᵒ ℓˢʰ}
  → {A : G.t G.Dir.≤ ℓᵒ ℓˢᵒ ℓˢʰ}
  → _
t {A = A} = GI.t A

s : ∀ ..{ℓᵒ ℓˢᵒ ℓˢʰ}
  → {A : G.t G.Dir.≤ ℓᵒ ℓˢᵒ ℓˢʰ}
  → _
s {A = A} = GI.s {A = A}

c : ∀ ..{ℓᵒ ℓˢᵒ ℓˢʰ}
  → (A : G.t G.Dir.≤ ℓᵒ ℓˢᵒ ℓˢʰ)
  → _
c A = GI.g G.Dir.≤ A
