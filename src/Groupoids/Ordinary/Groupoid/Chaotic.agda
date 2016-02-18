{-# OPTIONS --without-K #-}

module Groupoids.Ordinary.Groupoid.Chaotic where

open import Groupoids.Basis
open import Groupoids.Ordinary.Ambient.Morphism.Hom.Boot
open import Groupoids.Ordinary.Ambient.Universe.Boot

module ∻ where
  Free
    : ∀ {r}..{ℓ}
    → (A : Set ℓ)
    → 𝔘 r ℓ
  Free A = record { [_] = 𝔊.dim*[ 𝔊.∻.Free A ] }

  Forget
    : ∀ {r}..{ℓ}
    → (A : 𝔘 r ℓ)
    → Set ℓ
  Forget A = ● [ A ]
