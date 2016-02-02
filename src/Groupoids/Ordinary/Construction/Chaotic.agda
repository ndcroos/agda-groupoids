{-# OPTIONS --without-K #-}

module Groupoids.Ordinary.Construction.Chaotic where

open import Groupoids.Common
open import Groupoids.Ordinary.Homomorphism.Boot
open import Groupoids.Ordinary.Universe.Boot

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
