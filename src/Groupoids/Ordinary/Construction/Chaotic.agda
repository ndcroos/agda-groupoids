{-# OPTIONS --without-K #-}

module Groupoids.Ordinary.Construction.Chaotic where

open import Groupoids.Common
open import Groupoids.Ordinary.Homomorphism.Boot
open import Groupoids.Ordinary.Universe.Boot

module ∻ where
  Free
    : ∀ {n r}..{ℓ}
    → (A : Set ℓ)
    → 𝔘 n r ℓ
  Free A = record { [_] = 𝔊.dim*[ 𝔊.∻.Free A ] }

  Forget
    : ∀ {n r}..{ℓ}
    → (A : 𝔘 n r ℓ)
    → Set ℓ
  Forget A = ● [ A ]
