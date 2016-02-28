{-# OPTIONS --without-K #-}

module Groupoids.Ordinary.Groupoid.Yoneda where

open import Groupoids.Basis
open import Groupoids.Ordinary.Groupoid.Opposite
open import Groupoids.Ordinary.Ambient.Morphism.Hom.Boot
open import Groupoids.Ordinary.Ambient.Cosmos.Exponential
open import Groupoids.Ordinary.Ambient.Universe

-- module Yoneda where
--   𝓎[_]
--     : ∀ ..{ℓ}
--     → (A : 𝔘 1 ℓ)
--     → Hom₀ A (Op[ A ] ⇒₀ «Std» 0 ℓ)
--   ap₀₀ (ap₀₀ 𝓎[ A ] b) a = hom A a b
--   ap₀₁ (ap₀₀ 𝓎[ A ] b) f = hom* A f (idn₀ A)
--   ap₀₂ (ap₀₀ 𝓎[ A ] b) α = _
--   ⇒₀.⊢idn (ap₀₀ 𝓎[ A ] b) = _
--   ⇒₀.⊢seq (ap₀₀ 𝓎[ A ] b) = _
--   ⇒₀.⊢inv (ap₀₀ 𝓎[ A ] b) = _
--   ap₁₀ (ap₀₁ 𝓎[ A ] g) a = hom* A (idn₀ A) g
--   ap₁₁ (ap₀₁ 𝓎[ A ] g) f = _
--   ap₀₂ 𝓎[ A ] α = ι _
--   ⇒₀.⊢idn 𝓎[ A ] = ι _
--   ⇒₀.⊢seq 𝓎[ A ] = ι _
--   ⇒₀.⊢inv 𝓎[ A ] = ι _

-- module Coyoneda where
--   -- Note that Yoneda.𝓎[ Op A ] isn't quite what we need because Op (Op A) is
--   -- not definitionally equal to A in this setting, only isomorphic.

--   𝓎[_]
--     : ∀ ..{ℓ}
--     → (A : 𝔘 1 ℓ)
--     → Hom₀ Op[ A ] (A ⇒₀ «Std» 0 ℓ)
--   ap₀₀ (ap₀₀ 𝓎[ A ] a) b = hom A a b
--   ap₀₁ (ap₀₀ 𝓎[ A ] a) g = hom* A (idn₀ A) g
--   ap₀₂ (ap₀₀ 𝓎[ A ] a) β = _
--   ⇒₀.⊢idn (ap₀₀ 𝓎[ A ] a) = _
--   ⇒₀.⊢seq (ap₀₀ 𝓎[ A ] a) = _
--   ⇒₀.⊢inv (ap₀₀ 𝓎[ A ] a) = _
--   ap₁₀ (ap₀₁ 𝓎[ A ] f) b = hom* A f (idn₀ A)
--   ap₁₁ (ap₀₁ 𝓎[ A ] f) g = _
--   ap₀₂ 𝓎[ A ] α = ι _
--   ⇒₀.⊢idn 𝓎[ A ] = ι _
--   ⇒₀.⊢seq 𝓎[ A ] = ι _
--   ⇒₀.⊢inv 𝓎[ A ] = ι _
