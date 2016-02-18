{-# OPTIONS --without-K #-}

module Groupoids.Ordinary.Groupoid.Pushout where

-- open import PERs.Common
-- open import PERs.Ordinary.Groupoid.Coequalizer
-- open import PERs.Ordinary.Morphism..Boot
-- open import PERs.Ordinary.Monoidal.Tensor.Coproduct
-- open import PERs.Ordinary.Universe.Boot

-- module Pushout where
--   Push
--     : ∀ ..{ℓ₀ ℓ₁ ℓ₂}
--     → {A : 𝔘 ℓ₀}
--     → {B : 𝔘 ℓ₁}
--     → {X : 𝔘 ℓ₂}
--     → (F : Hom X A)
--     → (G : Hom X B)
--     → 𝔘 _
--   Push F G = CoEq (⊕.inl ⇒.⟔ F) (⊕.inr ⇒.⟔ G)

--   push
--     : ∀ ..{ℓ₀ ℓ₁ ℓ₂}
--     → {A : 𝔘 ℓ₀}
--     → {B : 𝔘 ℓ₁}
--     → {X : 𝔘 ℓ₂}
--     → (F : Hom X A)
--     → (G : Hom X B)
--     → Hom (A ⊕ B) (Push F G)
--   push F G = coEq (⊕.inl ⇒.⟔ F) (⊕.inr ⇒.⟔ G)

-- open Pushout public
--   using (Push)
--   using (push)
