{-# OPTIONS --without-K #-}

module Groupoids.Ordinary.Universe where

open import Groupoids.Common

module 𝔘 where
  open import Groupoids.Ordinary.Construction.Core
  open import Groupoids.Ordinary.Construction.Opposite
  open import Groupoids.Ordinary.Homomorphism
  open import Groupoids.Ordinary.Isomorphism
  open import Groupoids.Ordinary.Monoidal.Exponential
  open import Groupoids.Ordinary.Monoidal.Tensor.Product
  open import Groupoids.Ordinary.Universe.Boot public

  open ≅

  Gpd = 𝔘 0
  Cat = 𝔘 1

  «seq₀*»
    : ∀ {r}..{ℓ}
    → {A B C : 𝔘 r ℓ}
    → {F₀ F₁ : Fun₀ A B}
    → {G₀ G₁ : Fun₀ B C}
    → A ⇒₀ B ⊢ F₀ ≅ F₁
    → B ⇒₀ C ⊢ G₀ ≅ G₁
    → A ⇒₀ C ⊢ ⇒₀.seq F₀ G₀ ≅ ⇒₀.seq F₁ G₁
  ap₁₀ (» («seq₀*» {C = C}{F₁ = F₁}{G₀ = G₀} α β)) a =
    seq₀ C (ap₀₁ G₀ (ap₁₀ (» α) a)) (ap₁₀ (» β) (ap₀₀ F₁ a))
  ap₁₁ (» («seq₀*» {C = C}{F₁ = F₁}{G₀ = G₀} α β)) f =
    (seq₁ C
      (⊢seq₀-α C)
      (seq₁ C
        (seq₀*-λ C
          (seq₁ C
            (inv₁ C (⇒₀.⊢seq G₀))
            (seq₁ C
              (ap₀₂ G₀ (ap₁₁ (» α) f))
              (⇒₀.⊢seq G₀))))
        (seq₁ C
          (inv₁ C (⊢seq₀-α C))
          (seq₁ C
            (seq₀*-ρ C
              (ap₁₁ »[ β ] (ap₀₁ F₁ f)))
            (⊢seq₀-α C)))))
  ap₁₀ (« («seq₀*» {C = C}{F₀ = F₀}{G₁ = G₁} α β)) a =
    seq₀ C (ap₀₁ G₁ (ap₁₀ «[ α ] a)) (ap₁₀ «[ β ] (ap₀₀ F₀ a))
  ap₁₁ (« («seq₀*» {C = C}{F₀ = F₀}{G₁ = G₁} α β)) f =
    (seq₁ C
      (⊢seq₀-α C)
      (seq₁ C
        (seq₀*-λ C
          (seq₁ C
            (inv₁ C (⇒₀.⊢seq G₁))
            (seq₁ C
              (ap₀₂ G₁ (ap₁₁ «[ α ] f))
              (⇒₀.⊢seq G₁))))
        (seq₁ C
          (inv₁ C (⊢seq₀-α C))
          (seq₁ C
            (seq₀*-ρ C
              (ap₁₁ «[ β ] (ap₀₁ F₀ f)))
            (⊢seq₀-α C)))))
  ⊢»« («seq₀*» {C = C}{F₀ = F₀}{G₁ = G₁} α β) = ι λ a →
    seq₁ C
      (seq₀*-λ C
        (ap₁₁ »[ β ] (ap₁₀ »[ α ] a)))
      (seq₁ C
        (inv₁ C (⊢seq₀-α C))
        (seq₁ C
          (seq₀*-ρ C
            (seq₁ C
              (⊢seq₀-α C)
              (seq₁ C
                (seq₀*-λ C
                  (seq₁ C
                    (inv₁ C (⇒₀.⊢seq G₁))
                    (seq₁ C
                      (ap₀₂ G₁ (T.⊔⇑.π (⊢»« α) a))
                      (⇒₀.⊢idn G₁))))
                (⊢idn₀-λ C))))
          (T.⊔⇑.π (⊢»« β) (ap₀₀ F₀ a))))
  ⊢«» («seq₀*» {C = C}{F₁ = F₁}{G₀ = G₀} α β) = ι λ a →
    seq₁ C
      (seq₀*-λ C
        (ap₁₁ «[ β ] (ap₁₀ «[ α ] a)))
      (seq₁ C
        (inv₁ C (⊢seq₀-α C))
        (seq₁ C
          (seq₀*-ρ C
            (seq₁ C
              (⊢seq₀-α C)
              (seq₁ C
                (seq₀*-λ C
                  (seq₁ C
                    (inv₁ C (⇒₀.⊢seq G₀))
                    (seq₁ C
                      (ap₀₂ G₀ (T.⊔⇑.π (⊢«» α) a))
                      (⇒₀.⊢idn G₀))))
                (⊢idn₀-λ C))))
          (T.⊔⇑.π (⊢«» β) (ap₀₀ F₁ a))))

  «⊢idn₀-λ»
    : ∀ {r}..{ℓ}
    → {A B : 𝔘 r ℓ}
    → {F : Fun₀ A B}
    → A ⇒₀ B ⊢ ⇒₀.seq ⇒₀.idn F ≅ F
  ap₁₀ (» («⊢idn₀-λ» {B = B})) a =
    idn₀ B
  ap₁₁ (» («⊢idn₀-λ» {B = B})) f =
    (seq₁ B
      (⊢idn₀-ρ B)
      (inv₁ B (⊢idn₀-λ B)))
  ap₁₀ (« («⊢idn₀-λ» {B = B})) a =
    idn₀ B
  ap₁₁ (« («⊢idn₀-λ» {B = B})) f =
    (seq₁ B
      (⊢idn₀-ρ B)
      (inv₁ B (⊢idn₀-λ B)))
  ⊢»« («⊢idn₀-λ» {B = B}) = ι λ a →
    ⊢idn₀-λ B
  ⊢«» («⊢idn₀-λ» {B = B}) = ι λ a →
    ⊢idn₀-λ B

  «⊢idn₀-ρ»
    : ∀ {r}..{ℓ}
    → {A B : 𝔘 r ℓ}
    → {F : Fun₀ A B}
    → A ⇒₀ B ⊢ ⇒₀.seq F ⇒₀.idn ≅ F
  ap₁₀ (» («⊢idn₀-ρ» {B = B})) a =
    idn₀ B
  ap₁₁ (» («⊢idn₀-ρ» {B = B})) f =
    (seq₁ B
      (⊢idn₀-ρ B)
      (inv₁ B (⊢idn₀-λ B)))
  ap₁₀ (« («⊢idn₀-ρ» {B = B})) a =
    idn₀ B
  ap₁₁ (« («⊢idn₀-ρ» {B = B})) f =
    (seq₁ B
      (⊢idn₀-ρ B)
      (inv₁ B (⊢idn₀-λ B)))
  ⊢»« («⊢idn₀-ρ» {B = B}) = ι λ a →
    ⊢idn₀-λ B
  ⊢«» («⊢idn₀-ρ» {B = B}) = ι λ a →
    ⊢idn₀-λ B

  «⊢seq₀-α»
    : ∀ {r}..{ℓ}
    → {A B C D : 𝔘 r ℓ}
    → {F : Fun₀ A B}
    → {G : Fun₀ B C}
    → {H : Fun₀ C D}
    → A ⇒₀ D ⊢ ⇒₀.seq F (⇒₀.seq G H) ≅ ⇒₀.seq (⇒₀.seq F G) H
  ap₁₀ (» («⊢seq₀-α» {D = D})) a =
    idn₀ D
  ap₁₁ (» («⊢seq₀-α» {D = D})) {a}{b} f =
    seq₁ D
      (⊢idn₀-ρ D)
      (inv₁ D (⊢idn₀-λ D))
  ap₁₀ (« («⊢seq₀-α» {D = D})) a =
    idn₀ D
  ap₁₁ (« («⊢seq₀-α» {D = D})) {a}{b} f =
    seq₁ D
      (⊢idn₀-ρ D)
      (inv₁ D (⊢idn₀-λ D))
  ⊢»« («⊢seq₀-α» {D = D}) = ι λ a →
    ⊢idn₀-λ D
  ⊢«» («⊢seq₀-α» {D = D}) = ι λ a →
    ⊢idn₀-λ D

  -- «Cat» is naturally a 𝔘 2 1 (lsuc ℓ) (large 2-category) structure but
  -- actually using it as such is problematic with the current definitions in
  -- this library. The main issue is that we do not allow functors between 𝔘
  -- structures with different (n, r) dimensions and most of the other
  -- constructions live at n ≤ 1. We _could_ allow cross-dimension functors but
  -- doing so would introduce a lot of complexity for a bit of rarely needed
  -- flexibility. The other reason to lower the dimension is because there are
  -- currently no coherence constraint cells defined for n ≥ 2. Thus, we
  -- downshift the n-dimension by 1 so we end up with 𝔘 1 1 (large 1-category).

  «Cat»
    : ∀ r ..ℓ
    → Cat (lsuc ℓ)
  ● [ «Cat» r ℓ ] = 𝔘 r ℓ
  ⇇ [ «Cat» r ℓ ] A B = 𝔊.dim*[ [ A ⇔₀ B ] ]
  ↻ [ «Cat» r ℓ ] = ⇒₀.idn
  seq₀ («Cat» r ℓ) = ⇒₀.seq
  inv₀ («Cat» r ℓ) F {≜ = ()}
  seq₀* («Cat» r ℓ) = «seq₀*»
  inv₀* («Cat» r ℓ) α {≜ = ()}
  ⊢idn₀-λ («Cat» r ℓ) = «⊢idn₀-λ»
  ⊢idn₀-ρ («Cat» r ℓ) = «⊢idn₀-ρ»
  ⊢seq₀-α («Cat» r ℓ) = «⊢seq₀-α»
  ⊢inv₀-λ («Cat» r ℓ) {≜ = ()}
  ⊢inv₀-ρ («Cat» r ℓ) {≜ = ()}
  idn₁ («Cat» r ℓ) {A}{B} = ≅.idn (A ⇒₀ B)
  seq₁ («Cat» r ℓ) {A}{B} = ≅.seq (A ⇒₀ B)
  inv₁ («Cat» r ℓ) {A}{B} = ≅.inv (A ⇒₀ B)

  «Gpd»
    : ∀ r ..ℓ
    → Gpd (lsuc ℓ)
  «Gpd» r ℓ = [ «Cat» r ℓ ]/≅

  «Std»
    : ∀ r ..ℓ
    → Std (lsuc ℓ)
  ● [ «Std» r ℓ ] = ● [ «Gpd» r ℓ ]
  ● (⇇ [ «Std» r ℓ ] a b) = ● (⇇ [ «Gpd» r ℓ ] a b)
  ⇇ (⇇ [ «Std» r ℓ ] _ _) _ _ = 𝔊.𝟙↑
  ↻ (⇇ [ «Std» r ℓ ] _ _) = _
  ↻ [ «Std» r ℓ ] = idn₀ («Gpd» r ℓ)
  seq₀ («Std» r ℓ) = seq₀ («Gpd» r ℓ)
  inv₀ («Std» r ℓ) = inv₀ («Gpd» r ℓ)
  seq₀* («Std» r ℓ) = _
  inv₀* («Std» r ℓ) = _
  ⊢idn₀-λ («Std» r ℓ) = _
  ⊢idn₀-ρ («Std» r ℓ) = _
  ⊢seq₀-α («Std» r ℓ) = _
  ⊢inv₀-λ («Std» r ℓ) = _
  ⊢inv₀-ρ («Std» r ℓ) = _
  idn₁ («Std» r ℓ) = _
  seq₁ («Std» r ℓ) = _
  inv₁ («Std» r ℓ) = _

open 𝔘 public
