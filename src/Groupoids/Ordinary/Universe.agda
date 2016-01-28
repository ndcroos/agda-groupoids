{-# OPTIONS --without-K #-}

module Groupoids.Ordinary.Universe where

open import Groupoids.Common

module 𝔘 where
  open import Groupoids.Ordinary.Construction.Core
  open import Groupoids.Ordinary.Homomorphism
  open import Groupoids.Ordinary.Isomorphism
  open import Groupoids.Ordinary.Monoidal.Exponential
  open import Groupoids.Ordinary.Universe.Boot public

  open ≅

  Std = 𝔘 0 0
  Gpd = 𝔘 1 0
  Cat = 𝔘 1 1

  «seq₀*»
    : ∀ {r}..{ℓ}
    → {A B C : 𝔘 1 r ℓ}
    → {F₀ F₁ : Fun₀ A B}
    → {G₀ G₁ : Fun₀ B C}
    → A ⇒₀ B ⊢ F₀ ≅ F₁
    → B ⇒₀ C ⊢ G₀ ≅ G₁
    → A ⇒₀ C ⊢ ⇒₀.seq F₀ G₀ ≅ ⇒₀.seq F₁ G₁
  ap₁₀ (» («seq₀*» {C = C}{F₁ = F₁}{G₀ = G₀} α β)) a =
    seq₀ C (ap₀₁ G₀ (ap₁₀ (» α) a)) (ap₁₀ (» β) (ap₀₀ F₁ a))
  ap₁₁ (» («seq₀*» {C = C}{F₁ = F₁}{G₀ = G₀} α β)) f =
    (seq₁ C
      (⊢α₀ C)
      (seq₁ C
        (seq₀*λ C
          (seq₁ C
            (inv₁ C (⇒₀.⊢seq G₀))
            (seq₁ C
              (ap₀₂ G₀ (ap₁₁ (» α) f))
              (⇒₀.⊢seq G₀))))
        (seq₁ C
          (inv₁ C (⊢α₀ C))
          (seq₁ C
            (seq₀*ρ C
              (ap₁₁ »[ β ] (ap₀₁ F₁ f)))
            (⊢α₀ C)))))
  ap₁₀ (« («seq₀*» {C = C}{F₀ = F₀}{G₁ = G₁} α β)) a =
    seq₀ C (ap₀₁ G₁ (ap₁₀ «[ α ] a)) (ap₁₀ «[ β ] (ap₀₀ F₀ a))
  ap₁₁ (« («seq₀*» {C = C}{F₀ = F₀}{G₁ = G₁} α β)) f =
    (seq₁ C
      (⊢α₀ C)
      (seq₁ C
        (seq₀*λ C
          (seq₁ C
            (inv₁ C (⇒₀.⊢seq G₁))
            (seq₁ C
              (ap₀₂ G₁ (ap₁₁ «[ α ] f))
              (⇒₀.⊢seq G₁))))
        (seq₁ C
          (inv₁ C (⊢α₀ C))
          (seq₁ C
            (seq₀*ρ C
              (ap₁₁ «[ β ] (ap₀₁ F₀ f)))
            (⊢α₀ C)))))
  ⊢»« («seq₀*» {C = C}{F₀ = F₀}{G₁ = G₁} α β) = ι λ a →
    seq₁ C
      (seq₀*λ C
        (ap₁₁ »[ β ] (ap₁₀ »[ α ] a)))
      (seq₁ C
        (inv₁ C (⊢α₀ C))
        (seq₁ C
          (seq₀*ρ C
            (seq₁ C
              (⊢α₀ C)
              (seq₁ C
                (seq₀*λ C
                  (seq₁ C
                    (inv₁ C (⇒₀.⊢seq G₁))
                    (seq₁ C
                      (ap₀₂ G₁ (T.⊔⇑.π (⊢»« α) a))
                      (⇒₀.⊢idn G₁))))
                (⊢λ₀ C))))
          (T.⊔⇑.π (⊢»« β) (ap₀₀ F₀ a))))
  ⊢«» («seq₀*» {C = C}{F₁ = F₁}{G₀ = G₀} α β) = ι λ a →
    seq₁ C
      (seq₀*λ C
        (ap₁₁ «[ β ] (ap₁₀ «[ α ] a)))
      (seq₁ C
        (inv₁ C (⊢α₀ C))
        (seq₁ C
          (seq₀*ρ C
            (seq₁ C
              (⊢α₀ C)
              (seq₁ C
                (seq₀*λ C
                  (seq₁ C
                    (inv₁ C (⇒₀.⊢seq G₀))
                    (seq₁ C
                      (ap₀₂ G₀ (T.⊔⇑.π (⊢«» α) a))
                      (⇒₀.⊢idn G₀))))
                (⊢λ₀ C))))
          (T.⊔⇑.π (⊢«» β) (ap₀₀ F₁ a))))

  «⊢λ₀»
    : ∀ {r}..{ℓ}
    → {A B : 𝔘 1 r ℓ}
    → {F : Fun₀ A B}
    → A ⇒₀ B ⊢ ⇒₀.seq ⇒₀.idn F ≅ F
  ap₁₀ (» («⊢λ₀» {B = B})) a =
    idn₀ B
  ap₁₁ (» («⊢λ₀» {B = B})) f =
    (seq₁ B
      (⊢ρ₀ B)
      (inv₁ B (⊢λ₀ B)))
  ap₁₀ (« («⊢λ₀» {B = B})) a =
    idn₀ B
  ap₁₁ (« («⊢λ₀» {B = B})) f =
    (seq₁ B
      (⊢ρ₀ B)
      (inv₁ B (⊢λ₀ B)))
  ⊢»« («⊢λ₀» {B = B}) = ι λ a →
    ⊢λ₀ B
  ⊢«» («⊢λ₀» {B = B}) = ι λ a →
    ⊢λ₀ B

  «⊢ρ₀»
    : ∀ {r}..{ℓ}
    → {A B : 𝔘 1 r ℓ}
    → {F : Fun₀ A B}
    → A ⇒₀ B ⊢ ⇒₀.seq F ⇒₀.idn ≅ F
  ap₁₀ (» («⊢ρ₀» {B = B})) a =
    idn₀ B
  ap₁₁ (» («⊢ρ₀» {B = B})) f =
    (seq₁ B
      (⊢ρ₀ B)
      (inv₁ B (⊢λ₀ B)))
  ap₁₀ (« («⊢ρ₀» {B = B})) a =
    idn₀ B
  ap₁₁ (« («⊢ρ₀» {B = B})) f =
    (seq₁ B
      (⊢ρ₀ B)
      (inv₁ B (⊢λ₀ B)))
  ⊢»« («⊢ρ₀» {B = B}) = ι λ a →
    ⊢λ₀ B
  ⊢«» («⊢ρ₀» {B = B}) = ι λ a →
    ⊢λ₀ B

  «⊢α₀»
    : ∀ {r}..{ℓ}
    → {A B C D : 𝔘 1 r ℓ}
    → {F : Fun₀ A B}
    → {G : Fun₀ B C}
    → {H : Fun₀ C D}
    → A ⇒₀ D ⊢ ⇒₀.seq F (⇒₀.seq G H) ≅ ⇒₀.seq (⇒₀.seq F G) H
  ap₁₀ (» («⊢α₀» {D = D})) a =
    idn₀ D
  ap₁₁ (» («⊢α₀» {D = D})) {a}{b} f =
    seq₁ D
      (⊢ρ₀ D)
      (inv₁ D (⊢λ₀ D))
  ap₁₀ (« («⊢α₀» {D = D})) a =
    idn₀ D
  ap₁₁ (« («⊢α₀» {D = D})) {a}{b} f =
    seq₁ D
      (⊢ρ₀ D)
      (inv₁ D (⊢λ₀ D))
  ⊢»« («⊢α₀» {D = D}) = ι λ a →
    ⊢λ₀ D
  ⊢«» («⊢α₀» {D = D}) = ι λ a →
    ⊢λ₀ D

  «Cat»
    : ∀ r ..ℓ
    → 𝔘 2 1 _
  ● [ «Cat» r ℓ ] = 𝔘 1 r ℓ
  ⇇ [ «Cat» r ℓ ] A B = [ A ⇔₀ B ]
  ↻ [ «Cat» r ℓ ] = ⇒₀.idn
  seq₀ («Cat» r ℓ) = ⇒₀.seq
  inv₀ («Cat» r ℓ) F {≜ = ()}
  seq₀* («Cat» r ℓ) = «seq₀*»
  inv₀* («Cat» r ℓ) α {≜ = ()}
  ⊢λ₀ («Cat» r ℓ) = «⊢λ₀»
  ⊢ρ₀ («Cat» r ℓ) = «⊢ρ₀»
  ⊢α₀ («Cat» r ℓ) = «⊢α₀»
  ⊢λ₀⁻¹ («Cat» r ℓ) {≜ = ()}
  ⊢ρ₀⁻¹ («Cat» r ℓ) {≜ = ()}
  idn₁ («Cat» r ℓ) {A}{B} = ≅.idn (A ⇒₀ B)
  seq₁ («Cat» r ℓ) {A}{B} = ≅.seq (A ⇒₀ B)
  inv₁ («Cat» r ℓ) {A}{B} = ≅.inv (A ⇒₀ B)

  «Gpd»
    : ∀ r ..ℓ
    → 𝔘 2 0 _
  «Gpd» r ℓ = [ «Cat» r ℓ ]/≅

open 𝔘 public
