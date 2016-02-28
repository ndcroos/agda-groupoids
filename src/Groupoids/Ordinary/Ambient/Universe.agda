{-# OPTIONS --without-K #-}

module Groupoids.Ordinary.Ambient.Universe where

open import Groupoids.Basis

module 𝔘 where
  open import Groupoids.Ordinary.Groupoid.Core
  open import Groupoids.Ordinary.Groupoid.Opposite
  open import Groupoids.Ordinary.Ambient.Morphism.Hom
  open import Groupoids.Ordinary.Ambient.Morphism.Iso
  open import Groupoids.Ordinary.Ambient.Cosmos.Exponential
  open import Groupoids.Ordinary.Ambient.Cosmos.Tensor.Product
  open import Groupoids.Ordinary.Ambient.Universe.Boot public

  open ≅

  Gpd = 𝔘 1 0
  Cat = 𝔘 1 1

  seq₀*→
    : ∀ {n r}..{ℓ₀ ℓ₁ ℓ₂}
    → {A : 𝔘 n r ℓ₀}
    → {B : 𝔘 n r ℓ₁}
    → {C : 𝔘 n r ℓ₂}
    → {F₀ F₁ : Hom₀ A B}
    → {G₀ G₁ : Hom₀ B C}
    → (α : Hom₁ F₀ F₁)
    → (β : Hom₁ G₀ G₁)
    → Hom₁ (F₀ ⟓₀ G₀) (F₁ ⟓₀ G₁)
  ap₁₀ (seq₀*→ {C = C}{F₁ = F₁}{G₀ = G₀} α β) a =
    (seq₀ C
      (ap₀₁ G₀ (ap₁₀ α a))
      (ap₁₀ β (ap₀₀ F₁ a)))
  ap₁₁ (seq₀*→ {C = C}{F₁ = F₁}{G₀ = G₀} α β) f =
    (seq₁ C
      (⊢seq₀-α C)
      (seq₁ C
        (seq₀*-λ C
          (seq₁ C
            (inv₁ C (⇒₀.⊢seq G₀))
            (seq₁ C
              (ap₀₂ G₀ (ap₁₁ α f))
              (⇒₀.⊢seq G₀))))
        (seq₁ C
          (inv₁ C (⊢seq₀-α C))
          (seq₁ C
            (seq₀*-ρ C (ap₁₁ β (ap₀₁ F₁ f)))
            (⊢seq₀-α C)))))

  «seq₀*»
    : ∀ {n r}..{ℓ₀ ℓ₁ ℓ₂}
    → {A : 𝔘 n r ℓ₀}
    → {B : 𝔘 n r ℓ₁}
    → {C : 𝔘 n r ℓ₂}
    → {F₀ F₁ : Hom₀ A B}
    → {G₀ G₁ : Hom₀ B C}
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
    : ∀ {n r}..{ℓ₀ ℓ₁}
    → {A : 𝔘 n r ℓ₀}
    → {B : 𝔘 n r ℓ₁}
    → {F : Hom₀ A B}
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
    : ∀ {n r}..{ℓ₀ ℓ₁}
    → {A : 𝔘 n r ℓ₀}
    → {B : 𝔘 n r ℓ₁}
    → {F : Hom₀ A B}
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
    : ∀ {n r}..{ℓ₀ ℓ₁ ℓ₂ ℓ₃}
    → {A : 𝔘 n r ℓ₀}
    → {B : 𝔘 n r ℓ₁}
    → {C : 𝔘 n r ℓ₂}
    → {D : 𝔘 n r ℓ₃}
    → {F : Hom₀ A B}
    → {G : Hom₀ B C}
    → {H : Hom₀ C D}
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

  -- Note that «Cat» is the category of categories/groupoids depending on
  -- whether r > 0 (category) or r ≡ 0 (groupoid).

  «Cat»
    : ∀ r ..ℓ
    → Cat (lsuc ℓ)
  ● [ «Cat» r ℓ ] = 𝔘 1 r ℓ
  ⇇ [ «Cat» r ℓ ] A B = 𝔊.dim*[ [ A ⇔₀ B ] ]
  idn₀ («Cat» r ℓ) = ⇒₀.idn
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

  -- «Gpd» is the groupoid of categories/groupoids in the same way as «Cat».

  «Gpd»
    : ∀ r ..ℓ
    → Gpd (lsuc ℓ)
  «Gpd» r ℓ = [ «Cat» r ℓ ]/≅

  -- «Std» is the category of setoids.

  -- «Std»
  --   : ∀ r ..ℓ
  --   → Cat (lsuc ℓ)
  -- ● [ «Std» r ℓ ] = ● [ «Cat» r ℓ ]
  -- ● (⇇ [ «Std» r ℓ ] a b) = ● (⇇ [ «Cat» r ℓ ] a b)
  -- ⇇ (⇇ [ «Std» r ℓ ] _ _) _ _ = 𝔊.𝟙↑
  -- idn₀ («Std» r ℓ) = idn₀ («Cat» r ℓ)
  -- seq₀ («Std» r ℓ) = seq₀ («Cat» r ℓ)
  -- inv₀ («Std» r ℓ) f {()}
  -- seq₀* («Std» r ℓ) = _
  -- inv₀* («Std» r ℓ) = _
  -- ⊢idn₀-λ («Std» r ℓ) = _
  -- ⊢idn₀-ρ («Std» r ℓ) = _
  -- ⊢seq₀-α («Std» r ℓ) = _
  -- ⊢inv₀-λ («Std» r ℓ) = _
  -- ⊢inv₀-ρ («Std» r ℓ) = _
  -- idn₁ («Std» r ℓ) = _
  -- seq₁ («Std» r ℓ) = _
  -- inv₁ («Std» r ℓ) = _

  hom
   : ∀ {n r}..{ℓ}
   → (A : 𝔘 (su n) r ℓ)
   → (a b : A ▸)
   → 𝔘 n 0 ℓ
  ● [ hom A x y ] = A ▸ 1 ⊢ x ↝ y
  ● (⇇ [ hom A x y ] f g) = A ▸ 2 ⊢ f ↝ g
  ⇇ (⇇ [ hom A x y ] _ _) _ _ = 𝔊.𝟙↑
  idn₀ (hom A x y) = idn₁ A
  seq₀ (hom A x y) = seq₁ A
  inv₀ (hom A x y) f = inv₁ A f
  seq₀* (hom A x y) = _
  inv₀* (hom A x y) = _
  ⊢idn₀-λ (hom A x y) = _
  ⊢idn₀-ρ (hom A x y) = _
  ⊢seq₀-α (hom A x y) = _
  ⊢inv₀-λ (hom A x y) = _
  ⊢inv₀-ρ (hom A x y) = _
  idn₁ (hom A x y) = _
  seq₁ (hom A x y) = _
  inv₁ (hom A x y) = _

  hom*
    : ∀ {n}..{ℓ}
    → (A : 𝔘 (su n) 1 ℓ)
    → {a₀ a₁ b₀ b₁ : A ▸}
    → (f : Op[ A ] ▸ 1 ⊢ a₀ ↝ a₁)
    → (g : A ▸ 1 ⊢ b₀ ↝ b₁)
    → Hom₀ (hom A a₀ b₀) (hom A a₁ b₁)
  ap₀₀ (hom* A f g) k = seq₀ A f (seq₀ A k g)
  ap₀₁ (hom* A f g) α = seq₀*-ρ A (seq₀*-λ A α)
  ap₀₂ (hom* A f g) = _
  ⇒₀.⊢idn (hom* A f g) = _
  ⇒₀.⊢seq (hom* A f g) = _
  ⇒₀.⊢inv (hom* A f g) = _

  -- «hom»
  --   : ∀ ..{ℓ}
  --   → (A : 𝔘 {!!} 1 ℓ)
  --   → Hom₀ (Op[ A ] ⊗ A) («Std» 0 ℓ)
  -- ap₀₀ («hom» A) (a , b) = hom  A a b
  -- ap₀₁ («hom» A) (f , g) = hom* A f g
  -- ap₀₂ («hom» A) = _
  -- ⇒₀.⊢idn («hom» A) = _
  -- ⇒₀.⊢seq («hom» A) = _
  -- ⇒₀.⊢inv («hom» A) = _

  -- Psh
  --   : ∀ ..{ℓ}
  --   → (A : 𝔘 1 ℓ)
  --   → Set _
  -- Psh {ℓ} A = Hom₀ Op[ A ] («Std» 0 ℓ)

  -- «Psh»
  --   : ∀ ..{ℓ}
  --   → (A : 𝔘 1 ℓ)
  --   → 𝔘 _ _
  -- «Psh» {ℓ} A = Op[ A ] ⇒₀ «Std» 0 ℓ

  -- «Op»
  --   : ∀ {r}..{ℓ}
  --   → Hom₀ («Cat» r ℓ) («Cat» r ℓ)
  -- ap₀₀ «Op» =
  --   Op[_]
  -- ap₀₁ «Op» = ap₀₀
  --   ⇒.⊢.op⇒
  -- Hom₁.ap₁₀ (Iso.» (ap₀₂ «Op» α)) =
  --   ap₁₀ (Iso.« α)
  -- Hom₁.ap₁₁ (Iso.» (ap₀₂ «Op» {b = B} α)) f =
  --   inv₁ B (ap₁₁ (Iso.« α) f)
  -- Hom₁.ap₁₀ (Iso.« (ap₀₂ «Op» α)) a =
  --   ap₁₀ (Iso.» α) a
  -- Hom₁.ap₁₁ (Iso.« (ap₀₂ «Op» {b = B} α)) f =
  --   inv₁ B (ap₁₁ (Iso.» α) f)
  -- Iso.⊢»« (ap₀₂ «Op» α) =
  --   Iso.⊢»« α
  -- Iso.⊢«» (ap₀₂ «Op» α) =
  --   Iso.⊢«» α
  -- Hom₁.ap₁₀ (Iso.» (⇒₀.⊢idn «Op» {A})) a =
  --   idn₀ A
  -- Hom₁.ap₁₁ (Iso.» (⇒₀.⊢idn «Op» {A})) f =
  --   seq₁ A (⊢idn₀-λ A) (inv₁ A (⊢idn₀-ρ A))
  -- Hom₁.ap₁₀ (Iso.« (⇒₀.⊢idn «Op» {A})) a =
  --   idn₀ A
  -- Hom₁.ap₁₁ (Iso.« (⇒₀.⊢idn «Op» {A})) f =
  --   seq₁ A (⊢idn₀-λ A) (inv₁ A (⊢idn₀-ρ A))
  -- Iso.⊢»« (⇒₀.⊢idn «Op» {A}) =
  --   ι λ a → ⊢idn₀-λ A {a}{a}{idn₀ A {a}}
  -- Iso.⊢«» (⇒₀.⊢idn «Op» {A}) =
  --   ι λ a → ⊢idn₀-λ A {a}{a}{idn₀ A {a}}
  -- Hom₁.ap₁₀ (Iso.» (⇒₀.⊢seq «Op» {c = C})) a =
  --   idn₀ C
  -- Hom₁.ap₁₁ (Iso.» (⇒₀.⊢seq «Op» {c = C})) f =
  --   seq₁ C (⊢idn₀-λ C) (inv₁ C (⊢idn₀-ρ C))
  -- Hom₁.ap₁₀ (Iso.« (⇒₀.⊢seq «Op» {c = C})) a =
  --   idn₀ C
  -- Hom₁.ap₁₁ (Iso.« (⇒₀.⊢seq «Op» {c = C})) f =
  --   seq₁ C (⊢idn₀-λ C) (inv₁ C (⊢idn₀-ρ C))
  -- Iso.⊢»« (⇒₀.⊢seq «Op» {c = C}{F}{G}) =
  --   ι λ a → ⊢idn₀-λ C {ap₀₀ G (ap₀₀ F a)}
  -- Iso.⊢«» (⇒₀.⊢seq «Op» {c = C}{F}{G}) =
  --   ι λ a → ⊢idn₀-λ C {ap₀₀ G (ap₀₀ F a)}
  -- ⇒₀.⊢inv «Op» {()}

open 𝔘 public
