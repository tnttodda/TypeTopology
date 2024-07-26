```agda
{-# OPTIONS --without-K --exact-split --safe #-}

open import UF.FunExt
open import MLTT.Spartan
open import Naturals.Addition renaming (_+_ to _+ℕ_)
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import Naturals.Order
open import Integers.Type
open import Integers.Order
open import UF.PropTrunc
open import TWA.Thesis.Chapter2.Sequences
open import TWA.Thesis.Chapter5.SignedDigit
open import TWA.Thesis.Chapter5.BelowAndAbove
open import TWA.Thesis.Chapter5.IntervalObject hiding (⟨_⟩)

module TWA.Thesis.FurtherWork.IntervalObjectOrder
 {𝓦 : Universe}
 (fe : FunExt)
 (io : Interval-object fe 𝓦)
 where

open import TWA.Thesis.Chapter6.SignedDigitOrder fe
 renaming (_≤𝟛ᴺ_ to _≤𝟛ᴺ'_)
open import TWA.Thesis.Chapter5.SignedDigitIntervalObject fe io
open import TWA.Thesis.Chapter5.IntervalObjectApproximation fe io
open basic-interval-object-development fe io

𝕀-induction : (P : 𝕀 → 𝓥 ̇ )
           → P u
           → P v
           → ((α : ℕ → 𝕀) → Π (P ∘ α) → P (M α))
           → Π P
𝕀-induction P Pu Pv P⊕ x = {!!}

𝕀-induction' : (P : 𝕀 → 𝓥 ̇ )
            → P u
            → P v
            → ((x y : 𝕀) → P x → P y → P (x ⊕ y))
            → Π P
𝕀-induction' P Pu Pv P⊕ x = {!!}

-- x <= y := Σ d : ℕ , x + d = y

-- |---------------------------|
--        x               y

record order  (pt : propositional-truncations-exist)
 : 𝓤₀ ⊔ 𝓦 ⁺  ̇ where
 field
  _≤_ : 𝕀 → 𝕀 → 𝓤₀ ̇
 infix 10 _≤_
 
 field
  ≤-is-prop : {x y : 𝕀} → is-prop (x ≤ y)
  u-minimal : {x : 𝕀} → u ≤ x
  v-maximal : {x : 𝕀} → x ≤ v
  ⊕-lower : {x y z w : 𝕀} → x ≤ z → y ≤ w → x ⊕ y ≤ z ⊕ w
  ≤-canc : {x y z : 𝕀} → x ⊕ y ≤ z ⊕ y → x ≤ z
  
 ⊕-lower-l : {x y z : 𝕀} → x ≤ z → y ≤ z → x ⊕ y ≤ z
 ⊕-lower-l {x} {y} {z} x≤z y≤z
  = transport (x ⊕ y ≤_) (⊕-idem z) (⊕-lower x≤z y≤z)
  
 ⊕-lower-r : {x y z : 𝕀} → x ≤ y → x ≤ z → x ≤ y ⊕ z
 ⊕-lower-r {x} {y} {z} x≤y x≤z
  = transport (_≤ y ⊕ z) (⊕-idem x) (⊕-lower x≤y x≤z)

 ≤𝕀-refl : {x : 𝕀} → x ≤ x
 ≤𝕀-refl {x}
  = 𝕀-induction (λ x → x ≤ x) u-minimal v-maximal (λ _ _ → ⊕-lower) x

 ≤𝕀-trans : {x y z : 𝕀} → x ≤ y → y ≤ z → x ≤ z
 ≤𝕀-trans {x} {y} {z} x≤y y≤z
  = ≤-canc (transport ((x ⊕ y) ≤_) (⊕-comm y z) (⊕-lower x≤y y≤z))

 ≤-after : (α β : ℕ → 𝕀) → ℕ → 𝓤₀  ̇
 ≤-after α β n = (i : ℕ)
               → n ≤ℕ i
               → m ((first- (succ i)) α) ≤ m ((first- (succ i)) β)

 open PropositionalTruncation pt
 
 field
  m-to-M-≤ : (α β : ℕ → 𝕀) → ∃ (≤-after α β) → M α ≤ M β
 m-to-M-≤' : (α β : ℕ → 𝕀)
           → ((n : ℕ)
             → m ((first- (succ n)) α) ≤ m ((first- (succ n)) β))
           → M α ≤ M β
 m-to-M-≤' α β f = m-to-M-≤ α β ∣ (0 , (λ n _ → f n)) ∣

 
 _≤𝟛ᴺ_ = _≤𝟛ᴺ'_ pt

 _≤₃_ : 𝟛 → 𝟛 → 𝓤₀ ̇
 a  ≤₃ +1 = 𝟙
 −1 ≤₃ −1 = 𝟙
 O  ≤₃ −1 = 𝟘
 +1 ≤₃ −1 = 𝟘
 −1 ≤₃  O = 𝟙
 O  ≤₃  O = 𝟙
 +1 ≤₃  O = 𝟘

 integer-approx-relates-base₁ : (a b : 𝟛)
                              → a ≤₃ b
                              → ⟨ a ⟩ ≤ ⟨ b ⟩
 integer-approx-relates-base₁  a +1 a≤b = v-maximal
 integer-approx-relates-base₁ −1 −1 a≤b = u-minimal
 integer-approx-relates-base₁ −1  O a≤b = u-minimal
 integer-approx-relates-base₁  O  O a≤b
  = ⊕-lower u-minimal v-maximal

 integer-approx-relates-base₂ : (α β : 𝟛ᴺ)
                              →  integer-approx α 1
                              ≤ℤ integer-approx β 1
                              → α 0 ≤₃ β 0
 integer-approx-relates-base₂ α β α₀≤β₀ with α 0 | β 0
 ... | −1 | −1 = ⋆
 ... | −1 |  O = ⋆
 ... | −1 | +1 = ⋆
 ... |  O | −1 = ℤ-less-not-bigger-or-equal _ _ (0 , refl) α₀≤β₀
 ... |  O |  O = ⋆
 ... |  O | +1 = ⋆
 ... | +1 | −1 = ℤ-less-not-bigger-or-equal _ _ (1 , refl) α₀≤β₀
 ... | +1 |  O = ℤ-less-not-bigger-or-equal _ _ (0 , refl) α₀≤β₀
 ... | +1 | +1 = ⋆

 m-split : (α : 𝟛ᴺ) (n : ℕ)
         → m ((first- (succ (succ n))) (map ⟨_⟩ α))
         ＝ ⟨ α 0 ⟩ ⊕ m ((first- (succ n)) (map ⟨_⟩ (α ∘ succ)))
 m-split α n = refl

{- downLeft-rev-monotone : (x y : ℤ) → downLeft x ≤ℤ downLeft y → x ≤ℤ y
 downLeft-rev-monotone x y (zero , γ) = 0 , {!!}
 downLeft-rev-monotone x y (succ n , γ) = {!!} -}
 
 integer-approx-IH : (a b : 𝟛) (x y : ℤ)
                   → 𝟛-to-down a x ≤ℤ 𝟛-to-down b y
                   → x ≤ℤ y
 integer-approx-IH −1 −1 x y ax≤by = {!!}
 integer-approx-IH −1  O x y ax≤by = {!!}
 integer-approx-IH −1 +1 x y ax≤by = {!!}
 integer-approx-IH  O −1 x y ax≤by = {!!}
 integer-approx-IH  O  O x y ax≤by = {!!}
 integer-approx-IH  O +1 x y ax≤by = {!!}
 integer-approx-IH +1 −1 x y ax≤by = {!!}
 integer-approx-IH +1  O x y ax≤by = {!!}
 integer-approx-IH +1 +1 x y ax≤by = {!!}

 integer-approx-relates : (α β : 𝟛ᴺ) (n : ℕ)
                        →  integer-approx α (succ n)
                        ≤ℤ integer-approx β (succ n)
                        → m ((first- (succ n)) (map ⟨_⟩ α))
                        ≤ m ((first- (succ n)) (map ⟨_⟩ β))
 integer-approx-relates α β 0
  = integer-approx-relates-base₁ (α 0) (β 0)
  ∘ integer-approx-relates-base₂ α β
 integer-approx-relates α β (succ n) α≤β
  = ⊕-lower {!!}
      (integer-approx-relates (tail α) (tail β) {!!}
        (integer-approx-IH (α 0) (β 0) _ _ {!α≤β!}))
  where
   γ₁ : {!!}
   γ₁ = {!!}
   γ₂ : integer-approx (λ x → α (succ x)) (succ n)
     ≤ℤ integer-approx (λ x → β (succ x)) (succ n)
   γ₂ = {!α≤β!}

 ≤-relates : (α β : 𝟛ᴺ) → α ≤𝟛ᴺ β → ⟪ α ⟫ ≤ ⟪ β ⟫
 ≤-relates α β
  = ∥∥-induction (λ _ → ≤-is-prop)
     (λ (n , f) → m-to-M-≤ (map ⟨_⟩ α) (map ⟨_⟩ β)
       ∣ n , (λ i n≤i → integer-approx-relates α β i
         (f (succ i) (≤-trans n i (succ i) n≤i (≤-succ i)))) ∣)

```
