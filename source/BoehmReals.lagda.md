```agda
{-# OPTIONS --without-K --exact-split #-}

open import SpartanMLTT hiding (decidable)
open import Two-Properties hiding (zero-is-not-one)
open import NaturalsOrder
open import IntegersB
-- open import IntegersOrder
open import IntegersAddition renaming (_+_ to _+ℤ_)
open import IntegersNegation renaming (-_  to  −ℤ_)
open import UF-Subsingletons

module BoehmReals (fe : {𝓤 𝓥 : Universe} → {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {f g : Π Y}
                           → f ∼ g → f ≡ g) where

open import InfiniteSearch2 fe

{-# BUILTIN INTEGER       ℤ       #-}
{-# BUILTIN INTEGERPOS    pos     #-}
{-# BUILTIN INTEGERNEGSUC negsucc #-}

ι : ℕ → ℤ
ι = pos

_≤ℤ_ : ℤ → ℤ → 𝓤₀ ̇
pos x     ≤ℤ pos y     = x ≤ℕ y
negsucc x ≤ℤ negsucc y = y ≤ℕ x
pos _     ≤ℤ negsucc _ = 𝟘
negsucc _ ≤ℤ pos _     = 𝟙

≤ℤ-decidable : (x y : ℤ) → decidable (x ≤ℤ y)
≤ℤ-decidable (pos x) (pos y)         = ≤-decidable x y
≤ℤ-decidable (negsucc x) (negsucc y) = ≤-decidable y x
≤ℤ-decidable (pos _) (negsucc _)     = inr id
≤ℤ-decidable (negsucc _) (pos _)     = inl ⋆

downLeft downMid downRight upLeft upRight : ℤ → ℤ
downLeft  x = x +ℤ x
downMid   x = downLeft x +ℤ (ι 1)
downRight x = downLeft x +ℤ (ι 2) 
upLeft    x = x
upRight   x = x

_≤ℤ_≤ℤ_ : ℤ → ℤ → ℤ → 𝓤₀ ̇ 
x ≤ℤ y ≤ℤ z = (x ≤ℤ y) × (y ≤ℤ z)

_below_ : ℤ → ℤ → 𝓤₀ ̇ 
x below y = downLeft y ≤ℤ x ≤ℤ downRight y

×-decidable : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
            → decidable X → decidable Y → decidable (X × Y)
×-decidable (inl  x) (inl  y) = inl (x , y)
×-decidable (inl  _) (inr ¬y) = inr (λ (_ , y) → ¬y y)
×-decidable (inr ¬x) (inl  _) = inr (λ (x , _) → ¬x x)
×-decidable (inr ¬x) (inr  _) = inr (λ (x , _) → ¬x x)

below-decidable : (x y : ℤ) → decidable (x below y)
below-decidable x y
 = ×-decidable
     (≤ℤ-decidable (downLeft y) x)
     (≤ℤ-decidable x (downRight y))

𝕂 : 𝓤₀ ̇
𝕂 = Σ α ꞉ (ℤ → ℤ) , Π n ꞉ ℤ , α n below α (predℤ n) 

abs : ℤ → ℕ
abs (pos x)     = x
abs (negsucc x) = succ x

_−ℤ_ : ℤ → ℤ → ℤ
x −ℤ y = x +ℤ (−ℤ y)

abs-0-is-0 : abs (ι 0) ≡ 0
abs-0-is-0 = refl

abs-neg : (x : ℤ) → abs x ≡ abs (−ℤ x)
abs-neg (pos 0) = refl
abs-neg (pos (succ x)) = refl
abs-neg (negsucc x) = refl

neg-flip : (x y : ℤ) → (x −ℤ y) ≡ −ℤ (y −ℤ x)
neg-flip x y
 = ap (_−ℤ y) (minus-minus-is-plus x ⁻¹)
 ∙ negation-dist (−ℤ x) y
 ∙ ap (λ - → −ℤ -) (ℤ+-comm (−ℤ x) y)

neg-some : (x y : ℤ) → (−ℤ x) +ℤ (−ℤ y) ≡ −ℤ (x +ℤ y)
neg-some = negation-dist

neg-same : (x : ℤ) → (x −ℤ x) ≡ ι 0
neg-same x = ℤ-sum-of-inverse-is-zero x

abs-flip : (x y : ℤ) → abs (x −ℤ y) ≡ abs (y −ℤ x)
abs-flip x y = ap abs (neg-flip x y) ∙ abs-neg (y −ℤ x) ⁻¹

share-ancestor : (x y : ℤ) → 𝓤₀ ̇
share-ancestor x y = abs (x −ℤ y) ≤ℕ 2

share-ancestor-refl : (x : ℤ) → share-ancestor x x
share-ancestor-refl x
 = transport (_≤ℕ 2) (abs-0-is-0 ∙ ap abs (neg-same x) ⁻¹) ⋆

share-ancestor-sym : (x y : ℤ) → share-ancestor x y
                   → share-ancestor y x
share-ancestor-sym x y = {!!}

share-ancestor-trans : (a b c : ℤ)
                     → share-ancestor a b → share-ancestor b c
                     → share-ancestor a c
share-ancestor-trans a b c s t = {!!}

share-ancestor-decidable : (x y : ℤ) → decidable (share-ancestor x y)
share-ancestor-decidable x y = ≤-decidable (abs (x +ℤ (−ℤ y))) 2

dec-to-𝟚 : {X : 𝓤 ̇ } → decidable X → 𝟚
dec-to-𝟚 (inl _) = ₁
dec-to-𝟚 (inr _) = ₀

dec-to-𝟚-is-₁ : {X : 𝓤 ̇ } → {d : decidable X} → X → dec-to-𝟚 d ≡ ₁
dec-to-𝟚-is-₁ {_} {_} {inl  _} _ = refl
dec-to-𝟚-is-₁ {_} {_} {inr ¬x} x = 𝟘-elim (¬x x)

dec-to-𝟚-was-₁ : {X : 𝓤 ̇ } → {d : decidable X} → dec-to-𝟚 d ≡ ₁ → X
dec-to-𝟚-was-₁ {_} {_} {inl x} _ = x
dec-to-𝟚-was-₁ {_} {_} {inr _} z = 𝟘-elim (zero-is-not-one z)

c' : {Y : ℕ → 𝓥 ̇ } → (ds : (n : ℕ) → decidable (Y n))
   → ((n : ℕ) → Y (succ n) → Y n) → ℕ∞
c' ds f
 = (λ n   → dec-to-𝟚 (ds n))
 , (λ n r → dec-to-𝟚-is-₁ (f n (dec-to-𝟚-was-₁ r))) 

-- Other:
discrete-cc : {X : 𝓤 ̇ } → is-discrete X → X × X → ℕ∞
discrete-cc ds (x , y) = c' (λ _ → ds x y) (λ _ → id)

above-share-ancestor : (x₁ x₂ y₁ y₂ : ℤ) → x₁ below y₁ → x₂ below y₂
                     → share-ancestor x₁ x₂
                     → share-ancestor y₁ y₂
above-share-ancestor x₁ x₂ y₁ y₂ (a , b) (c , d) dy≤2
 = {!!}
-- abs (x₁ − x₂) ≤ 2
-- 2y₁ ≤ x₁ ≤ (2y₁ + 2)
-- 2y₂ ≤ x₂ ≤ (2y₂ + 2)
-- abs (y₁ − y₂) ≤ 2

c : 𝕂 × 𝕂 → ℕ∞
c  ((α , γα) , (β , γβ))
 = c' (λ n → share-ancestor-decidable (α (pos n)) (β (pos n)))
      (λ n → above-share-ancestor
         (α (pos (succ n)))  (β (pos (succ n)))
         (α (pos       n))   (β (pos       n))
        (γα (pos (succ n))) (γβ (pos (succ n))))

c-sym : (α β : 𝕂) → c (α , β) ≡ c (β , α)
c-sym (α , γα) (β , γβ)
 = ℕ∞-equals (λ i → ap (λ - → dec-to-𝟚 (≤-decidable - 2)) (abs-flip (α (pos i)) (β (pos i))))

c-eai : (α : 𝕂) → c (α , α) ≡ ∞
c-eai (α , _)
 = ℕ∞-equals (λ i → dec-to-𝟚-is-₁ (share-ancestor-refl (α (pos i))))

c-ult : (α β ζ : 𝕂) → min (c (α , β)) (c (β , ζ)) ≼ c (α , ζ)
c-ult α β ζ n r
 = dec-to-𝟚-is-₁
     (share-ancestor-trans
       (pr₁ α (pos n))
       (pr₁ β (pos n))
       (pr₁ ζ (pos n))
       (dec-to-𝟚-was-₁ (Lemma[min𝟚ab≡₁→a≡₁] {pr₁ (c (α , β)) n} {pr₁ (c (β , ζ)) n} r))
       (dec-to-𝟚-was-₁ (Lemma[min𝟚ab≡₁→b≡₁] {pr₁ (c (α , β)) n} {pr₁ (c (β , ζ)) n} r)))

-- Incorrect!! The sequences don't converge
c-iae : (α β : 𝕂) → c (α , β) ≡ ∞ → α ≡ β
c-iae (α , _) (β , _) e = {!!}
 where
   γ : α ≡ β
   γ = {!!}

```
