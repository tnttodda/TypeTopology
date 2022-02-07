
```agda
{-# OPTIONS --without-K --exact-split #-}

open import SpartanMLTT hiding (decidable)
open import Two-Properties hiding (zero-is-not-one)
open import NaturalsOrder
open import IntegersB
-- open import IntegersOrder
open import IntegersAddition renaming (_+_ to _+ℤ_)
open import UF-Subsingletons

module BoehmReals (fe : {𝓤 𝓥 : Universe} → {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {f g : Π Y}
                           → f ∼ g → f ≡ g) where

open import InfiniteSearch2 fe

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

upLeft upRight : ℤ → ℤ
upLeft  = {!!}
upRight = {!!}

_≤ℤ_≤ℤ_ : ℤ → ℤ → ℤ → 𝓤₀ ̇ 
x ≤ℤ y ≤ℤ z = (x ≤ℤ y) × (y ≤ℤ z)

_below_ : ℤ → ℤ → 𝓤₀ ̇ 
x below y = {!!} -- downLeft y ≤ℤ x ≤ℤ downRight y

×-decidable : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → decidable X → decidable Y → decidable (X × Y)
×-decidable (inl  x) (inl  y) = inl (x , y)
×-decidable (inl  _) (inr ¬y) = inr (λ (_ , y) → ¬y y)
×-decidable (inr ¬x) (inl  _) = inr (λ (x , _) → ¬x x)
×-decidable (inr ¬x) (inr  _) = inr (λ (x , _) → ¬x x)

below-decidable : (x y : ℤ) → decidable (x below y)
below-decidable x y
 = ×-decidable
     (≤ℤ-decidable (y +ℤ y) x)
     (≤ℤ-decidable x (succℤ (succℤ (y +ℤ y))))

𝕂 : 𝓤₀ ̇
𝕂 = Σ α ꞉ (ℤ → ℤ) , Π n ꞉ ℤ , {!!} -- α n below α (predℤ n) 

_below_and_ : ℤ → ℤ → ℤ → 𝓤₀ ̇ 
x below y and z = x below y × x below z

below-and-decidable : (x y z : ℤ) → decidable (x below y and z)
below-and-decidable x y z = {!!} -- ×-decidable (below-decidable x y) (below-decidable x z)

dec-to-𝟚 : {X : 𝓤 ̇ } → decidable X → 𝟚
dec-to-𝟚 (inl _) = ₁
dec-to-𝟚 (inr _) = ₀

abs : ℤ → ℕ
abs (pos x)     = x
abs (negsucc x) = succ x

−ℤ_ : ℤ → ℤ
−ℤ (pos 0) = pos 0
−ℤ (pos (succ x)) = negsucc x
−ℤ (negsucc x) = pos (succ x)

share-ancestor : (x y : ℤ) → 𝓤₀ ̇
share-ancestor x y = abs (x +ℤ (−ℤ y)) ≤ℕ 2

share-ancestor-decidable : (x y : ℤ) → decidable (share-ancestor x y)
share-ancestor-decidable x y = ≤-decidable _ _

c' : {Y : ℕ → 𝓥 ̇ } → ((n : ℕ) → decidable (Y n)) → (ℕ → 𝟚)
c' ds n = dec-to-𝟚 (ds n)

-- Other:
discrete-cc : {X : 𝓤 ̇ } → is-discrete X → X × X → (ℕ → 𝟚)
discrete-cc ds (x , y) = c' (λ _ → ds x y)

c : (ℤ → ℤ) × (ℤ → ℤ) → (ℕ → 𝟚)
c  (α , β) = c' (λ n → share-ancestor-decidable (α (pos n)) (β (pos n)))

```
