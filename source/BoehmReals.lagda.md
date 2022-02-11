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
```

ℤ operations

```agda
ι : ℕ → ℤ
ι = pos

_≤ℤ_ : ℤ → ℤ → 𝓤₀ ̇
pos x     ≤ℤ pos y     = x ≤ℕ y
negsucc x ≤ℤ negsucc y = y ≤ℕ x
pos _     ≤ℤ negsucc _ = 𝟘
negsucc _ ≤ℤ pos _     = 𝟙

_≤ℤ_≤ℤ_ : ℤ → ℤ → ℤ → 𝓤₀ ̇ 
x ≤ℤ y ≤ℤ z = (x ≤ℤ y) × (y ≤ℤ z)

_−ℤ_ : ℤ → ℤ → ℤ
x −ℤ y = x +ℤ (−ℤ y)

neg-flip : (x y : ℤ) → (x −ℤ y) ≡ −ℤ (y −ℤ x)
neg-flip x y
 = ap (_−ℤ y) (minus-minus-is-plus x ⁻¹)
 ∙ negation-dist (−ℤ x) y
 ∙ ap (λ - → −ℤ -) (ℤ+-comm (−ℤ x) y)

neg-some : (x y : ℤ) → (−ℤ x) +ℤ (−ℤ y) ≡ −ℤ (x +ℤ y)
neg-some = negation-dist

neg-same : (x : ℤ) → (x −ℤ x) ≡ ι 0
neg-same x = ℤ-sum-of-inverse-is-zero x

abs : ℤ → ℕ
abs (pos x)     = x
abs (negsucc x) = succ x

abs-0-is-0 : abs (ι 0) ≡ 0
abs-0-is-0 = refl

abs-neg : (x : ℤ) → abs x ≡ abs (−ℤ x)
abs-neg (pos 0) = refl
abs-neg (pos (succ x)) = refl
abs-neg (negsucc x) = refl

abs-flip : (x y : ℤ) → abs (x −ℤ y) ≡ abs (y −ℤ x)
abs-flip x y = ap abs (neg-flip x y) ∙ abs-neg (y −ℤ x) ⁻¹
```

Definition of below and thus 𝕂

```agda
downLeft downMid downRight upLeft upRight : ℤ → ℤ
downLeft  x = x +ℤ x
downMid   x = downLeft x +ℤ (ι 1)
downRight x = downLeft x +ℤ (ι 2) 
upLeft    x = {!!}
upRight   x = {!!}

_below_ : ℤ → ℤ → 𝓤₀ ̇ 
x below y = downLeft y ≤ℤ x ≤ℤ downRight y

_below'_ : ℤ → ℤ → 𝓤₀ ̇
x below' y = (x ≡ downLeft y) + (x ≡ downMid y) + (x ≡ downRight y)

succ-lc : (x y : ℕ) → succ x ≡ succ y → x ≡ y
succ-lc zero zero refl = refl
succ-lc (succ x) (succ .x) refl = refl

ℕ-is-discrete : is-discrete ℕ
ℕ-is-discrete zero zero = inl refl
ℕ-is-discrete zero (succ y) = inr (λ ())
ℕ-is-discrete (succ x) zero = inr (λ ())
ℕ-is-discrete (succ x) (succ y)
 = Cases (ℕ-is-discrete x y) (inl ∘ ap succ) (inr ∘ (λ f e → f (succ-lc x y e)))

pos-lc : (x y : ℕ) → pos x ≡ pos y → x ≡ y
pos-lc x .x refl = refl

negsucc-lc : (x y : ℕ) → negsucc x ≡ negsucc y → x ≡ y
negsucc-lc x .x refl = refl

ℤ-is-discrete : is-discrete ℤ
ℤ-is-discrete (pos x) (pos y)
 = Cases (ℕ-is-discrete x y) (inl ∘ ap pos) (inr ∘ (λ f e → f (pos-lc x y e)))
ℤ-is-discrete (negsucc x) (negsucc y)
 = Cases (ℕ-is-discrete x y) (inl ∘ ap negsucc) (inr ∘ (λ f e → f (negsucc-lc x y e)))
ℤ-is-discrete (pos x) (negsucc y) = inr (λ ())
ℤ-is-discrete (negsucc x) (pos y) = inr (λ ())

≤ℕ-up : (x y : ℕ) → x ≤ℕ y → ¬ (x ≡ y) → x ≤ℕ succ y
≤ℕ-up zero y p f = ⋆
≤ℕ-up (succ x) (succ y) p f = ≤ℕ-up x y p (f ∘ ap succ)

≤ℤ-up : (x y : ℤ) → x ≤ℤ y → ¬ (x ≡ y) → x ≤ℤ succℤ y
≤ℤ-up (pos x) (pos y) p f = ≤ℕ-up x y p (f ∘ ap pos)
≤ℤ-up (negsucc x) (pos y) _ _ = ⋆
≤ℤ-up (negsucc x) (negsucc 0) _ _ = ⋆
≤ℤ-up (negsucc x) (negsucc (succ y)) p f = {!!}

≤ℤ-split : (x y : ℤ) → x ≤ℤ y → (x ≡ y) + (x ≤ℤ succℤ y)
≤ℤ-split x y p
 = Cases (ℤ-is-discrete x y) inl (inr ∘ ≤ℤ-up x y p)

fact : (x y : ℤ) → y ≤ℤ succℤ x → x ≤ℤ succℤ (succℤ (succℤ y)) → x ≡ succℤ y
fact (pos x) (pos x₁) y≤sx x≤sssy = {!!}
fact (pos x) (negsucc x₁) y≤sx x≤sssy = {!!}
fact (negsucc x) (pos x₁) y≤sx x≤sssy = {!!}
fact (negsucc x) (negsucc x₁) y≤sx x≤sssy = {!!}

below→below' : (x y : ℤ) → x below y → x below' y
below→below' x y (p , q)
 = Cases (≤ℤ-split (downLeft y) x p) (inl ∘ _⁻¹)
     λ ly≤sx → Cases (≤ℤ-split x (downRight y) q) (inr ∘ inr)
     (λ x≤sry → inr (inl {!!}))

≤ℤ-succ : (x : ℤ) → x ≤ℤ succℤ x
≤ℤ-succ (pos x) = ≤-succ x
≤ℤ-succ (negsucc 0) = ⋆
≤ℤ-succ (negsucc (succ x)) = ≤-succ x

≤ℤ-trans : (x y z : ℤ) → x ≤ℤ y → y ≤ℤ z → x ≤ℤ z
≤ℤ-trans (pos x) (pos y) (pos z) p q = ≤-trans x y z p q
≤ℤ-trans (negsucc x) (negsucc y) (negsucc 0) p q = ⋆
≤ℤ-trans (negsucc x) (negsucc y) (negsucc (succ z)) p q = ≤-trans (succ z) y x q p
≤ℤ-trans (negsucc x) (pos y) (pos z) p q = ⋆
≤ℤ-trans (negsucc x) (negsucc y) (pos z) p q = ⋆

≤ℤ-refl : (x : ℤ) → x ≤ℤ x
≤ℤ-refl (pos x) = ≤-refl x
≤ℤ-refl (negsucc x) = ≤-refl x

below'→below : (x y : ℤ) → x below' y → x below y
below'→below .(downLeft y) y (inl refl)
 = ≤ℤ-refl (y +ℤ y)
 , ≤ℤ-trans (y +ℤ y) (succℤ (y +ℤ y)) (succℤ (succℤ (y +ℤ y)))
     (≤ℤ-succ (y +ℤ y))
     (≤ℤ-succ (succℤ (y +ℤ y)))
below'→below .(downMid y) y (inr (inl refl))
 = ≤ℤ-succ (y +ℤ y)
 , ≤ℤ-succ (succℤ (y +ℤ y))
below'→below .(downRight y) y (inr (inr refl))
 = ≤ℤ-trans (y +ℤ y) (succℤ (y +ℤ y)) (succℤ (succℤ (y +ℤ y)))
     (≤ℤ-succ (y +ℤ y))
     (≤ℤ-succ (succℤ (y +ℤ y)))
 , ≤ℤ-refl (succℤ (succℤ (y +ℤ y)))

𝕂 : 𝓤₀ ̇
𝕂 = Σ α ꞉ (ℤ → ℤ) , Π n ꞉ ℤ , α n below α (predℤ n) 

×-decidable : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
            → decidable X → decidable Y → decidable (X × Y)
×-decidable (inl  x) (inl  y) = inl (x , y)
×-decidable (inl  _) (inr ¬y) = inr (λ (_ , y) → ¬y y)
×-decidable (inr ¬x) (inl  _) = inr (λ (x , _) → ¬x x)
×-decidable (inr ¬x) (inr  _) = inr (λ (x , _) → ¬x x)

≤ℤ-decidable : (x y : ℤ) → decidable (x ≤ℤ y)
≤ℤ-decidable (pos x) (pos y)         = ≤-decidable x y
≤ℤ-decidable (negsucc x) (negsucc y) = ≤-decidable y x
≤ℤ-decidable (pos _) (negsucc _)     = inr id
≤ℤ-decidable (negsucc _) (pos _)     = inl ⋆

below-decidable : (x y : ℤ) → decidable (x below y)
below-decidable x y
 = ×-decidable
     (≤ℤ-decidable (downLeft y) x)
     (≤ℤ-decidable x (downRight y))
```

Definition of share-ancestor and properties

```agda
share-ancestor : (x y : ℤ) → 𝓤₀ ̇
share-ancestor x y = abs (x −ℤ y) ≤ℕ 2

share-ancestor-decidable : (x y : ℤ) → decidable (share-ancestor x y)
share-ancestor-decidable x y = ≤-decidable (abs (x +ℤ (−ℤ y))) 2

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

above-share-ancestor : (x₁ x₂ y₁ y₂ : ℤ) → x₁ below y₁ → x₂ below y₂
                     → share-ancestor x₁ x₂
                     → share-ancestor y₁ y₂
above-share-ancestor x₁ x₂ y₁ y₂ (a , b) (c , d) dy≤2
 = {!!}
-- abs (x₁ − x₂) ≤ 2
-- 2y₁ ≤ x₁ ≤ (2y₁ + 2)
-- 2y₂ ≤ x₂ ≤ (2y₂ + 2)
-- abs (y₁ − y₂) ≤ 2
```

Definition of closeness function for sequences

```agda
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
```

discrete-cc : {X : 𝓤 ̇ } → is-discrete X → X × X → ℕ∞
discrete-cc ds (x , y) = c' (λ _ → ds x y) (λ _ → id)

Definition of closeness function for 𝕂

```agda
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
