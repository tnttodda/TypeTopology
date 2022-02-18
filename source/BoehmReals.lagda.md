```agda
{-# OPTIONS --without-K --exact-split #-}

open import SpartanMLTT hiding (decidable)
open import Two-Properties hiding (zero-is-not-one)
open import NaturalsOrder
open import NaturalsAddition renaming (_+_ to _+ℕ_)
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

diff : ℤ → ℤ → ℕ
diff x y = abs (x −ℤ y)

abs-flip : (x y : ℤ) → diff x y ≡ diff y x
abs-flip x y = ap abs (neg-flip x y) ∙ abs-neg (y −ℤ x) ⁻¹
```

Definition of below and thus 𝕂

```agda
_/2 : ℕ → ℕ
0 /2 = 0
1 /2 = 0
succ (succ n) /2 = succ (n /2)

sign : ℤ → (ℕ → ℤ)
sign (pos     _) = pos
sign (negsucc _) = negsucc

num : ℤ → ℕ
num  (pos     n) = n
num  (negsucc n) = n

odd even : ℤ → 𝓤₀ ̇
odd (pos                   0) = 𝟘
odd (pos                   1) = 𝟙
odd (pos (succ (succ x)))     = odd (pos x)
odd (negsucc               0) = 𝟙
odd (negsucc               1) = 𝟘
odd (negsucc (succ (succ x))) = odd (negsucc x)
even x = ¬ odd x

even-or-odd? : (x : ℤ) → even x + odd x
even-or-odd? (pos                   0) = inl (λ x → x)
even-or-odd? (pos                   1) = inr ⋆
even-or-odd? (pos (succ (succ x)))     = even-or-odd? (pos x)
even-or-odd? (negsucc               0) = inr ⋆
even-or-odd? (negsucc               1) = inl (λ x → x)
even-or-odd? (negsucc (succ (succ x))) = even-or-odd? (negsucc x)

odd-is-prop : (x : ℤ) → is-prop (odd x)
odd-is-prop (pos                   0) = 𝟘-is-prop
odd-is-prop (pos                   1) = 𝟙-is-prop
odd-is-prop (pos (succ (succ x)))     = odd-is-prop (pos x)
odd-is-prop (negsucc               0) = 𝟙-is-prop
odd-is-prop (negsucc               1) = 𝟘-is-prop
odd-is-prop (negsucc (succ (succ x))) = odd-is-prop (negsucc x)

¬-is-prop : {X : 𝓤 ̇ } → is-prop (¬ X)
¬-is-prop p q = fe (λ i → 𝟘-is-prop (p i) (q i))

even-is-prop : (x : ℤ) → is-prop (even x)
even-is-prop x = ¬-is-prop

even-or-odd-is-prop : (x : ℤ) → (p q : even x + odd x) → p ≡ q
even-or-odd-is-prop x = +-is-prop (even-is-prop x) (odd-is-prop x) id

downLeft downMid downRight upLeft upRight : ℤ → ℤ
downLeft  x = x +ℤ x
downMid   x = downLeft x +ℤ (ι 1)
downRight x = downLeft x +ℤ (ι 2)
upRight   x = sign x (num x /2)

upLeft' : (x : ℤ) → even x + odd x → ℤ
upLeft' x (inl _) = predℤ (upRight x)
upLeft' x (inr _) = upRight x

upLeft    x = upLeft' x (even-or-odd? x)

odd-succ2 : (x : ℤ) → odd x → odd (succℤ (succℤ x))
odd-succ2 (pos (succ x)) o = o
odd-succ2 (negsucc 0) o = ⋆
odd-succ2 (negsucc (succ (succ x))) o = o

even-succ2 : (x : ℤ) → even x → even (succℤ (succℤ x))
even-succ2 (pos 0) e = id
even-succ2 (pos (succ x)) e = e
even-succ2 (negsucc 0) e = λ _ → e ⋆
even-succ2 (negsucc (succ zero)) e = λ z → z
even-succ2 (negsucc (succ (succ x))) e = e

upLeft-even : (x : ℤ) → even x → upLeft x ≡ predℤ (upRight x)
upLeft-even x e = ap (upLeft' x) (even-or-odd-is-prop x (even-or-odd? x) (inl e))

upLeft-odd : (x : ℤ) → odd x → upLeft x ≡ upRight x
upLeft-odd x o = ap (upLeft' x) (even-or-odd-is-prop x (even-or-odd? x) (inr o))

_below_ : ℤ → ℤ → 𝓤₀ ̇ 
x below y = downLeft y ≤ℤ x ≤ℤ downRight y

_below2_ : ℤ → ℤ → 𝓤₀ ̇ 
x below2 y = downLeft (downLeft y) ≤ℤ x ≤ℤ downRight (downRight y)

_below'_ : ℤ → ℤ → 𝓤₀ ̇
x below' y = (x ≡ downLeft y) + (x ≡ downMid y) + (x ≡ downRight y)

_below''_ : ℤ → ℤ → 𝓤₀ ̇ 
x below'' y = diff x (downLeft y) ≤ℕ 2

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

≤ℕ-up : (x y : ℕ) → x ≤ℕ y → ¬ (x ≡ y) → succ x ≤ℕ y
≤ℕ-up zero zero p f = f refl
≤ℕ-up zero (succ y) p f = ⋆
≤ℕ-up (succ x) (succ y) p f = ≤ℕ-up x y p (f ∘ ap succ)

≤ℤ-up : (x y : ℤ) → x ≤ℤ y → ¬ (x ≡ y) → succℤ x ≤ℤ y
≤ℤ-up (pos x) (pos y) p f = ≤ℕ-up x y p (f ∘ ap pos)
≤ℤ-up (negsucc 0) (pos y) _ _ = ⋆
≤ℤ-up (negsucc (succ x)) (pos y) _ _ = ⋆
≤ℤ-up (negsucc 0) (negsucc y) p f = f (ap negsucc (zero-minimal'' y p ⁻¹))
≤ℤ-up (negsucc (succ x)) (negsucc y) p f
 = ≤ℕ-up y (succ x) p (λ y≡sx → f (ap negsucc (y≡sx ⁻¹)))

≤ℤ-split : (x y : ℤ) → x ≤ℤ y → (x ≡ y) + (succℤ x ≤ℤ y)
≤ℤ-split x y p
 = Cases (ℤ-is-discrete x y) inl (inr ∘ ≤ℤ-up x y p)

≤ℤ-anti : (x y : ℤ) → x ≤ℤ y → y ≤ℤ x → x ≡ y
≤ℤ-anti (pos x) (pos y) x≤y y≤x = ap pos (≤-anti x y x≤y y≤x)
≤ℤ-anti (negsucc x) (negsucc y) x≤y y≤x = ap negsucc (≤-anti x y y≤x x≤y)

unsucc-≤ℤ : (x y : ℤ) → succℤ x ≤ℤ succℤ y → x ≤ℤ y
unsucc-≤ℤ (pos x) (pos y) sx≤sy = sx≤sy
unsucc-≤ℤ (pos x) (negsucc 0) ()
unsucc-≤ℤ (pos x) (negsucc (succ y)) ()
unsucc-≤ℤ (negsucc x) (pos y) sx≤sy = ⋆
unsucc-≤ℤ (negsucc x) (negsucc 0) sx≤sy = ⋆
unsucc-≤ℤ (negsucc (succ x)) (negsucc (succ y)) sx≤sy = sx≤sy

below→below' : (x y : ℤ) → x below y → x below' y
below→below' x y (p , q)
 = Cases (≤ℤ-split (downLeft y) x p) (inl ∘ _⁻¹)
     λ ly≤sx → Cases (≤ℤ-split x (downRight y) q) (inr ∘ inr)
     (λ x≤sry → inr (inl (≤ℤ-anti x (downMid y) (unsucc-≤ℤ x (downMid y) x≤sry) ly≤sx)))

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

+-decidable : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
            → decidable X → decidable Y → decidable (X + Y)
+-decidable (inl  x) _        = inl (inl x)
+-decidable (inr ¬x) (inl  y) = inl (inr y)
+-decidable (inr ¬x) (inr ¬y) = inr (cases ¬x ¬y)

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
share-ancestor x y = Σ z ꞉ ℤ , (x below z) × (y below z)

upRight-succ : (x : ℤ) → upRight (succℤ (succℤ x)) ≡ succℤ (upRight x)
upRight-succ (pos x) = refl
upRight-succ (negsucc 0) = refl
upRight-succ (negsucc 1) = refl
upRight-succ (negsucc (succ (succ x))) = refl

upLeft'-succ : (x : ℤ) → (p : even x + odd x)
             → upLeft (succℤ (succℤ x)) ≡ succℤ (upLeft' x p)
upLeft'-succ x (inl e) = upLeft-even (succℤ (succℤ x)) (even-succ2 x e)
                       ∙ (succpredℤ (upRight x)
                       ∙ predsuccℤ (upRight x) ⁻¹
                       ∙ ap predℤ (upRight-succ x ⁻¹)) ⁻¹
upLeft'-succ x (inr o) = upLeft-odd (succℤ (succℤ x)) (odd-succ2 x o)
                       ∙ upRight-succ x

upLeft-succ : (x : ℤ) → upLeft (succℤ (succℤ x)) ≡ succℤ (upLeft x)
upLeft-succ x = upLeft'-succ x (even-or-odd? x)

downLeft-below : (x : ℤ) → downLeft x below x
downLeft-below x = (≤ℤ-refl (x +ℤ x))
                 , ≤ℤ-trans (x +ℤ x) (succℤ (x +ℤ x)) (succℤ (succℤ (x +ℤ x)))
                     (≤ℤ-succ (x +ℤ x))
                     (≤ℤ-succ (succℤ (x +ℤ x)))

downMid-below : (x : ℤ) → downMid x below x
downMid-below x = {!!}

downRight-below : (x : ℤ) → downRight x below x
downRight-below x = {!!}

{-
x/2-double-even : (x : ℤ) → even x → ((x /2) +ℤ (x /2)) ≡ x
x/2-double-even = ?

x/2-double-odd : (x : ℤ) → odd x → ((x /2) +ℤ (x /2)) ≡ x +ℤ (sign x 1)
x/2-double-odd = ?
-}

up-below-right : (x : ℤ) → x below upRight x
up-below-right (pos zero) = ⋆ , ⋆
up-below-right (pos (succ zero)) = ⋆ , ⋆
up-below-right (pos (succ (succ x)))
 = transport (pos (succ (succ x)) below_) (upRight-succ (pos x) ⁻¹)
     (below'→below (pos (succ (succ x))) (pos (succ (x /2))) {!!})
up-below-right (negsucc zero) = ⋆ , ⋆
up-below-right (negsucc (succ zero)) = ⋆ , ⋆
up-below-right (negsucc (succ (succ x))) = {!!}

up-below : (x : ℤ) → (x below upLeft x) × (x below upRight x)
up-below = {!!} 

below-up : (x y : ℤ) → x below y → (y ≡ upLeft x) + (y ≡ upRight x)
below-up x y (p , q) = {!!}

share-ancestor-up : (x y : ℤ) → share-ancestor x y
                  → (upLeft  x ≡ upLeft y) + (upLeft  x ≡ upRight y)
                  + (upRight x ≡ upLeft y) + (upRight x ≡ upRight y)
share-ancestor-up x y (z , p , q) = γ x y z (below-up x z p) (below-up y z q) where
  γ : ∀ x y z
    → (z ≡ upLeft x) + (z ≡ upRight x)
    → (z ≡ upLeft y) + (z ≡ upRight y)
    → (upLeft  x ≡ upLeft y) + (upLeft  x ≡ upRight y)
    + (upRight x ≡ upLeft y) + (upRight x ≡ upRight y)
  γ x y .(upLeft x)  (inl refl) (inl r) = inl r
  γ x y .(upLeft x)  (inl refl) (inr r) = inr (inl r)
  γ x y .(upRight x) (inr refl) (inl r) = inr (inr (inl r))
  γ x y .(upRight x) (inr refl) (inr r) = inr (inr (inr r))

share-ancestor-decidable : (x y : ℤ) → decidable (share-ancestor x y)
share-ancestor-decidable x y = Cases γ (inl ∘ δ) (inr ∘ ζ)
 where
   γ : decidable ((y below upLeft x) + (y below upRight x)) 
   γ = +-decidable (below-decidable y (upLeft x)) (below-decidable y (upRight x))
   δ : (y below upLeft x) + (y below upRight x) → share-ancestor x y
   δ (inl g) = upLeft  x , pr₁ (up-below x) , g
   δ (inr g) = upRight x , pr₂ (up-below x) , g
   ζ : ¬ ((y below upLeft x) + (y below upRight x)) → ¬ share-ancestor x y
   ζ f (z , p , q) = f (Cases (below-up x z p)
                         (λ l → inl (transport (y below_) l q))
                         (λ r → inr (transport (y below_) r q)))

share-ancestor-refl : (x : ℤ) → share-ancestor x x
share-ancestor-refl x = upRight x , pr₂ (up-below x) , pr₂ (up-below x)

share-ancestor-sym : (x y : ℤ) → share-ancestor x y → share-ancestor y x
share-ancestor-sym x y (z , p , q) = z , q , p

share-ancestor-up2 : (x : ℤ) → share-ancestor (upLeft x) (upRight x)
share-ancestor-up2 x = {!!}

share-ancestor-trans : (x y z : ℤ)
                     → ((a , _) : share-ancestor x y)
                     → ((b , _) : share-ancestor y z)
                     → share-ancestor a b
share-ancestor-trans x y z (a , p) (b , q)
 = Cases γ (Cases δ f g) (Cases δ h i)
 where
   γ : (a ≡ upLeft y) + (a ≡ upRight y)
   γ = below-up y a (pr₂ p)
   δ : (b ≡ upLeft y) + (b ≡ upRight y)
   δ = below-up y b (pr₁ q)
   f : b ≡ upLeft y → a ≡ upLeft y → share-ancestor a b
   f w e = transport (share-ancestor a) (e ∙ w ⁻¹)
             (share-ancestor-refl a)
   g : b ≡ upRight y → a ≡ upLeft y → share-ancestor a b
   g w e = transport (share-ancestor a) (w ⁻¹)
             (transport (λ - → share-ancestor - (upRight y)) (e ⁻¹)
               (share-ancestor-up2 y))
   h : b ≡ upLeft y → a ≡ upRight y → share-ancestor a b
   h w e = transport (share-ancestor a) (w ⁻¹)
             (transport (λ - → share-ancestor - (upLeft y)) (e ⁻¹)
               (share-ancestor-sym (upLeft y) (upRight y)
                 (share-ancestor-up2 y)))
   i : b ≡ upRight y → a ≡ upRight y → share-ancestor a b
   i w e = transport (share-ancestor a) (e ∙ w ⁻¹)
             (share-ancestor-refl a)


above-share-ancestor : (x y a b : ℤ) → x below a → y below b
                     → ((c , _) : share-ancestor x y)
                     → share-ancestor a b
above-share-ancestor x y a b p q (c , r , s)
 = share-ancestor-trans x (downMid c) y (a , p , {!!}) (b , {!!} , q)

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
               (α (pos       n ))  (β (pos       n ))
              (γα (pos (succ n))) (γβ (pos (succ n))))

c-sym : (α β : 𝕂) → c (α , β) ≡ c (β , α)
c-sym (α , γα) (β , γβ)
 = ℕ∞-equals λ i → ?

c-eai : (α : 𝕂) → c (α , α) ≡ ∞
c-eai (α , _)
 = ℕ∞-equals (λ i → dec-to-𝟚-is-₁ (share-ancestor-refl (α (pos i))))

c-ult' : (α β ζ : 𝕂) (n : ℕ) → pr₁ (min (c (α , β)) (c (β , ζ))) (succ n) ≡ ₁
       → pr₁ (c (α , ζ)) n ≡ ₁
c-ult' α β ζ n r
 = {!!}

c-ult : (α β ζ : 𝕂) → min (c (α , β)) (c (β , ζ)) ≼ c (α , ζ)
c-ult α β ζ n r
 = {!pr₂ (c (α , ζ!}
 {- dec-to-𝟚-is-₁
     (share-ancestor-trans
       (pr₁ α (pos n))
       (pr₁ β (pos n))
       (pr₁ ζ (pos n))
       (dec-to-𝟚-was-₁ (Lemma[min𝟚ab≡₁→a≡₁] {pr₁ (c (α , β)) n} {pr₁ (c (β , ζ)) n} r))
       (dec-to-𝟚-was-₁ (Lemma[min𝟚ab≡₁→b≡₁] {pr₁ (c (α , β)) n} {pr₁ (c (β , ζ)) n} r))) -}

-- Incorrect!! The sequences don't converge
c-iae : (α β : 𝕂) → c (α , β) ≡ ∞ → α ≡ β
c-iae (α , _) (β , _) e = {!!}
 where
   γ : α ≡ β
   γ = {!!}
```
