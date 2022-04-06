```agda
{-# OPTIONS --without-K --exact-split #-}

open import UF-Equiv
open import UF-FunExt
open import UF-Subsingletons
open import SpartanMLTT
open import Two-Properties hiding (zero-is-not-one)
open import NaturalsOrder
open import IntegersOrder
open import IntegersB
open import NaturalsAddition renaming (_+_ to _+ℕ_)
open import IntegersAddition renaming (_+_ to _+ℤ_)
open import IntegersNegation renaming (-_  to  −ℤ_)
open import UF-Subsingletons
open import NaturalsOrder
open import DecidableAndDetachable

module TernaryBoehmReals (fe : FunExt) (pe : PropExt) where

open import SearchableTypes fe pe
open import TernaryBoehmRealsPrelude fe
```

## Idea and Illustration

We encode real numbers using the data type for ternary Boehm reals 𝕂.

Each 𝕂 is a function x ꞉ ℤ → ℤ with some restrictions on it, so that we only
have our encodings of real numbers inside 𝕂, and not any function of type ℤ → ℤ.

The function x : ℤ → ℤ takes a "precision-level" n : ℤ and gives back an
encoding x(n) : ℤ of a real interval.

The idea is that each precision-level n : ℤ represents a "layer4" in the
following illustrative "brick pattern".

Level n+1 has bricks half the size of those on level n.
Here level 0 and 1 are shown.

-1        0         1         2
__________ _________ _________ ____
|___-2____|____0____|____2____|____
 ____|___-1____|____1____|____3____|
 ____ ____ ____ ____ ____ ____ ____
|-4__|-2__|_0__|_2__|_4__|_6__|_8__|
 _|_-3_|_-1_|__1_|__3_|__5_|__7_|__
4
Then, x(n) : ℤ refers to a precise labelled "brick" in the brick pattern.

Each brick encodes a real interval; specifically the interval ⟪ x(n) , n ⟫ as
defined below.

⟪_⟫ : ℤ × ℤ → ℚ × ℚ
⟪ k , p ⟫ = (k / 2^{p + 1}) , ((k + 2) / 2^{p + 1})

## Formal definition

therefore, an encoding of a real number is a sequence of encodings of real
intervals -- the restriction we add is that each brick x(n) is "below" the brick
-- x(n+1); meaning ⟪ x(n+1) , n+1 ⟫ ⊂ ⟪ x(n) , n ⟫.

note that there are precisely three brick below each brick.

```
downLeft downMid downRight : ℤ → ℤ
downLeft  a = a +ℤ a
downMid   a = succℤ (downLeft a)
downRight a = succℤ (downMid  a)

_below_ : ℤ → ℤ → 𝓤₀ ̇ 
a below b = downLeft b ≤ℤ a ≤ℤ downRight b

𝕂 : 𝓤₀ ̇ 
𝕂 = Σ x ꞉ (ℤ → ℤ) , ((n : ℤ) → (x (succℤ n)) below (x n))
```

The real number represented by x : 𝕂 is defined as ⟦ x ⟧ : ℝ.

```
⟨_⟩ : 𝕂 → (ℤ → ℤ)
⟨ x , _ ⟩ = x
```

⟦_⟧ : 𝕂 → ℝ
⟦ x ⟧ = ⋂ᵢ ⟪ ⟨ x ⟩ i ⟫

-------------------------------------------------------------------

## upLeft / upRight

We may also wish to go "up" the brick pattern from a specific brick.

Even-numbered bricks are covered by two bricks at the preceeding
precision-level, whereas odd-numbered bricks are covered by exactly one.

We define the functions upLeft : ℤ → ℤ and upRight : ℤ → ℤ, such that when k : ℤ
is even upLeft k = predℤ (upRight k) and when n is odd upLeft k = upRight k.

```
upRight : ℤ → ℤ
upRight x = sign x (num x /2)

upLeft' : (x : ℤ) → even x + odd x → ℤ
upLeft' x (inl _) = predℤ (upRight x)
upLeft' x (inr _) =        upRight x

upLeft : ℤ → ℤ
upLeft x = upLeft' x (even-or-odd? x)

upLeft-elim : (x : ℤ) → (P : ℤ → 𝓤 ̇ )
            → P (predℤ (upRight x)) → P (upRight x)
            → P (upLeft x)
upLeft-elim x P Pe Po with even-or-odd? x
... | (inl e) = Pe
... | (inr o) = Po

odd-succ-succ : (x : ℤ) → odd x → odd (succℤ (succℤ x))
odd-succ-succ (pos x) = id
odd-succ-succ (negsucc zero) = id
odd-succ-succ (negsucc (succ (succ x))) = id

even-succ-succ : (x : ℤ) → even x → even (succℤ (succℤ x))
even-succ-succ (pos x) = id
even-succ-succ (negsucc zero) = id
even-succ-succ (negsucc (succ (succ x))) = id

upLeft²-elim : (x : ℤ) → (P : ℤ → ℤ → 𝓤 ̇ )
             → P (predℤ (upRight x)) (predℤ (upRight (succℤ (succℤ x))))
             → P (upRight x) (upRight (succℤ (succℤ x)))
             → P (upLeft x) (upLeft (succℤ (succℤ x)))
upLeft²-elim x P Pe Po with even-or-odd? x
... | (inl e) = transport (P (predℤ (upRight x)))
                  (ap (upLeft' (succℤ (succℤ x)))
                     (even-or-odd-is-prop (succℤ (succℤ x))
                       (inl (even-succ-succ x e))
                       (even-or-odd? (succℤ (succℤ x)))))
                  Pe
... | (inr o) = transport (P (upRight x))
                  (ap (upLeft' (succℤ (succℤ x)))
                     (even-or-odd-is-prop (succℤ (succℤ x))
                        (inr (odd-succ-succ x o))
                        (even-or-odd? (succℤ (succℤ x)))))
                  Po

upLeft²-elim-pred : (x : ℤ) → (P : ℤ → ℤ → 𝓤 ̇ )
                  → P (predℤ (upRight (predℤ (predℤ x)))) (predℤ (upRight x))
                  → P (upRight (predℤ (predℤ x))) (upRight x)
                  → P (upLeft (predℤ (predℤ x))) (upLeft x)
upLeft²-elim-pred x P Pe Po
 = transport (P (upLeft y))
     (ap upLeft (ap succℤ (succpredℤ (predℤ x)) ∙ succpredℤ x))
     Py
 where
   y : ℤ
   y = predℤ (predℤ x)
   Pe' : P (predℤ (upRight y)) (predℤ (upRight (succℤ (succℤ y))))
   Pe' = transport
           (λ - → P (predℤ (upRight (predℤ (predℤ x)))) (predℤ (upRight -)))
           (succpredℤ _ ⁻¹ ∙ ap succℤ (succpredℤ _ ⁻¹))
           Pe
   Po' : P (upRight y) (upRight (succℤ (succℤ y)))
   Po' = transport
           (λ - → P (upRight (predℤ (predℤ x))) (upRight -))
           (succpredℤ _ ⁻¹ ∙ ap succℤ (succpredℤ _ ⁻¹))
           Po
   Py : P (upLeft (predℤ (predℤ x))) (upLeft (succℤ (succℤ (predℤ (predℤ x)))))
   Py = upLeft²-elim y P Pe' Po'
```

upLeft-is-below  : (k : ℕ) → k below upLeft  k
upLeft-is-below  = {!!}

upRight-is-below : (k : ℕ) → k below upRight k
upRight-is-below = {!!}

## Replacement function

Given any α : 𝕂 and i : ℤ, we can replace all precision levels n <ℤ i
with rec upRight (i - n) α(i) (or upLeft) and still represent the same
real number.

replace : 𝕂 → ℤ → 𝕂
replace (α , γα) i = λ n → if   n <ℤ i
                           then rec upRight (i - n) α(i)
                           else α(n)
                   , λ n → if   n <ℤ i
                           then rec upRight-is-below (i - n) γα(i) 
                           else γα(n)

It is the case that for all α : 𝕂 and i : ℤ, ⟦ α ⟧ ≡ ⟦ replace α i ⟧.

What this means is that all information held at x(n) about locating
⟦ x ⟧ is held at x(n+1).

Similarly to the replacement function, we can construct 𝕂 using just
a function ℕ → ℤ.

build : (Σ x ꞉ (ℕ → ℤ) , (n : ℕ) → (x (succ n)) below (x n)) → ℤ → 𝕂
build (x , γx) i = λ n → if   n <ℤ i
                         then rec upRight (i - n)  x(0)
                         else x(n - i)
                 , λ n → if   n <ℤ i
                         then rec upRight-is-below (i - n) γx(i) 
                         else γx(n - i)

We can also build a 𝕂 that goes 'via' some given interval encoding.

```
build-via' : ((k , i) : ℤ × ℤ) (n : ℤ) → (n <ℤ i) + (n ≡ i) + (i <ℤ n) → ℤ
build-via' (k , i) n (inl      (j , sn+j≡i))
 = rec k upRight (succ j)
build-via' (k , i) n (inr (inl         n≡i))
 = k
build-via' (k , i) n (inr (inr (j , sn+j≡n)))
 = rec k downLeft (succ j)

build-via'-below
 : ((k , i) : ℤ × ℤ) (n : ℤ)
 → (η₁ : (succℤ n <ℤ i) + (succℤ n ≡ i) + (i <ℤ succℤ n))
 → (η₂ : (      n <ℤ i) + (      n ≡ i) + (i <ℤ       n))
 → build-via' (k , i) (succℤ n) η₁ below build-via' (k , i) n η₂
build-via'-below (k , i) n = {!!}

build-via : ℤ × ℤ → 𝕂
build-via (k , i) = (λ n → build-via' (k , i) n (η₁ n))
                  , λ n → build-via'-below (k , i) n (η₂ n) (η₁ n)
 where
   η₁ = λ (n : ℤ) → ℤ-trichotomous        n  i
   η₂ = λ (n : ℤ) → ℤ-trichotomous (succℤ n) i
```

-------------------------------------------------------------------

## Representing closed intervals

Given any specific brick on a specific level, i.e. (k , p) : ℤ × ℤ
representing ⟪ k , p ⟫, we can define an element of the closed
interval ⟪ k , p ⟫.

```
CompactInterval : ℤ × ℤ → 𝓤₀ ̇
CompactInterval (k , p) = Σ (x , _) ꞉ 𝕂 , x(p) ≡ k

ι : {i : ℤ × ℤ} → CompactInterval i → 𝕂
ι = pr₁
```

You can also build an element of a closed interval in a similar way

```
build-ci : (x : 𝕂) → (δ : ℤ) → CompactInterval (⟨ x ⟩ δ , δ)
build-ci x δ = x , refl

ℤ-trichotomous-is-prop
 : (n i : ℤ) → is-prop ((n <ℤ i) + (n ≡ i) + (i <ℤ n))
ℤ-trichotomous-is-prop = {!!}

build-via-ci : ((k , i) : ℤ × ℤ) → CompactInterval (k , i)
build-via-ci (k , i)
 = build-via (k , i)
 , ap (build-via' (k , i) i)
     (ℤ-trichotomous-is-prop i i (ℤ-trichotomous i i) (inr (inl refl)))
```

TODO

```
rec-upLeft/downLeft  : ℤ → ℤ → ℤ
rec-upLeft/downLeft x (pos n)     = rec x downLeft n
rec-upLeft/downLeft x (negsucc n) = rec x upLeft   (succ n)

rec-upRight/downRight  : ℤ → ℤ → ℤ
rec-upRight/downRight x (pos n)     = rec x downRight n
rec-upRight/downRight x (negsucc n) = rec x upRight   (succ n)

lower upper : ℤ × ℤ → ℤ → ℤ
lower (k , i) δ with ℤ-trichotomous i δ
... | inl      (n , si+n≡δ)  = rec k downLeft (succ n)
... | inr (inl refl)         = k
... | inr (inr (n , sδ+n≡i)) = rec k   upLeft (succ n)
upper (k , i) δ with ℤ-trichotomous i δ
... | inl      (n , si+n≡δ)  = rec k downRight (succ n)
... | inr (inl refl)         = k
... | inr (inr (n , sδ+n≡i)) = rec k   upRight (succ n)

_above_ : ℤ → ℤ → 𝓤₀ ̇ 
b above a = upLeft a ≤ℤ b ≤ℤ upRight a

_below'_ : ℤ → ℤ → 𝓤₀ ̇
a below' b = (a ≡ downLeft b) + (a ≡ downMid b) + (a ≡ downRight b)

upRight-suc : (a : ℤ) → upRight (succℤ (succℤ a)) ≡ succℤ (upRight a)
upRight-suc (pos zero) = refl
upRight-suc (pos (succ zero)) = refl
upRight-suc (pos (succ (succ x))) = refl
upRight-suc (negsucc zero) = refl
upRight-suc (negsucc (succ zero)) = refl
upRight-suc (negsucc (succ (succ x))) = refl

pred-upRight-suc : (a : ℤ) → predℤ (upRight (succℤ (succℤ a))) ≡ succℤ (predℤ (upRight a))
pred-upRight-suc (pos zero) = refl
pred-upRight-suc (pos (succ zero)) = refl
pred-upRight-suc (pos (succ (succ x))) = refl
pred-upRight-suc (negsucc zero) = refl
pred-upRight-suc (negsucc (succ zero)) = refl
pred-upRight-suc (negsucc (succ (succ x))) = refl

upLeft-suc : (a : ℤ) → upLeft (succℤ (succℤ a)) ≡ succℤ (upLeft a)
upLeft-suc a
 = upLeft²-elim a (λ a b → b ≡ succℤ a) (pred-upRight-suc a) (upRight-suc a)

pred-upRight-pred : (a : ℤ) → predℤ (upRight (predℤ (predℤ a))) ≡ predℤ (predℤ (upRight a))
pred-upRight-pred (pos zero) = refl
pred-upRight-pred (pos (succ zero)) = refl
pred-upRight-pred (pos (succ (succ x))) = refl
pred-upRight-pred (negsucc zero) = refl
pred-upRight-pred (negsucc (succ zero)) = refl
pred-upRight-pred (negsucc (succ (succ x))) = refl

upRight-pred : (a : ℤ) → upRight (predℤ (predℤ a)) ≡ predℤ (upRight a)
upRight-pred (pos 0) = refl
upRight-pred (pos 1) = refl
upRight-pred (pos (succ (succ x))) = refl
upRight-pred (negsucc 0) = refl
upRight-pred (negsucc 1) = refl
upRight-pred (negsucc (succ (succ x))) = refl

upLeft-pred : (a : ℤ) → upLeft (predℤ (predℤ a)) ≡ predℤ (upLeft a)
upLeft-pred a
 = upLeft²-elim-pred a (λ a b → a ≡ predℤ b) (pred-upRight-pred a) (upRight-pred a)
 
ℤ-elim : (P : ℤ → 𝓤 ̇ )
       → ((n : ℕ) → P (pos n)) → ((n : ℕ) → P (negsucc n))
       → Π P
ℤ-elim P Pp Pn (pos     n) = Pp n
ℤ-elim P Pp Pn (negsucc n) = Pn n

upLeft-downLeft-pos : (b : ℕ) → succℤ (upLeft (downLeft (pos b))) ≡ pos b
upLeft-downLeft-pos 0 = refl
upLeft-downLeft-pos (succ b)
 = ap (succℤ ∘ upLeft ∘ succℤ) (ℤ-left-succ-pos (pos b) b)
 ∙ ap succℤ (upLeft-suc (downLeft (pos b)))
 ∙ ap succℤ (upLeft-downLeft-pos b)

upLeft-downLeft-negsucc : (b : ℕ) → succℤ (upLeft (downLeft (negsucc b))) ≡ negsucc b
upLeft-downLeft-negsucc 0 = refl
upLeft-downLeft-negsucc (succ b)
 = ap (succℤ ∘ upLeft ∘ predℤ) (ℤ-left-pred-negsucc (negsucc b) b)
 ∙ ap succℤ (upLeft-pred (downLeft (negsucc b)))
 ∙ succpredℤ _ ∙ predsuccℤ _ ⁻¹
 ∙ ap predℤ (upLeft-downLeft-negsucc b)

upRight-downLeft-pos : (b : ℕ) → pos b ≡ upRight (downLeft (pos b))
upRight-downLeft-pos 0 = refl
upRight-downLeft-pos (succ b)
 = ap succℤ (upRight-downLeft-pos b)
 ∙ upRight-suc (downLeft (pos b)) ⁻¹
 ∙ ap (upRight ∘ succℤ) (ℤ-left-succ-pos (pos b) b ⁻¹)

upRight-downLeft-negsucc : (b : ℕ) → negsucc b ≡ upRight (downLeft (negsucc b))
upRight-downLeft-negsucc 0 = refl
upRight-downLeft-negsucc (succ b)
 = ap predℤ (upRight-downLeft-negsucc b)
 ∙ upRight-pred (downLeft (negsucc b)) ⁻¹
 ∙ ap (upRight ∘ predℤ) (ℤ-left-pred-negsucc (negsucc b) b ⁻¹)

below-implies-above-dL : (b : ℤ) → b above (downLeft b)
below-implies-above-dL b
 = (1 , ℤ-elim (λ b → succℤ (upLeft (downLeft b)) ≡ b)
          upLeft-downLeft-pos upLeft-downLeft-negsucc b)
 , (0 , ℤ-elim (λ b → b ≡ upRight (downLeft b))
          upRight-downLeft-pos upRight-downLeft-negsucc b)

upLeft-downMid-pos : (b : ℕ) → upLeft (downMid (pos b)) ≡ pos b
upLeft-downMid-pos 0 = refl
upLeft-downMid-pos (succ b)
 = ap (upLeft ∘ succℤ) (ℤ-left-succ-pos (pos b) (succ b))
 ∙ upLeft-suc (downMid (pos b))
 ∙ ap succℤ (upLeft-downMid-pos b)

upLeft-downMid-negsucc : (b : ℕ) → upLeft (downMid (negsucc b)) ≡ negsucc b
upLeft-downMid-negsucc 0 = refl
upLeft-downMid-negsucc (succ b)
 = ap (upLeft ∘ succℤ) (ℤ-left-pred-negsucc (negsucc b) (succ b))
 ∙ ap upLeft (succpredℤ (predℤ (downLeft (negsucc b))))
 ∙ ap (upLeft ∘ predℤ) (predsuccℤ (downLeft (negsucc b)) ⁻¹)
 ∙ upLeft-pred (downMid (negsucc b))
 ∙ ap predℤ (upLeft-downMid-negsucc b)

upRight-downMid-pos : (b : ℕ) → pos b ≡ upRight (downMid (pos b))
upRight-downMid-pos 0 = refl
upRight-downMid-pos (succ b)
 = ap succℤ (upRight-downMid-pos b)
 ∙ upRight-suc (downMid (pos b)) ⁻¹
 ∙ ap (upRight ∘ succℤ ∘ succℤ) (ℤ-left-succ-pos (pos b) b ⁻¹)

upRight-downMid-negsucc : (b : ℕ) → negsucc b ≡ upRight (downMid (negsucc b))
upRight-downMid-negsucc 0 = refl
upRight-downMid-negsucc (succ b)
 = ap predℤ (upRight-downMid-negsucc b)
 ∙ upRight-pred (downMid (negsucc b)) ⁻¹
 ∙ ap (upRight ∘ predℤ) (predsuccℤ _)
 ∙ ap upRight (ℤ-left-pred-negsucc (negsucc b) b ⁻¹)
 ∙ ap upRight (succpredℤ _ ⁻¹)

below-implies-above-dM : (b : ℤ) → b above (downMid b)
below-implies-above-dM b
 = (0 , ℤ-elim (λ b → upLeft (downMid b) ≡ b)
          upLeft-downMid-pos upLeft-downMid-negsucc b)
 , (0 , ℤ-elim (λ b → b ≡ upRight (downMid b))
          upRight-downMid-pos upRight-downMid-negsucc b)

upLeft-downRight-pos : (b : ℕ) → upLeft (downRight (pos b)) ≡ pos b
upLeft-downRight-pos 0 = refl
upLeft-downRight-pos (succ b)
 = ap (upLeft ∘ succℤ) (ℤ-left-succ-pos (pos b) (succ (succ b)))
 ∙ upLeft-suc (downRight (pos b))
 ∙ ap succℤ (upLeft-downRight-pos b)

upLeft-downRight-negsucc : (b : ℕ) → upLeft (downRight (negsucc b)) ≡ negsucc b
upLeft-downRight-negsucc 0 = refl
upLeft-downRight-negsucc (succ b)
 = ap (upLeft ∘ succℤ ∘ succℤ) (ℤ-left-pred-negsucc (negsucc b) (succ b))
 ∙ ap (upLeft ∘ succℤ) (succpredℤ (predℤ (downLeft (negsucc b))))
 ∙ ap upLeft (succpredℤ (downLeft (negsucc b)))
 ∙ ap upLeft (predsuccℤ (downLeft (negsucc b))) ⁻¹
 ∙ ap (upLeft ∘ predℤ) (predsuccℤ (succℤ (downLeft (negsucc b))) ⁻¹)
 ∙ upLeft-pred (downRight (negsucc b))
 ∙ ap predℤ (upLeft-downRight-negsucc b)

upRight-downRight-pos : (b : ℕ) → succℤ (pos b) ≡ upRight (downRight (pos b))
upRight-downRight-pos 0 = refl
upRight-downRight-pos (succ b)
 = ap succℤ (upRight-downRight-pos b)
 ∙ upRight-suc (downRight (pos b)) ⁻¹
 ∙ ap (upRight ∘ succℤ ∘ succℤ ∘ succℤ) (ℤ-left-succ-pos (pos b) b ⁻¹)

upRight-downRight-negsucc : (b : ℕ) → succℤ (negsucc b) ≡ upRight (downRight (negsucc b))
upRight-downRight-negsucc 0 = refl
upRight-downRight-negsucc (succ b)
 = upRight-downLeft-negsucc b
 ∙ ap upRight (succpredℤ _ ⁻¹)
 ∙ ap (upRight ∘ succℤ) (ℤ-left-pred-negsucc (negsucc b) b ⁻¹)
 ∙ ap (upRight ∘ succℤ) (succpredℤ _ ⁻¹)

below-implies-above-dR : (b : ℤ) → b above (downRight b)
below-implies-above-dR b
 = (0 , ℤ-elim (λ b → upLeft (downRight b) ≡ b)
           upLeft-downRight-pos upLeft-downRight-negsucc b)
 , (1 , ℤ-elim (λ b → succℤ b ≡ upRight (downRight b))
           upRight-downRight-pos upRight-downRight-negsucc b)

below-implies-below' : (a b : ℤ) → a below b → a below' b
below-implies-below' a b ((0 , e) , _)
 = inl (e ⁻¹)
below-implies-below' a b ((1 , e) , _)
 = (inr ∘ inl) (e ⁻¹)
below-implies-below' a b ((2 , e) , _)
 = (inr ∘ inr) (e ⁻¹)
below-implies-below' a b ((succ (succ (succ _)) , _) , (0 , f))
 = (inr ∘ inr) f
below-implies-below' a b ((succ (succ (succ _)) , _) , (1 , f))
 = (inr ∘ inl) (succℤ-lc f)
below-implies-below' a b ((succ (succ (succ _)) , _) , (2 , f))
 = inl (succℤ-lc (succℤ-lc f))
below-implies-below' a b ((succ (succ (succ n)) , e) , (succ (succ (succ m)) , f))
 = 𝟘-elim (k≢2 k≡2)
 where   
   k : ℕ
   k = (succ (succ (succ (succ (succ (succ (n +ℕ m)))))))
   η : downLeft b +pos k ≡ downRight b
   η = (ap ((succℤ ^ 6) ∘ downLeft b +ℤ_) (pos-addition-equiv-to-ℕ n m ⁻¹)
     ∙ ap (succℤ ^ 6) (ℤ+-assoc (downLeft b) (pos n) (pos m) ⁻¹)
     ∙ ap (succℤ ^ 5) (ℤ-left-succ-pos (downLeft b +pos n) m ⁻¹)
     ∙ ap (succℤ ^ 4) (ℤ-left-succ-pos (succℤ (downLeft b +pos n)) m ⁻¹)
     ∙ ap (succℤ ^ 3) (ℤ-left-succ-pos ((succℤ ^ 2) (downLeft b +pos n)) m ⁻¹)
     ∙ ap ((succℤ ^ 3) ∘ (_+pos m)) e
     ∙ f)
   ζ : downLeft b +pos 2 ≡ downRight b
   ζ = refl
   k≡2 : k ≡ 2
   k≡2 = pos-lc k 2 (ℤ+-lc (pos k) (pos 2) (downLeft b) (η ∙ ζ ⁻¹))
   k≢2 : k ≢ 2
   k≢2 = λ ()

below'-implies-above : (a b : ℤ) → a below' b → b above a
below'-implies-above .(downLeft  b) b (inl refl)
 = below-implies-above-dL b
below'-implies-above .(downMid   b) b (inr (inl refl))
 = below-implies-above-dM b
below'-implies-above .(downRight b) b (inr (inr refl))
 = below-implies-above-dR b

below-implies-above : (a b : ℤ) → a below b → b above a
below-implies-above a b = (below'-implies-above a b) ∘ (below-implies-below' a b)

ℤ-pos-distrib : (a b : ℤ) (n m : ℕ) → ((a +ℤ b) +pos (n +ℕ m)) ≡ (a +pos n) +ℤ (b +pos m)
ℤ-pos-distrib a b n m
 = ℤ+-assoc a b (pos (n +ℕ m))
 ∙ ap (a +ℤ_)
     (ap (b +ℤ_) (pos-addition-equiv-to-ℕ n m ⁻¹)
     ∙ ℤ+-assoc b (pos n) (pos m) ⁻¹
     ∙ ap (_+pos m) (ℤ+-comm b (pos n))
     ∙ ℤ+-assoc (pos n) b (pos m))
 ∙ ℤ+-assoc a (pos n) (b +pos m) ⁻¹
 
downLeft-≤ : (a b : ℤ) → a ≤ℤ b → downLeft a ≤ℤ downLeft b
downLeft-≤ a .(a +ℤ pos n) (n , refl) = n +ℕ n , ℤ-pos-distrib a a n n

downRight-≤ : (a b : ℤ) → a ≤ℤ b → downRight a ≤ℤ downRight b
downRight-≤ a .(a +ℤ pos n) (n , refl)
 = n +ℕ n
 , (ℤ-left-succ-pos (succℤ (a +ℤ a)) (n +ℕ n)
 ∙ ap succℤ (ℤ-left-succ-pos (a +ℤ a) (n +ℕ n))
 ∙ ap (succℤ ∘ succℤ) (ℤ-pos-distrib a a n n))

factual : (x : ℕ) → Σ n ꞉ ℕ , ((succ x /2) +ℕ n ≡ succ (x /2))
factual zero = 1 , refl
factual (succ zero) = 0 , refl
factual (succ (succ x)) = k , (addition-succ (succ x /2) k ∙ ap succ γ)
 where
   k = pr₁ (factual x)
   γ = pr₂ (factual x)

factual2 : (x : ℕ) → Σ n ꞉ ℕ , ((negsucc (succ x /2) +pos n) ≡ negsucc (x /2))
factual2 zero = zero , refl
factual2 (succ zero) = 1 , refl
factual2 (succ (succ x))
 = k , (ζ ∙ ap predℤ γ)
 where
   k = pr₁ (factual2 x)
   γ = pr₂ (factual2 x)
   ζ : negsucc (succ (succ x /2)) +pos k ≡ predℤ (negsucc (succ x /2) +pos k)
   ζ = ℤ-left-pred-pos (negsucc (succ x /2)) k

upRight4 : (a : ℤ) → upRight a ≤ℤ upRight (succℤ a)
upRight4 (pos zero) = zero , refl
upRight4 (pos (succ x))
 = transport (upRight (pos (succ x)) ≤ℤ_)
     (upRight-suc (pos x) ⁻¹)
     ((pr₁ (factual x)) , (pos-addition-equiv-to-ℕ (succ x /2) (pr₁ (factual x))
                        ∙ ap pos (pr₂ (factual x))))
upRight4 (negsucc zero) = 1 , refl
upRight4 (negsucc (succ x)) = factual2 x

upRight' : (a : ℤ) (n : ℕ) → upRight a ≤ℤ upRight (a +pos n)
upRight' a 0 = 0 , refl
upRight' a 1 = upRight4 a
upRight' a (succ (succ n))
 = transport (upRight a ≤ℤ_) (upRight-suc (a +pos n) ⁻¹)
     (succ k , ap succℤ γ)
 where
   k = pr₁ (upRight' a n)
   γ = pr₂ (upRight' a n)

upRight-≤ : (a b : ℤ) → a ≤ℤ b → upRight a ≤ℤ upRight b
upRight-≤ a b (n , refl) = upRight' a n

upLeft-eo : (a : ℤ) → (e : even a) (o : odd (succℤ a))
          → upLeft' a (inl e) ≤ℤ upLeft' (succℤ a) (inr o)
upLeft-eo x e o = ℤ≤-trans (predℤ (upRight x)) (upRight x) (upRight (succℤ x))
                    (1 , succpredℤ (upRight x)) (upRight4 x)

factual4 : (x : ℕ) → odd (pos x) → pos (x /2) ≡ predℤ (pos (succ x /2))
factual4 1 o = refl
factual4 (succ (succ (succ x))) o = ap succℤ (factual4 (succ x) o)

factual5 : (x : ℕ) → odd (negsucc x) → negsucc (succ (x /2)) ≡ negsucc (succ (succ x /2))
factual5 0 o = refl
factual5 (succ (succ x)) o = ap predℤ (factual5 x o)

upLeft-oe : (a : ℤ) → (o : odd a) (e : even (succℤ a))
          → upLeft' a (inr o) ≤ℤ upLeft' (succℤ a) (inl e)
upLeft-oe (pos x) o e = 0 , factual4 x o
upLeft-oe (negsucc 0) o e = 0 , refl
upLeft-oe (negsucc (succ (succ x))) o e = 0 , factual5 x o

upLeft-succ* : (a : ℤ) → upLeft a ≤ℤ upLeft (succℤ a)
upLeft-succ* a with even-or-odd? a
... | (inl e) = transport (λ - → upLeft' a (inl e) ≤ℤ upLeft' (succℤ a) -)
                  (even-or-odd-is-prop (succℤ a)
                    (inr (succ-even-is-odd a e)) (even-or-odd? (succℤ a)))
                  (upLeft-eo a e (succ-even-is-odd a e))
... | (inr o) = transport (λ - → upLeft' a (inr o) ≤ℤ upLeft' (succℤ a) -)
                  (even-or-odd-is-prop (succℤ a)
                    (inl (succ-odd-is-even a o)) (even-or-odd? (succℤ a)))
                  (upLeft-oe a o (succ-odd-is-even a o))

upLeft'' : (a : ℤ) (n : ℕ) → upLeft a ≤ℤ upLeft (a +pos n)
upLeft'' a 0 = zero , refl
upLeft'' a (succ n)
 = transport (upLeft a ≤ℤ_) (ap upLeft (ℤ-left-succ-pos a n))
     (ℤ≤-trans (upLeft a) (upLeft (succℤ a)) (upLeft (succℤ a +pos n))
        (upLeft-succ* a) (upLeft'' (succℤ a) n))

upLeft-≤ : (a b : ℤ) → a ≤ℤ b → upLeft a ≤ℤ upLeft b
upLeft-≤ a b (n , refl) = upLeft'' a n

ci-lower-upper-<' : ((k , i) : ℤ × ℤ) → (x : CompactInterval (k , i))
                  → (δ : ℤ)
                  → (n : ℕ) → succℤ i +pos n ≡ δ
                  → rec k downLeft (succ n) ≤ℤ ⟨ ι x ⟩ δ ≤ℤ rec k downRight (succ n) 

ci-lower-upper-<' (k , i) ((x , γx) , refl) δ 0        refl
 = γx i
ci-lower-upper-<' (k , i) ((x , γx) , refl) δ (succ n) refl
 = ℤ≤-trans _ _ _ (downLeft-≤ _ _ IHl) (pr₁ (γx (succℤ i +ℤ pos n)))
 , ℤ≤-trans _ _ _ (pr₂ (γx (succℤ i +pos n))) (downRight-≤ _ _ IHr)
 where
   IH = ci-lower-upper-<' (x i , i) ((x , γx) , refl)
          (predℤ δ) n (predsuccℤ _ ⁻¹)
   IHl : rec (x i) downLeft (succ n) ≤ℤ x (succℤ i +ℤ pos n)
   IHl = transport (λ - → rec (x i) downLeft (succ n) ≤ℤ x -)
          (predsuccℤ _)
          (pr₁ IH)
   IHr : x (succℤ i +pos n) ≤ℤ rec (x i) downRight (succ n)
   IHr = transport (λ - → x - ≤ℤ rec (x i) downRight (succ n))
           (predsuccℤ _)
           (pr₂ IH)

ci-lower-upper-< : ((k , i) : ℤ × ℤ) → (x : CompactInterval (k , i))
                 → (δ : ℤ)
                 → ((n , _) : i <ℤ δ)
                 → rec k downLeft (succ n) ≤ℤ ⟨ ι x ⟩ δ ≤ℤ rec k downRight (succ n) 
ci-lower-upper-< (k , i) x δ (n , i<δ) = ci-lower-upper-<' (k , i) x δ n i<δ

ci-lower-upper->' : ((k , i) : ℤ × ℤ) → (x : CompactInterval (k , i))
                  → (δ : ℤ)
                  → (n : ℕ) → succℤ δ +pos n ≡ i
                  → rec k   upLeft (succ n) ≤ℤ ⟨ ι x ⟩ δ ≤ℤ rec k   upRight (succ n) 
ci-lower-upper->' (k , i) ((x , γx) , refl) δ 0        refl
 = below-implies-above _ _ (γx δ)
ci-lower-upper->' (k , i) ((x , γx) , refl) δ (succ n) refl
 = ℤ≤-trans _ _ _ (upLeft-≤ _ _ IHl) (pr₁ (below-implies-above _ _ (γx δ)))
 , ℤ≤-trans _ _ _ (pr₂ (below-implies-above _ _ (γx δ))) (upRight-≤ _ _ IHr)
 where
   δx : x (predℤ δ) above x (succℤ (predℤ δ))
   δx = below-implies-above (x (succℤ (predℤ δ))) (x (predℤ δ)) (γx (predℤ δ))
   IH = ci-lower-upper->' (x i , i) ((x , γx) , refl)
          (succℤ δ) n (ℤ-left-succ-pos (succℤ δ) n)
   IHl : rec (x i) upLeft (succ n) ≤ℤ x (succℤ δ)
   IHl = pr₁ IH
   IHr : x (succℤ δ) ≤ℤ rec (x i) upRight (succ n)
   IHr = pr₂ IH

ci-lower-upper-> : ((k , i) : ℤ × ℤ) → (x : CompactInterval (k , i))
                 → (δ : ℤ)
                 → ((n , _) : δ <ℤ i)
                 → rec k   upLeft (succ n) ≤ℤ ⟨ ι x ⟩ δ ≤ℤ rec k   upRight (succ n) 
ci-lower-upper-> (k , i) x δ (n , δ<i) = ci-lower-upper->' (k , i) x δ n δ<i

ci-lower-upper : ((k , i) : ℤ × ℤ) → (x : CompactInterval (k , i))
               → (δ : ℤ)
               → lower (k , i) δ ≤ℤ ⟨ ι x ⟩ δ ≤ℤ upper (k , i) δ 
ci-lower-upper (k , i) ((x , γx) , refl) δ with ℤ-trichotomous i δ
... | inl      i<δ   = ci-lower-upper-< (k , i) ((x , γx) , refl) δ i<δ
... | inr (inl refl) = (0 , refl) , (0 , refl)
... | inr (inr i>δ)  = ci-lower-upper-> (k , i) ((x , γx) , refl) δ i>δ

ci-low-up : ((k , i) : ℤ × ℤ) (δ : ℤ)
          → lower (k , i) δ ≤ℤ upper (k , i) δ
ci-low-up   (k , i) δ = ℤ≤-trans _ _ _ (pr₁ γ) (pr₂ γ)
 where
   γ = ci-lower-upper (k , i) (build-via-ci (k , i)) δ

ci-lu-left : ((k , i) : ℤ × ℤ) (δ : ℤ)
           → lower (k , i) δ ≤ℤ lower (k , i) δ ≤ℤ upper (k , i) δ
ci-lu-left  (k , i) δ = (ℤ≤-refl _) , (ci-low-up (k , i) δ)

ci-lu-right : ((k , i) : ℤ × ℤ) (δ : ℤ)
           → lower (k , i) δ ≤ℤ upper (k , i) δ ≤ℤ upper (k , i) δ
ci-lu-right (k , i) δ = (ci-low-up (k , i) δ) , (ℤ≤-refl _)
```

TODO

```
replace'' : ((k , i) : ℤ × ℤ) (c δ : ℤ)
         →  lower (k , i)        δ  ≤ℤ c         ≤ℤ upper (k , i)        δ
         → (lower (k , i) (predℤ δ) ≤ℤ upLeft  c ≤ℤ upper (k , i) (predℤ δ))
         + (lower (k , i) (predℤ δ) ≤ℤ upRight c ≤ℤ upper (k , i) (predℤ δ))
replace'' (k , i) c δ l≤c≤u = {!!}

replace' : ((k , i) : ℤ × ℤ)
         → (c δ : ℤ)
         → lower (k , i)        δ  ≤ℤ c  ≤ℤ upper (k , i)        δ
         → Σ c' ꞉ ℤ
         , lower (k , i) (predℤ δ) ≤ℤ c' ≤ℤ upper (k , i) (predℤ δ)
         × c below c'
replace' (k , i) c δ l≤c≤u with replace'' (k , i) c δ l≤c≤u
... | inl x = upLeft  c , x , {!!} -- upLeft-below 
... | inr x = upRight c , x , {!!} -- upRight-below

replace : ((k , i) (c , δ) : ℤ × ℤ)
        → lower (k , i) δ ≤ℤ c ≤ℤ upper (k , i) δ
        → Σ ((x , _) , _) ꞉ CompactInterval (k , i)
        , x δ ≡ c
replace (k , i) (c , δ) l≤c≤u
 = {!!}
```

## Signed-digits are isomorphic to Ternary Boehm reals

Recall that we previously represented numbers in the closed interval
[-1,1] using signed-digit functions of type ℕ → 𝟛.

⦉_⦊ : (ℕ → 𝟛) → ℝ
⦉ α ⦊ = Σᵢ α i * 2^{-i-1}

This interval is represented by the Boehm "brick" (-1 , -1) : ℕ × ℕ.

```
[−1,1]-code : ℤ × ℤ
[−1,1]-code = (negsucc 0 , negsucc 0)
```

The location structure of the signed-digit approach is actually
isomorphic to the ternary Boehm approach.

For example, the signed digit function
 α ≔     { −1            ,  O           , +1             ...} : ℕ → 𝟛
follows the same location structure as
 x ≔ {-1 , downLeft x(0) , downMid x(1) , downRight x(2) ...} : ℕ → ℤ

```
𝟛-to-down : 𝟛 → (ℤ → ℤ)
𝟛-to-down −1 = downLeft
𝟛-to-down  O = downMid
𝟛-to-down +1 = downRight

signed-to-boehm' : (ℕ → 𝟛) → (ℕ → ℤ)
signed-to-boehm' α 0 = negsucc 0
signed-to-boehm' α (succ n) = 𝟛-to-down (α n) (signed-to-boehm' α n)
```

signed-to-boehm'-below
  : (α : ℕ → 𝟛) → (n : ℕ)
  → (signed-to-boehm' α (succ n)) below (signed-to-boehm' α n)
signed-to-boehm'-below α n = {!!} -- Easy

signed-to-boehm : (ℕ → 𝟛) → CompactInterval [−1,1]-code
signed-to-boehm α
 = build-ci (signed-to-boehm' α , signed-to-boehm'-below α)

Therefore, it should be the case that, for all x : ℕ → 𝟛
⦉ x ⦊ = ⟦ signed-to-boehm x ⟧.

Recall that we use an interval object specification of the real
numbers 𝕀.

We already defined the following realisability map,

q : 𝟛 → 𝕀
q −1 = −1
q  O =  O
q +1 = +1

𝕢 : (ℕ → 𝟛) → 𝕀
𝕢 = M ∘ map ⟨_⟩

We also want to define the following realisability map,

𝕣 : CompactInterval [−1,1]-code → 𝕀

such that for all x : ℕ → 𝟛, 𝕢 x = 𝕣 (signed-to-boehm x).

We will do this by defining,

boehm-to-signed : CompactInterval [−1,1]-code → (ℕ → 𝟛)
boehm-to-signed {!!}

such that

boehm-signed-iso₁ : boehm-to-signed ∘ signed-to-boehm ≃ id
boehm-signed-iso₁ = {!!}

boehm-signed-iso₂ : signed-to-boehm ∘ boehm-to-signed ≃ id
boehm-signed-iso₂ = {!!}

Then, by setting

𝕣 = 𝕢 ∘ boehm-to-signed,

our proof follows: we immediately get that for all x : ℕ → 𝟛,

𝕢 x = (𝕢 ∘ boehm-to-signed) (signed-to-boehm x),

by boehm-signed-iso₁.

----

Ask Andrew:
 * Implement countable/iterated midpoint on Dedekind reals

-------------------------------------------------------------------

## The key difference

The key difference between the signed digit approach and the Boehm
approach is that,
 * With signed digit, the information kept in x(n) *depends on*
                      the information in all x(i) such that i < n,
 * With Boehm codes,  the information kept in x(n) *includes*
                      the information in all x(i) such that i < n.

-------------------------------------------------------------------

## Closeness function on 𝕂

For every discrete-sequence type ℕ → X (where X is discrete), we have
a canonical closeness function c : (ℕ → X) × (ℕ → X) → ℕ∞.

Recall that for x,y : ℕ → X and any δ : ℕ,

c (x , y) ≼ ι δ ⇔ (x ≈ y) δ,

where c(x , y) : ℕ∞ is the value of the discrete-sequence closeness
function for x and y.

```
_≈'_ : {X : 𝓤 ̇ } → (ℕ → X) → (ℕ → X) → ℕ → 𝓤 ̇
(α ≈' β) n = (i : ℕ) → i <ℕ n → α n ≡ β n
```

From the canonical closeness function on (ℕ → ℤ), we can define one
on 𝕂:

c : 𝕂 × 𝕂 → ℕ∞
c ((α , _) , (β , _)) = c (α ∘ pos , β ∘ pos)

Note that we only take into account positive precision-levels of
object x : 𝕂; but, as we already said, for our purposes of encoding
real numbers, the information kept in any ⟨ x ⟩ (pos n₁) : ℤ includes
the information kept in any ⟨ x ⟩ (negsucc n₂) : ℤ.

This closeness function, like that on signed-digits, gives the
closeness of *encodings* of real numbers; not the real numbers
themselves. If we wish to determine the closeness of the numbers
themselves, we can instead use the following pseudo-closeness
function (BUT MAYBE NOT)

pc : 𝕂 × 𝕂 → ℕ∞ 
pc ((α , _) , (β , _))
 = λ n → dec-to-𝟚 (abs (α (pos n) −ℤ β (pos n)) ≤ℤ 2)

## Predicates we wish to search

In our general regression framework, we search uniformly continuous
decidable predicates on types equipped with closeness functions.

(Recall that there is no non-trivial uniformly continuous decidable
predicate on the real numbers ℝ.)

When defining uniformly continuous predicates on signed-digits,
we utilised the discrete-sequence closeness function.

```
uc-d-predicates-on-seqs : {𝓦 𝓤 : Universe} → {X : 𝓤 ̇ } → (δ : ℕ) → (𝓦 ⁺) ⊔ 𝓤 ̇
uc-d-predicates-on-seqs {𝓦} {𝓤} {X} δ
 = decidable-predicate-informed-by {𝓦}
     (sequence-relation-≈' (λ _ → X) δ)
```

We call the δ : ℕ of such a predicate its 'modulus of continuity'.

So for uniformly continuous decidable predicates p on signed-digit
encodings x,y : ℕ → 𝟛, with modulus of continuity δ : ℕ, it is enough
to know that (x ≈ y) δ to know that p(x) is logically equivalent
to p(y).

(Reword ↓)
But! With Boehm codes 𝕂, all the information is kept in the most recent
code. So an "equivalent" predicate should only need to satisfy the
following.

```
open equivalence-relation

ℤ→ℤ-equivalence-relation : (δ : ℤ) → equivalence-relation {𝓤₀} (ℤ → ℤ)
_≣_     (ℤ→ℤ-equivalence-relation δ) x y   = x δ ≡ y δ
≣-refl  (ℤ→ℤ-equivalence-relation δ) x     = refl
≣-sym   (ℤ→ℤ-equivalence-relation δ) x y   = _⁻¹
≣-trans (ℤ→ℤ-equivalence-relation δ) x y z = _∙_

pr₁-equivalence-relation : {X : 𝓤 ̇ } {Y : X → 𝓤' ̇ }
                         → equivalence-relation {𝓥} X
                         → equivalence-relation {𝓥} (Σ Y)
_≣_     (pr₁-equivalence-relation A) x y   = pr₁ x ≣⟨ A ⟩ pr₁ y
≣-refl  (pr₁-equivalence-relation A) x     = ≣-refl  A (pr₁ x)
≣-sym   (pr₁-equivalence-relation A) x y   = ≣-sym   A (pr₁ x) (pr₁ y)
≣-trans (pr₁-equivalence-relation A) x y z = ≣-trans A (pr₁ x) (pr₁ y) (pr₁ z)

𝕂-equivalence-relation : (δ : ℤ) → equivalence-relation {𝓤₀} 𝕂
𝕂-equivalence-relation δ = pr₁-equivalence-relation (ℤ→ℤ-equivalence-relation δ)

𝕂c-equivalence-relation : ((k , i) : ℤ × ℤ) (δ : ℤ)
                        → equivalence-relation {𝓤₀} (CompactInterval (k , i))
𝕂c-equivalence-relation (k , i) δ = pr₁-equivalence-relation (𝕂-equivalence-relation δ)

special-predicate-on-𝕂 : {𝓦 : Universe} → (δ : ℤ) → (𝓦 ⁺) ̇ 
special-predicate-on-𝕂 {𝓦} δ
 = decidable-predicate-informed-by {𝓦} (𝕂-equivalence-relation δ)
```

Relationships:
 * c (α , β) ≼ δ                 → pc (α , β) ≼ δ
 * c (α , β) ≼ (succ δ)          → ⟨ α ⟩ (pos δ) ≡ ⟨ β ⟩ (pos δ)
 * ⟨ α ⟩ (pos δ) ≡ ⟨ β ⟩ (pos δ) → pc (α , β) ≼ δ ?

## Special predicates on K relate to predicates on ℤ × ℤ

```
special-predicate-on-I : {𝓦 : Universe} → (δ : ℤ) → (𝓦 ⁺) ̇
special-predicate-on-I {𝓦} δ
 = decidable-predicate-informed-by {𝓦} (Identity ℤ)

open equiv-of-setoids

SE' : (δ : ℤ)
    → equiv-of-setoids
        (𝕂-equivalence-relation δ)
        (Identity ℤ)
f (SE' δ) = (λ α → α δ) ∘ ⟨_⟩
g (SE' δ) = build-via ∘ (_, δ)
trans-A (SE' δ) α = {!!}
trans-B (SE' δ) z = {!!}
lift-AB (SE' δ) α β = id
lift-BA (SE' δ) z z refl = refl

special-predicate-𝕂-to-I
 : {𝓦 : Universe} → (δ : ℤ)
 →  (pdiϕ𝕂 : special-predicate-on-𝕂 {𝓦} δ)
 → Σ pdiϕI ꞉ special-predicate-on-I {𝓦} δ
 , ((x : 𝕂)
       → p⟨ 𝕂-equivalence-relation _    - pdiϕ𝕂 ⟩ x
       → p⟨ Identity _                   - pdiϕI ⟩ (f (SE' δ) x))
special-predicate-𝕂-to-I δ
 = convert-predicates _ _ (SE' δ)

special-predicate-I-to-𝕂
 : {𝓦 : Universe} → (δ : ℤ)
 →  (pdiϕI : special-predicate-on-I {𝓦} δ)
 → Σ pdiϕ𝕂 ꞉ special-predicate-on-𝕂 {𝓦} δ
 , ((x : ℤ)
       → p⟨ Identity _                   - pdiϕI ⟩ x
       → p⟨ 𝕂-equivalence-relation _     - pdiϕ𝕂 ⟩ (g (SE' δ) x))
special-predicate-I-to-𝕂 δ
 = convert-predicates _ _ (equiv-of-setoids-sym _ _ (SE' δ))
```

But these are not searchable!

## Special predicates on CompactIntervals relate to searchable predicates on I

```

special-predicate-on-𝕂c : {𝓦 : Universe} → ((k , i) : ℤ × ℤ) → (δ : ℤ) → (𝓦 ⁺) ̇ 
special-predicate-on-𝕂c {𝓦} (k , i) δ
 = decidable-predicate-informed-by {𝓦} (𝕂c-equivalence-relation (k , i) δ)

special-predicate-on-Ic : {𝓦 : Universe} → (δ l u : ℤ) → (𝓦 ⁺) ̇ 
special-predicate-on-Ic {𝓦} δ l u
 = decidable-predicate-informed-by {𝓦} (Identity (ℤ[ l , u ]))
```

These are searchable.

```
{-
η : (n : ℤ) → (x : 𝕂) → CompactInterval (⟨ x ⟩ n , n)
η n = _, refl
-}
```

The Ic predicates are searchable, and are logically equivalent to the 𝕂c
predicates.

```
SE : ((k , i) : ℤ × ℤ) (δ : ℤ)
   → equiv-of-setoids
       (𝕂c-equivalence-relation (k , i) δ)
       (Identity ℤ[ (lower (k , i) δ) , (upper (k , i) δ) ])
f (SE (k , i) δ) α           = ⟨ ι α ⟩ δ , ci-lower-upper (k , i) α δ
g (SE (k , i) δ) (z , l≤z≤u) = pr₁ (replace (k , i) (z , δ) l≤z≤u)
trans-A (SE (k , i) δ) α
 = pr₂ (replace (k , i) (⟨ ι α ⟩ δ , δ) (ci-lower-upper (k , i) α δ)) ⁻¹
trans-B (SE (k , i) δ) (z , l≤z≤u)
 = to-subtype-≡ ≤ℤ²-is-prop (pr₂ (replace (k , i) (z , δ) l≤z≤u) ⁻¹)
lift-AB (SE (k , i) δ) α β
 = to-subtype-≡ ≤ℤ²-is-prop 
lift-BA (SE (k , i) δ) (z , l≤z≤u) (z , l≤z≤u) refl
 = refl

special-predicate-𝕂c-to-Ic
 : {𝓦 : Universe} → ((k , i) : ℤ × ℤ) → (δ : ℤ)
 →  (pdiϕ𝕂c : special-predicate-on-𝕂c {𝓦} (k , i) δ)
 → Σ pdiϕIc ꞉ special-predicate-on-Ic {𝓦} δ (lower (k , i) δ) (upper (k , i) δ)
 , ((x : CompactInterval (k , i))
       → p⟨ 𝕂c-equivalence-relation _ _ - pdiϕ𝕂c ⟩ x
       → p⟨ Identity _                   - pdiϕIc ⟩ (f (SE (k , i) δ) x))
special-predicate-𝕂c-to-Ic (k , i) δ
 = convert-predicates _ _ (SE (k , i) δ)

special-predicate-Ic-to-𝕂c
 : {𝓦 : Universe} → ((k , i) : ℤ × ℤ) → (δ : ℤ)
 →  (pdiϕIc : special-predicate-on-Ic {𝓦} δ (lower (k , i) δ) (upper (k , i) δ))
 → Σ pdiϕ𝕂c ꞉ special-predicate-on-𝕂c {𝓦} (k , i) δ
 , ((x : ℤ[ _ , _ ])
       → p⟨ Identity _                   - pdiϕIc ⟩ x
       → p⟨ 𝕂c-equivalence-relation _ _ - pdiϕ𝕂c ⟩ (g (SE (k , i) δ) x))
special-predicate-Ic-to-𝕂c (k , i) δ
 = convert-predicates _ _ (equiv-of-setoids-sym _ _ (SE (k , i) δ))
```

Therefore, 𝕂c predicates are searchable in two ways: directly, or
via the setoid equivalence.

```

𝕂c-searchable-directly : {𝓦 : Universe} → ((k , i) : ℤ × ℤ) → (δ : ℤ)
                       → Searchable {𝓦} (𝕂c-equivalence-relation (k , i) δ)
𝕂c-searchable-directly = {!!}

𝕂c-searchable-equiv : {𝓦 : Universe} → ((k , i) : ℤ × ℤ) → (δ : ℤ)
                    → Searchable {𝓦} (𝕂c-equivalence-relation (k , i) δ)
𝕂c-searchable-equiv (k , i) δ
 = convert-searchable _ _ (SE (k , i) δ) (ℤ[ l , u ]-searchable (pr₁ l≤u) (pr₂ l≤u))
 where
   l = lower (k , i) δ
   u = upper (k , i) δ
   l≤u = ci-low-up (k , i) δ

```


## Predicates to test

## Fuel

```
```


---------------------------------------------------------------------

## Predicates on interval encodings

A uc-d predicate on an interval encoding is as follows:

uc-d-predicate-on-I : (p : ℤ × ℤ → 𝓤 ̇ ) → 𝓤 ̇
uc-d-predicate-on-I p
 = ((k , i) : ℤ × ℤ) → decidable (p (k , i)))
 × (((k , i) (c , j) : ℤ) → (k , i) ≡ (c , j) → p (k , i) ⇔ p (c , j))

Of course, because ℤ × ℤ is discrete, such predicates are always
uniformly continuous -- the second condition always holds. Therefore,
we need only consider decidable predicates

d-predicate-on-I : 𝓤 ⁺
d-predicate-on-I p i l u
 = Σ p : (ℤ × ℤ → 𝓤 ̇ ) , Σ (i , l , u : ℤ) ̇
 , ((k : ℤ) → l ≤ℤ k ≤ℤ u → decidable (p (k , i)))

"Beneath" each special predicate on 𝕂, is a decidable predicate on ℤ.

construct-sp : d-predicate-on-I
             → Σ p* : (𝕂 → 𝓤 ̇) , special-predicate p 
construct-sp (p , i , l , u , d)
 = (λ (α , _) → p (α(i) , i))
 , (λ (α , _) → d (α(i) , i))
 , (i , λ (α , _) (β , _) αi≡βi →
      (transport (λ - → p (- , i)) (αi≡βi ⁻¹))
    , (transport (λ - → p (- , i))  αi≡βi    ))

destruct-sp : (p* : 𝕂 → 𝓤 ̇ ) → special-predicate p*
            → Σ p : (ℤ × ℤ) → 𝓤 ̇ , 

## Subsets of ℤ are searchable
