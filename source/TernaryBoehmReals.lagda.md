```agda
{-# OPTIONS --without-K --exact-split #-}

open import TernaryBoehmRealsPrelude
open import UF-Equiv

module TernaryBoehmReals where

```

## Idea and Illustration

We encode real numbers using the data type for ternary Boehm reals 𝕂.

Each 𝕂 is a function x ꞉ ℤ → ℤ with some restrictions on it, so that we only
have our encodings of real numbers inside 𝕂, and not any function of type ℤ → ℤ.

The function x : ℤ → ℤ takes a "precision-level" n : ℤ and gives back an
encoding x(n) : ℤ of a real interval.

The idea is that each precision-level n : ℤ represents a "layer" in the
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

Therefore, an encoding of a real number is a sequence of encodings of real
intervals -- the restriction we add is that each brick x(n) is "below" the brick
-- x(n+1); meaning ⟪ x(n+1) , n+1 ⟫ ⊂ ⟪ x(n) , n ⟫.

Note that there are precisely three brick below each brick.

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
upRight upLeft : ℤ → ℤ
upRight x = sign x (num x /2)
upLeft  x with even-or-odd? x
...     | (inl e) = predℤ (upRight x)
...     | (inr o) =        upRight x
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

build-via : ℤ × ℤ → 𝕂
build-via (k , i) = λ n → if   n <ℤ i
                          then rec upRight (i - n) k
                          if   n ≡  i
                          then k
                          else rec downLeft (n - i) k
                  , λ n → if   n ≤ℤ i
                          then rec upRight-is-below (i - n) i
                          else rec downLeft-is-above (n - i) i

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

build-ci : (Σ x ꞉ (ℕ → ℤ) , (n : ℕ) → (x (succ n)) below (x n))
         → (i : ℤ) → CompactInterval (x(0) , i)
build-ci x = build x i , {!!}

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
_≈_ : {X : 𝓤 ̇ } → (ℕ → X) → (ℕ → X) → ℕ → 𝓤 ̇
(α ≈ β) n = (i : ℕ) → i <ℕ n → α n ≡ β n
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
uc-d-predicate-on-seqs : {X : 𝓤 ̇ } → (p : (ℕ → X) → 𝓥 ̇ ) → (𝓤 ⊔ 𝓥) ̇ 
uc-d-predicate-on-seqs {𝓤} {𝓥} {X} p
 = ((α : ℕ → X) → decidable (p α))
 × (Σ δ ꞉ ℕ , ((α β : ℕ → X) → (α ≈ β) δ → p α ⇔ p β))
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
special-predicate-on-𝕂 : (δ : ℤ) → 𝓤 ⁺ ̇
special-predicate-on-𝕂 {𝓤} δ
 = Σ p ꞉ (𝕂 → 𝓤 ̇ )
 , ((x : 𝕂) → decidable (p x))
 × ((α β : 𝕂) → ⟨ α ⟩ δ ≡ ⟨ β ⟩ δ → p α ⇔ p β)
```

Relationships:
 * c (α , β) ≼ δ                 → pc (α , β) ≼ δ
 * c (α , β) ≼ (succ δ)          → ⟨ α ⟩ (pos δ) ≡ ⟨ β ⟩ (pos δ)
 * ⟨ α ⟩ (pos δ) ≡ ⟨ β ⟩ (pos δ) → pc (α , β) ≼ δ ?

## Special predicates on K relate to predicates on I

```
special-predicate-on-I : (δ : ℤ) → 𝓤 ⁺ ̇
special-predicate-on-I {𝓤} δ
 = Σ p ꞉ (ℤ × ℤ → 𝓤 ̇ )
 , ((k : ℤ) → decidable (p (k , δ)))

special-predicate-I-to-𝕂 : {𝓤 : Universe} → (δ : ℤ)
                         → special-predicate-on-I {𝓤} δ
                         → special-predicate-on-𝕂 {𝓤} δ
special-predicate-I-to-𝕂 {𝓤} δ (p , d) = p* , d* , ϕ
 where
   p* : 𝕂 → 𝓤 ̇
   p* x = p (⟨ x ⟩ δ , δ) 
   d* : (x : 𝕂) → decidable (p* x)
   d* x = d (⟨ x ⟩ δ) 
   ϕ : (α β : 𝕂) → ⟨ α ⟩ δ ≡ ⟨ β ⟩ δ
                 → p (⟨ α ⟩ δ , δ) ⇔ p (⟨ β ⟩ δ , δ)
   ϕ α β αδ≡βδ = transport (p ∘ (_, δ))  αδ≡βδ
               , transport (p ∘ (_, δ)) (αδ≡βδ ⁻¹)
```

special-predicate-𝕂-to-I : (δ : ℕ)
                         → special-predicate-on-𝕂 δ → special-predicate-on-I δ
special-predicate-𝕂-to-I δ (p* , d* , ϕ) = p , d
 where
   p : ℤ × ℤ → 𝓤 ̇ 
   p (k , i) = p* (build-via (k , i))
   d : (k : ℤ) → decidable (p* (build-via (k , δ))) 
   d  k      = d* (build-via (k , δ))

But these are not searchable!

## Special predicates on CompactIntervals relate to searchable predicates on I

```
special-predicate-on-𝕂c : ((k , i) : ℤ × ℤ) (δ : ℤ) → 𝓤 ⁺ ̇ 
special-predicate-on-𝕂c {𝓤} (k , i) δ
 = Σ p ꞉ (CompactInterval (k , i) → 𝓤 ̇ )
 , ((x : CompactInterval (k , i)) → decidable (p x))
 × ((α β : CompactInterval (k , i))
   → ⟨ ι α ⟩ δ ≡ ⟨ ι β ⟩ δ → p α ⇔ p β)

special-predicate-on-Ic : (δ l u : ℤ) → 𝓤 ⁺ ̇ 
special-predicate-on-Ic {𝓤} δ l u
 = Σ p ꞉ (ℤ × ℤ → 𝓤 ̇ )
 , ((k : ℤ) → l ≤ℤ k ≤ℤ u → decidable (p (k , δ)))

```

These are searchable.

```
η : (n : ℤ) → (x : 𝕂) → CompactInterval (⟨ x ⟩ n , n)
η n = _, refl

-- Not sure about this:
special-predicate-𝕂c-to-𝕂
 : {𝓤 : Universe} (δ : ℤ)
 → (((k , i) : ℤ × ℤ) → special-predicate-on-𝕂c {𝓤} (k , i) δ)
 → special-predicate-on-𝕂 {𝓤} δ
special-predicate-𝕂c-to-𝕂 δ ps
 = (λ α → pr₁      (ps (⟨ α ⟩ δ , δ)) (η δ α))
 , (λ α → pr₁ (pr₂ (ps (⟨ α ⟩ δ , δ))) (η δ α))
 , (λ α β αδ≡βδ → (λ psαα → {!!}) , {!!})
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
lower (k , i) δ = rec-upLeft/downLeft   k (i −ℤ δ)
upper (k , i) δ = rec-upRight/downRight k (i −ℤ δ)

ci-lower-upper : ((k , i) : ℤ × ℤ) → (x : CompactInterval (k , i))
               → (δ : ℤ)
               → lower (k , i) δ ≤ℤ ⟨ ι x ⟩ δ ≤ℤ upper (k , i) δ 
ci-lower-upper (k , i) x δ with (i −ℤ δ)
... | pos n = {!!}
... | negsucc n = {!!}

ci-low-up : ((k , i) : ℤ × ℤ) (δ : ℤ)
          → lower (k , i) δ ≤ℤ upper (k , i) δ
ci-low-up   (k , i) δ = {!!}

ci-lu-left : ((k , i) : ℤ × ℤ) (δ : ℤ)
           → lower (k , i) δ ≤ℤ lower (k , i) δ ≤ℤ upper (k , i) δ
ci-lu-left  (k , i) δ = (ℤ≤-refl _) , (ci-low-up (k , i) δ)

ci-lu-right : ((k , i) : ℤ × ℤ) (δ : ℤ)
           → lower (k , i) δ ≤ℤ upper (k , i) δ ≤ℤ upper (k , i) δ
ci-lu-right (k , i) δ = (ci-low-up (k , i) δ) , (ℤ≤-refl _)



```

TODO

```
_∈_ : ℤ × ℤ → ℤ × ℤ → 𝓤₀ ̇ 
(c , j) ∈ (k , i) = lower (k , i) j ≤ℤ c ≤ℤ upper (k , i) j

ℤ[_,_] : ℤ → ℤ → 𝓤₀ ̇
ℤ[ l , u ] = Σ c ꞉ ℤ , l ≤ℤ c ≤ℤ u

ℤ* : ℤ × ℤ → 𝓤₀ ̇
ℤ* (k , i) = Σ (_∈ (k , i))

ℤ*≡ : {(k , i) : ℤ × ℤ} → {(a , ζ₁) (b , ζ₂) : ℤ* (k , i)}
    → a ≡ b
    → (a , ζ₁) ≡ (b , ζ₂)
ℤ*≡ = {!!}
```

The Ic predicates are searchable, and are logically equivalent to the 𝕂c
predicates.

```
special-predicate-Ic' : {𝓤 : Universe} → (l u : ℤ) → 𝓤 ⁺ ̇
special-predicate-Ic' {𝓤} l u
 = Σ p ꞉ (ℤ[ l , u ] → 𝓤 ̇ )
 , ((x : ℤ[ l , u ]) → decidable (p x))

special-predicate-Ic : {𝓤 : Universe} → ((k , i) : ℤ × ℤ) (δ : ℤ) → 𝓤 ⁺ ̇
special-predicate-Ic {𝓤} (k , i) δ
 = Σ p ꞉ (ℤ* (k , i) → 𝓤 ̇ )
 , ((x : ℤ* (k , i)) → decidable (p x))

special-predicate-𝕂c-Ic : {𝓤 : Universe} ((k , i) : ℤ × ℤ) (δ : ℤ)
                        → special-predicate-on-𝕂c {𝓤} (k , i) δ 
                        → special-predicate-Ic    {𝓤} (k , i) δ
special-predicate-𝕂c-Ic (k , i) δ (p , d , ϕ)
 = (λ ((c , j) , ζ) → p {!!}) -- build-via )
 , (λ ((c , j) , ζ) → d {!!}) -- build-via )

special-predicate-Ic-𝕂c : {𝓤 : Universe} ((k , i) : ℤ × ℤ) (δ : ℤ)
                        → special-predicate-Ic    {𝓤} (k , i) δ 
                        → special-predicate-on-𝕂c {𝓤} (k , i) δ
special-predicate-Ic-𝕂c (k , i) δ (p , d)
 = (λ α → p ((⟨ ι α ⟩ δ , δ) , ci-lower-upper (k , i) α δ))
 , (λ α → d ((⟨ ι α ⟩ δ , δ) , ci-lower-upper (k , i) α δ))
 , λ α β αδ≡βδ
 → (transport p (ℤ*≡ (ap (_, δ)  αδ≡βδ    )))
 , (transport p (ℤ*≡ (ap (_, δ) (αδ≡βδ ⁻¹))))

```

```
≤ℤ-antisym : ∀ x y → x ≤ℤ y ≤ℤ x → x ≡ y
≤ℤ-antisym x y (x≤y , y≤x) with ℤ≤-split x y x≤y | ℤ≤-split y x y≤x
... | inl (n , γ) | inl (m , δ)
 = 𝟘-elim (ℤ-equal-not-less-than x (ℤ<-trans x y x (n , γ) (m , δ)))
... | inl  _  | inr y≡x = y≡x ⁻¹
... | inr x≡y | _       = x≡y

≤ℤ-back : ∀ x y → x <ℤ y → x ≤ℤ predℤ y
≤ℤ-back x .(succℤ x +ℤ pos n) (n , refl)
 = ℤ≤-trans x (x +pos n) (predℤ (succℤ x +pos n))
     (n , refl)
     (transport ((x +pos n) ≤ℤ_)
       (predsuccℤ (x +pos n) ⁻¹
       ∙ ap predℤ (ℤ-left-succ x (pos n) ⁻¹))
       (ℤ≤-refl (x +pos n)))

Ic-predicates-are-searchable'
 : {𝓤 : Universe} (δ l u : ℤ) → (n : ℕ) → l +pos n ≡ u
 → ((p , _) : special-predicate-on-Ic {𝓤} δ l u)
 →  Σ k ꞉ ℤ , ((Σ k₀ ꞉ ℤ , l ≤ℤ k₀ ≤ℤ u × p (k₀ , δ)) → p (k , δ))
Ic-predicates-are-searchable' δ .u u 0 refl (p , d)
 = u , γ
 where
   γ : Σ k₀ ꞉ ℤ , u ≤ℤ k₀ ≤ℤ u × p (k₀ , δ) → p (u , δ)
   γ (u₀ , e , pu₀) = transport (p ∘ (_, δ)) (u≡u₀ ⁻¹) pu₀
    where
      u≡u₀ : u ≡ u₀
      u≡u₀ = ≤ℤ-antisym u u₀ e 
Ic-predicates-are-searchable' δ l u (succ n) l+n≡u (p , d)
 = Cases (d u ((succ n , l+n≡u) , ℤ≤-refl u))
     (λ  pu → u , λ _                    → pu)
     (λ ¬pu → k , λ (k₀ , (l≤k₀ , k₀≤u) , pk₀) →
       Cases (ℤ≤-split k₀ u k₀≤u)
         (λ k₀<u → γ (k₀ , (l≤k₀
                         , transport (k₀ ≤ℤ_)
                             (succℤ-lc (succpredℤ u ∙ l+n≡u ⁻¹))
                             (≤ℤ-back k₀ u k₀<u))
                         , pk₀))
         (λ k₀≡u → 𝟘-elim (¬pu (transport p (ap (_, δ) k₀≡u) pk₀))))
 where
  IH : Σ k ꞉ ℤ , ((Σ k₀ ꞉ ℤ , l ≤ℤ k₀ ≤ℤ (l +pos n) × p (k₀ , δ)) → p (k , δ))
  IH = Ic-predicates-are-searchable' δ l (l +pos n) n refl
        (p , λ k (l≤k , (i , k+i≡pu))
           → d k (l≤k , succ i , (ap succℤ k+i≡pu ∙ l+n≡u)))
  k = pr₁ IH
  γ = pr₂ IH

Ic-predicates-are-searchable
 : {𝓤 : Universe} (δ l u : ℤ)
 → ((p , _) : special-predicate-on-Ic {𝓤} δ l u)
 → Σ k ꞉ ℤ , ((Σ k₀ ꞉ ℤ , l ≤ℤ k₀ ≤ℤ u × p (k₀ , δ)) → p (k , δ))
Ic-predicates-are-searchable δ l u (p , d)
 = Cases (ℤ-dichotomous l u)
     (λ (n , l≤u) → Ic-predicates-are-searchable' δ l u n l≤u (p , d))
     (λ      u≤l  → l
                  , λ (k₀ , (l≤k₀ , k₀≤u) , pk₀)
                  → transport (λ - → p (- , δ))
                      (≤ℤ-antisym k₀ l ((ℤ≤-trans k₀ u l k₀≤u u≤l) , l≤k₀))
                      pk₀)


Ic'-search
 : {𝓤 : Universe} (l u : ℤ)
 → ((p , _) : special-predicate-Ic' {𝓤} l u)
 → Σ k ꞉ ℤ[ l , u ] , (Σ p → p k)
Ic'-search = {!!}

Ic-predicates-are-searchable2'
 : {𝓤 : Universe} ((k , i) : ℤ × ℤ) (δ : ℤ)
 → ((p , _) : special-predicate-Ic {𝓤} (k , i) δ)
 → let l = lower (k , i) δ in
   let u = upper (k , i) δ in
   Σ (c , ζ) ꞉ ℤ[ l , u ]
 , ((Σ (c₀ , ζ₀) ꞉ ℤ[ l , u ] , p ((c₀ , δ) , ζ₀))
 → p ((c , δ) , ζ))
Ic-predicates-are-searchable2' (k , i) δ (p , d)
 = Ic'-search l u ((λ (x , l≤x≤u) → p ((x , δ) , l≤x≤u))
                 , (λ (x , l≤x≤u) → d ((x , δ) , l≤x≤u)))
 where
   l = lower (k , i) δ
   u = upper (k , i) δ
```

Therefore, 𝕂c predicates are searchable in two ways: directly, or
via the isomorphism.

```
logically-equivalent
 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
 → (px : X → 𝓦 ̇ ) (py : Y → 𝓦 ̇ )
 → (f : X → Y)
 → (g : Y → X)
 → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇ 
logically-equivalent {𝓤} {𝓥} {𝓦} {X} {Y} px py f g
 = ((x : X) → px x ⇔ py (f x))
 × ((y : Y) → py y ⇔ px (g y))

logically-equivalent2
 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
 → (A : (X → 𝓦 ̇ ) → 𝓤' ̇ )
 → (B : (Y → 𝓦 ̇ ) → 𝓣 ̇ )
 → (f : Σ A → Σ B)
 → (g : Σ B → Σ A)
 → 𝓤 ⊔ 𝓥 ⊔ (𝓦 ⁺) ⊔ 𝓤' ⊔ 𝓣 ̇ 
logically-equivalent2 {𝓤} {𝓥} {𝓦} {𝓢} {𝓣} {X} {Y} A B f g
 = (Π p ꞉ Σ A , ((x : X) → pr₁ p x → Σ (pr₁ (f p))))
 × (Π p ꞉ Σ B , ((y : Y) → pr₁ p y → Σ (pr₁ (g p))))

this-logically-equiv : ((k , i) : ℤ × ℤ) (δ : ℤ)
 → logically-equivalent2
     {!!} {!!}
     (special-predicate-𝕂c-Ic (k , i) δ)
     (special-predicate-Ic-𝕂c (k , i) δ)
this-logically-equiv (k , i) δ
 = (λ (p , d , ϕ) x → {!!})
 , (λ (p , d)     x → {!!})

logically-equivalent-properties
 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
 → (A : (X → 𝓦 ̇ ) → 𝓣 ̇ )
 → (B : (Y → 𝓦 ̇ ) → 𝓣 ̇ )
 → ((px , _) : Σ A) ((py , _) : Σ B)
 → (f : Σ A → Σ B)
 → (g : Σ B → Σ A)
 → logically-equivalent2 A B f g
 → (Σ x ꞉ X , (Σ px → px x))
 → (Σ y ꞉ Y , (Σ py → py y))
logically-equivalent-properties A B (px , dϕx) (py , dϕy) f g (e₁ , e₂) (x , γx)
 = pr₁ (e₁ (px , dϕx) x (γx {!!}))
 , {!!}
```


## Predicates to test

## Fuel





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
