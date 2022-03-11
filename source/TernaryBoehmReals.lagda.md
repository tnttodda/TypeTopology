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
ℤ[_,_] : ℤ → ℤ → 𝓤₀ ̇
ℤ[ l , u ] = Σ c ꞉ ℤ , l ≤ℤ c ≤ℤ u

record predicate-verifier (X : 𝓤 ̇ ) : 𝓤 ⊔ 𝓥 ⁺ ̇  where
  field
    _≣_ : X → X → 𝓥 ̇
    ≣-refl  : (x     : X) → x ≣ x
    ≣-sym   : (x y   : X) → x ≣ y → y ≣ x
    ≣-trans : (x y z : X) → x ≣ y → y ≣ z → x ≣ z

preds-that-satisfy : {𝓤 𝓥 𝓦 : Universe} {X : 𝓤 ̇ }
                   → predicate-verifier {𝓤} {𝓥} X
                   → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺ ̇ 
preds-that-satisfy {𝓤} {𝓥} {𝓦} {X} A
 = Σ p ꞉ (X → 𝓦 ̇  )
 , ((x : X) → decidable (p x))
 × ((x y : X) → x ≣ y → p x ⇔ p y)
 where open predicate-verifier A

searchable : {𝓤 𝓥 𝓦 : Universe} (X : 𝓤 ̇ )
           → predicate-verifier {𝓤} {𝓥} X
           → 𝓤 ⊔ 𝓥 ⊔ (𝓦 ⁺) ̇
searchable {𝓤} {𝓥} {𝓦} X A
 = Π (p , d , ϕ) ꞉ preds-that-satisfy {𝓤} {𝓥} {𝓦} A
 , (Σ x ꞉ X , (Σ p → p x))

all-predicates : (X : 𝓤 ̇ ) → predicate-verifier {𝓤} {𝓤} X
predicate-verifier._≣_     (all-predicates X) = _≡_
predicate-verifier.≣-refl  (all-predicates X) x     = refl
predicate-verifier.≣-sym   (all-predicates X) x y   = _⁻¹
predicate-verifier.≣-trans (all-predicates X) x y z = _∙_

all-satisfy-all : {X : 𝓤 ̇ } → (p : X → 𝓥 ̇ ) → ((x : X) → decidable (p x))
                → preds-that-satisfy (all-predicates X)
all-satisfy-all p d
 = p , d , λ x y x≡y → transport p x≡y , transport p (x≡y ⁻¹)

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

ℤ[_,_]-unpred : (l u : ℤ) → ℤ[ l , predℤ u ] → ℤ[ l , u ]
ℤ[_,_]-unpred l u (x , l≤x , n , x≤pu)
 = x , l≤x , succ n , (ap succℤ x≤pu ∙ succpredℤ u)

ℤ[_,_]-pred : (l u : ℤ) → ((x , _) : ℤ[ l , u ]) → x <ℤ u → ℤ[ l , predℤ u ]
ℤ[ l , u ]-pred (x , l≤x , _) x<u = x , l≤x , (≤ℤ-back x u x<u)

```

The Ic predicates are searchable, and are logically equivalent to the 𝕂c
predicates.

```

ℤ[_,_]-searchable' : {𝓦 : Universe} → (l u : ℤ) → (n : ℕ) → l +pos n ≡ u
                   → searchable {_} {_} {𝓦} (ℤ[ l , u ]) (all-predicates _)
ℤ[ u , u ]-searchable' zero refl (p , d , ϕ)
 = (u , ℤ≤-refl u , ℤ≤-refl u)
 , λ (x , pu) → transport p
     (to-subtype-≡ ≤ℤ²-is-prop (≤ℤ-antisym u (pr₁ x) (pr₂ x) ⁻¹)) pu
ℤ[ l , u ]-searchable' (succ n) l+n≡u (p , d , ϕ)
 = Cases (d (u , ((succ n , l+n≡u) , ℤ≤-refl u)))
     (λ  pu → _ , (λ _ → pu))
     (λ ¬pu → ℤ[ l , u ]-unpred k , λ ((k₀ , (l≤k₀ , k₀≤u)) , pk₀)
      → Cases (ℤ≤-split k₀ u k₀≤u)
          (λ k<u → γ (ℤ[ l , u ]-pred (k₀ , (l≤k₀ , k₀≤u)) k<u
                 , transport p (to-subtype-≡ ≤ℤ²-is-prop refl) pk₀))
          (λ k≡u → 𝟘-elim (¬pu (transport p (to-subtype-≡ ≤ℤ²-is-prop k≡u) pk₀))))
 where
   IH = ℤ[ l , predℤ u ]-searchable' n (succℤ-lc (l+n≡u ∙ succpredℤ u ⁻¹))
          (all-satisfy-all (p ∘ ℤ[ l , u ]-unpred) (d ∘ ℤ[ l , u ]-unpred))
   k = pr₁ IH
   γ = pr₂ IH

```

Therefore, 𝕂c predicates are searchable in two ways: directly, or
via the isomorphism.

```
record predicate-verifiers {𝓤 𝓤' 𝓥 𝓥' : Universe} {X : 𝓤 ̇ } {Y : 𝓤' ̇ }
  (A : predicate-verifier {𝓤 } {𝓥 } X)
  (B : predicate-verifier {𝓤'} {𝓥'} Y)  : 𝓤 ⊔ 𝓤' ⊔ 𝓥 ⊔ 𝓥' ⁺  ̇ where
  field
    f : X → Y
    g : Y → X
    trans-A : (x : X) → predicate-verifier._≣_ A x ((g ∘ f) x)
    trans-B : (y : Y) → predicate-verifier._≣_ B y ((f ∘ g) y)
    lift-AB : (x₁ x₂ : X) → predicate-verifier._≣_ A    x₁     x₂
                          → predicate-verifier._≣_ B (f x₁) (f x₂)
    lift-BA : (y₁ y₂ : Y) → predicate-verifier._≣_ B    y₁     y₂
                          → predicate-verifier._≣_ A (g y₁) (g y₂)

compact-predicates : ((k , i) : ℤ × ℤ) (δ : ℤ) → predicate-verifier {𝓤₀} {𝓤₀} (CompactInterval (k , i))
predicate-verifier._≣_     (compact-predicates (k , i) δ) x y   = ⟨ ι x ⟩ δ ≡ ⟨ ι y ⟩ δ
predicate-verifier.≣-refl  (compact-predicates (k , i) δ) x     = refl
predicate-verifier.≣-sym   (compact-predicates (k , i) δ) x y   = _⁻¹
predicate-verifier.≣-trans (compact-predicates (k , i) δ) x y z = _∙_

compact→ℤ : ((k , i) : ℤ × ℤ) (δ : ℤ)
          → let l = lower (k , i) δ in
            let u = upper (k , i) δ in
            predicate-verifiers
              (all-predicates ℤ[ l , u ])
              (compact-predicates (k , i) δ)
predicate-verifiers.f       (compact→ℤ (k , i) δ)
 = {!!} -- build-via
predicate-verifiers.g       (compact→ℤ (k , i) δ) x
 = ⟨ ι x ⟩ δ , (ci-lower-upper (k , i) x δ)
predicate-verifiers.trans-A (compact→ℤ (k , i) δ) (c , ζ)
 = {!!}
predicate-verifiers.trans-B (compact→ℤ (k , i) δ)
 = {!!}
predicate-verifiers.lift-AB (compact→ℤ (k , i) δ)
 = {!!}
predicate-verifiers.lift-BA (compact→ℤ (k , i) δ) x y xδ≡yδ
 = to-subtype-≡ ≤ℤ²-is-prop xδ≡yδ

natural-conversion-process-ϕ
 : {𝓤 𝓤' 𝓥 𝓥' 𝓦 : Universe}
 → {X : 𝓤 ̇ } {Y : 𝓤' ̇  }
 → (A  : predicate-verifier  {𝓤 } {𝓥 } X)
 → (B  : predicate-verifier  {𝓤'} {𝓥'} Y)
 → (FG : predicate-verifiers A B)
 → let f = predicate-verifiers.f FG in
   let g = predicate-verifiers.g FG in
   (Π (px , _) ꞉ preds-that-satisfy {𝓤 } {𝓥 } {𝓦} A
 ,  Σ (py , _) ꞉ preds-that-satisfy {𝓤'} {𝓥'} {𝓦} B
 , ((x : X) → px x ⇔ py (f x)))
natural-conversion-process-ϕ A B FG
 = (λ (px , dx , ϕx) → (px ∘ g  , dx ∘ g
 , (λ y₁ y₂ By₁y₂ → ϕx (g y₁) (g y₂) (lift-BA y₁ y₂ By₁y₂)))
 , (λ x → ϕx x ((g ∘ f) x) (trans-A x)))
 where open predicate-verifiers FG

something
 : {𝓤 𝓤' 𝓥 𝓥' 𝓦 : Universe}
 → {X : 𝓤 ̇ } {Y : 𝓤' ̇  }
 → (A  : predicate-verifier  {𝓤 } {𝓥 } X)
 → (B  : predicate-verifier  {𝓤'} {𝓥'} Y)
 → (FG : predicate-verifiers {𝓤 } {𝓤'} {𝓥 } {𝓥'} A B)
 → (px : preds-that-satisfy {𝓤 } {𝓥 } {𝓦} A)
 → (Σ x ꞉ X , (Σ (pr₁ px) → pr₁ px x))
 → let ((py , _) , _) = natural-conversion-process-ϕ A B FG px in
   (Σ y ꞉ Y , (Σ py → py y))
something A B FG (px , dx , ϕx) (x , γx)
 = f x
 , λ (y , pyy) → pr₁ (γy x) (γx (g y , pr₂ (γy (g y))
                   (pr₁ (ϕx (g y) (g (f (g y))) (trans-A (g y))) pyy)))
 where open predicate-verifiers FG
       open predicate-verifier B
       γy = pr₂ (natural-conversion-process-ϕ A B FG (px , dx , ϕx))
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
