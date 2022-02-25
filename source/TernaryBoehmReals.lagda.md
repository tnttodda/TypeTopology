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

module TernaryBoehmReals
 (fe : {𝓤 𝓥 : Universe} → {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {f g : Π Y}
                        → f ∼ g → f ≡ g) where

open import InfiniteSearch2 fe

{-# BUILTIN INTEGER       ℤ       #-}
{-# BUILTIN INTEGERPOS    pos     #-}
{-# BUILTIN INTEGERNEGSUC negsucc #-}
```

##

We encode real numbers using the data type for ternary Boehm reals 𝕂.

Each 𝕂 is a function x ꞉ ℤ → ℤ with some restrictions on it, so that
we only have our encodings of real numbers inside 𝕂, and not any
function of type ℤ → ℤ.

The function x : ℤ → ℤ takes a "precision-level" n : ℤ and gives back
an encoding x(n) : ℤ of a real interval.

##

The idea is that each precision-level n : ℤ represents a "layer" in
the following illustrative "brick pattern".

Level n+1 has bricks half the size of those on level n.
Here level 0 and 1 are shown.

-1        0         1         2
__________ _________ _________ ____
|___-2____|____0____|____2____|____
 ____|___-1____|____1____|____3____|
 ____ ____ ____ ____ ____ ____ ____
|-4__|-2__|_0__|_2__|_4__|_6__|_8__|
 _|_-3_|_-1_|__1_|__3_|__5_|__7_|__

Then, x(n) : ℤ refers to a precise labelled "brick" in the brick
pattern.

Each brick encodes a real interval; specifically the interval
⟪ x(n) , n ⟫ as defined below.

⟪_⟫ : ℤ × ℤ → ℚ × ℚ
⟪ k , p ⟫ = (k / 2^{p + 1}) , ((k + 2) / 2^{p + 1})

##

Therefore, an encoding of a real number is a sequence of encodings of
real intervals -- the restriction we add is that each brick x(n) is
"below" the brick x(n+1); meaning ⟪ x(n+1) , n+1 ⟫ ⊂ ⟪ x(n) , n ⟫.

Note that there are precisely three brick below each brick.

downLeft downMid downRight : ℤ
downLeft  a = a +ℤ a
downMid   a = succℤ (downLeft a)
downRight a = succℤ (downMid  a)

_below_ : ℤ → ℤ
a below b = downLeft b ≤ℤ a ≤ℤ downRight b

𝕂 : 𝓤₀ ̇ 
𝕂 = Σ x ꞉ ℤ → ℤ , (n : ℤ) → (x (succℤ n)) below (x n)

The real number represented by x : 𝕂 is defined as ⟦ x ⟧ : ℝ.

⟨_⟩ : 𝕂 → (ℤ → ℤ)
⟨ x , _ ⟩ = x

⟦_⟧ : 𝕂 → ℝ
⟦ x ⟧ = ⋃ᵢ ⟪ ⟨ x ⟩ i ⟫

## upLeft / upRight

We may also wish to go "up" the brick pattern from a specific brick.

Even-numbered bricks are covered by two bricks at the preceeding
precision-level, whereas odd-numbered bricks are covered by exactly
one.

We define the functions upLeft : ℤ → ℤ and upRight : ℤ → ℤ, such that
when k : ℤ is even upLeft k = predℤ (upRight k) and when n is odd
upLeft k = upRight k.

upLeft upRight : ℤ → ℤ
upLeft  = {!!}
upRight = {!!}

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

##

Similarly to the replacement function, we can construct 𝕂 using just
a function ℕ → ℤ.

build : (Σ x ꞉ (ℕ → ℤ) , (n : ℕ) → (x (succ n)) below (x n)) → ℤ → 𝕂
build (x , γx) i = λ n → if   n <ℤ i
                         then rec upRight (i - n)  x(0)
                         else x(n - i)
                 , λ n → if   n <ℤ i
                         then rec upRight-is-below (i - n) γx(i) 
                         else γx(n - i)
                         
##

Given any specific brick on a specific level, i.e. (k , p) : ℤ × ℤ
representing ⟪ k , p ⟫, we can define an element of the closed
interval ⟪ k , p ⟫.

ClosedInterval : ℤ × ℤ → 𝓤₀ ̇
ClosedInterval (k , p) = Σ (x , _) : 𝕂 , x(p) ≡ k 

You can also build an element of a closed interval in a similar way

build-ci : (Σ x ꞉ (ℕ → ℤ) , (n : ℕ) → (x (succ n)) below (x n))
         → (i : ℤ) → ClosedInterval (x(0) , i)
build-ci x = build x i , {!!}

## Signed-digits are isomorphic

Recall that we previously represented numbers in the closed interval
[-1,1] using signed-digit functions of type ℕ → 𝟛.

⦉_⦊ : (ℕ → 𝟛) → ℝ
⦉ α ⦊ = Σᵢ α i * 2^{-i-1}

This interval is represented by the Boehm "brick" (-1 , -1) : ℕ × ℕ.

[−1,1]-code : ℤ × ℤ
[−1,1]-code = (-1 , -1)

The location structure of the signed-digit approach is actually
isomorphic to the ternary Boehm approach.

For example, the signed digit function
 α ≔     { −1            ,  O           , +1             ...} : ℕ → 𝟛
follows the same location structure as
 x ≔ {-1 , downLeft x(0) , downMid x(1) , downRight x(2) ...} : ℕ → ℤ

𝟛-to-down : 𝟛 → (ℤ → ℤ)
𝟛-to-down −1 = downLeft
𝟛-to-down  O = downMid
𝟛-to-down +1 = downRight

signed-to-boehm' : (ℕ → 𝟛) → (ℕ → ℤ)
signed-to-boehm' α 0 = -1
signed-to-boehm' α (succ n) = 𝟛-to-down (α n) (signed-to-boehm' α n)

signed-to-boehm'-below
  : (α : ℕ → 𝟛) → (n : ℕ)
  → (signed-to-boehm' α (succ n)) below (signed-to-boehm' α n)
signed-to-boehm'-below α n = {!!} -- Easy

signed-to-boehm : (ℕ → 𝟛) → ClosedInterval [−1-1]-code
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

## The key difference

The key difference between the signed digit approach and the Boehm
approach is that,
 * With signed digit, the information kept in x(n) *depends on*
                      the information in all x(i) such that i < n,
 * With Boehm codes,  the information kept in x(n) *includes*
                      the information in all x(i) such that i < n.

## Closeness function on 𝕂

For every discrete-sequence type ℕ → X (where X is discrete), we have
a canonical closeness function c : (ℕ → X) × (ℕ → X) → ℕ∞.

Recall that for x,y : ℕ → X and any δ : ℕ,

c (x , y) ≼ ι δ ⇔ (x ≈ y) δ,

where c(x , y) : ℕ∞ is the value of the discrete-sequence closeness
function for x and y.

_≈_ : {X : 𝓤 ̇ } → (ℕ → X) → (ℕ → X) → ℕ → 𝓤 ̇
(α ≈ β) n = (i : ℕ) → i < n → α n ≡ β n

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
themselves, we can instead use the following pseudo-closenss
function (I THINK!)

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

uc-d-predicate-on-seqs : {X : 𝓤 ̇ } → (p : X → 𝓥 ̇ ) → (𝓤 ⊔ 𝓥) ̇ 
uc-d-predicate-on-seqs {X} p
 = ((x : X) → decidable (p x))
 × (Σ δ ꞉ ℕ , (α β : ℕ → X) → (α ≈ β) δ → p α ⇔ p β)

We call the δ : ℕ of such a predicate its 'modulus of continuity'.

So for uniformly continuous decidable predicates p on signed-digit
encodings x,y : ℕ → 𝟛, with modulus of continuity δ : ℕ, it is enough
to know that (x ≈ y) δ to know that p(x) is logically equivalent
to p(y).

(Reword ↓)
But! With Boehm codes 𝕂, all the information is kept in the most recent
code. So if an "equivalent" predicate should only need to satisfy the
following.

special-predicate : (p : 𝕂 → 𝓤 ̇ ) → 𝓤 ̇
special-predicate p
 = ((x : 𝕂) → decidable (p x))
 × (Σ δ ꞉ ℕ , (α β : 𝕂) → ⟨ α ⟩ (pos δ) ≡ ⟨ β ⟩ (pos δ) → p α ⇔ p β)


Relationships:
 * c (α , β) ≼ δ                 → pc (α , β) ≼ δ
 * c (α , β) ≼ (succ δ)          → ⟨ α ⟩ (pos δ) ≡ ⟨ β ⟩ (pos δ)
 * ⟨ α ⟩ (pos δ) ≡ ⟨ β ⟩ (pos δ) → pc (α , β) ≼ δ ?
