```agda
{-# OPTIONS --without-K --exact-split #-}

module TernaryBoehmRealsPrelude where


open import SpartanMLTT public
open import Two-Properties public hiding (zero-is-not-one)
open import NaturalsOrder public
open import NaturalsAddition public renaming (_+_ to _+ℕ_)
open import IntegersB public
open import IntegersOrder public
open import IntegersAddition public renaming (_+_ to _+ℤ_)
open import IntegersNegation public renaming (-_  to  −ℤ_)
open import UF-Subsingletons public
open import NaturalsOrder public
-- open import Infi

_≤ℤ_≤ℤ_ : ℤ → ℤ → ℤ → 𝓤₀ ̇ 
x ≤ℤ y ≤ℤ z = (x ≤ℤ y) × (y ≤ℤ z)

≤ℤ²-is-prop : {l u : ℤ} (x : ℤ) → is-prop (l ≤ℤ x ≤ℤ u)
≤ℤ²-is-prop {l} {u} x = ×-is-prop (ℤ≤-is-prop l x) (ℤ≤-is-prop x u)

data 𝟛 : 𝓤₀ ̇ where
  −1 O +1 : 𝟛

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

_−ℤ_ : ℤ → ℤ → ℤ
x −ℤ y = x +ℤ (−ℤ y)
