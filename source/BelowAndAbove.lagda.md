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

module BelowAndAbove (fe : FunExt)where

open import TernaryBoehmRealsPrelude fe

downLeft downMid downRight : ℤ → ℤ
downLeft  a = a +ℤ a
downMid   a = succℤ (downLeft a)
downRight a = succℤ (downMid  a)

_below_ : ℤ → ℤ → 𝓤₀ ̇ 
a below b = downLeft b ≤ℤ a ≤ℤ downRight b

{-
_above_ : ℤ → ℤ → 𝓤₀ ̇ 
b above a = upLeft a ≤ℤ b ≤ℤ upRight a
-}

_below'_ : ℤ → ℤ → 𝓤₀ ̇
a below' b = (a ≡ downLeft b) + (a ≡ downMid b) + (a ≡ downRight b)

downLeft-below  : (a : ℤ) → downLeft a below a
downLeft-below  a = (0 , refl) , (2 , refl)

downMid-below   : (a : ℤ) → downMid a below a
downMid-below   a = (1 , refl) , (1 , refl)

downRight-below : (a : ℤ) → downRight a below a
downRight-below a = (2 , refl) , (0 , refl)

below'-implies-below : (a b : ℤ) → a below' b → a below b
below'-implies-below .(downLeft  b) b (inl      refl ) = downLeft-below b
below'-implies-below .(downMid   b) b (inr (inl refl)) = downMid-below b
below'-implies-below .(downRight b) b (inr (inr refl)) = downRight-below b



```
