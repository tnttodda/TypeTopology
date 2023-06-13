\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import MLTT.Spartan
open import UF.FunExt
open import NotionsOfDecidability.Complemented
open import TypeTopology.DiscreteAndSeparated
open import Notation.Order
open import Naturals.Order
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Quotient
open import UF.Miscelanea
open import MLTT.Two-Properties
open import UF.Equiv

module Thesis.Chapter2.FiniteDiscrete where

-- Definition 3.1.5
𝔽 : ℕ → 𝓤₀  ̇
𝔽 0 = 𝟘
𝔽 (succ n) = 𝟙 + 𝔽 n

-- Definition 3.1.6
finite-discrete : 𝓤 ̇ → 𝓤  ̇
finite-discrete X = Σ n ꞉ ℕ , 𝔽 n ≃ X

-- Lemma 3.1.7
𝔽-is-discrete : (n : ℕ) → is-discrete (𝔽 n)
𝔽-is-discrete 0 = 𝟘-is-discrete
𝔽-is-discrete (succ n) = +-is-discrete 𝟙-is-discrete (𝔽-is-discrete n)

finite-discrete-is-discrete
 : {X : 𝓤 ̇ } → finite-discrete X → is-discrete X
finite-discrete-is-discrete (n , e)
 = equiv-to-discrete e (𝔽-is-discrete n)

-- Extras
𝔽-is-set : {n : ℕ} → is-set (𝔽 n)
𝔽-is-set {succ n} = +-is-set 𝟙 (𝔽 n) 𝟙-is-set 𝔽-is-set

finite-is-set : {F : 𝓤 ̇ } → (f : finite-discrete F) → is-set F
finite-is-set (n , f) = equiv-to-set (≃-sym f) 𝔽-is-set
\end{code}