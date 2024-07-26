```agda
{-# OPTIONS --without-K --exact-split --safe #-}

open import MLTT.Spartan
open import UF.DiscreteAndSeparated
open import UF.Subsingletons
open import UF.Sets
open import UF.Sets-Properties
open import UF.Equiv
open import UF.EquivalenceExamples

module TWA.Thesis.Chapter2.Equiv-Example where

open import UF.Subsingletons-FunExt
open import Quotient.Type

_is-_-small : (X : 𝓤 ̇ ) (𝓥 : Universe) → (𝓤 ⊔ 𝓥 ⁺) ̇ 
X is- 𝓥 -small = Σ Y ꞉ 𝓥  ̇ , X ≃ Y

module _ (sq : general-set-quotients-exist λ x → x) where

 open general-set-quotients-exist sq

 question : (A : 𝓣  ̇ ) (B : A → 𝓤  ̇ ) (𝓥 : Universe)
          → Σ B is- 𝓥 -small
          → (a : A) → B a is- {!!} -small
 question {𝓣} {𝓤} A B 𝓥 (Y , f , (g , η) , (h , μ)) a
  = fiber (pr₁ ∘ {!f!}) a
  , {!!}

```
