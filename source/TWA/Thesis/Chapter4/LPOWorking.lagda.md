```agda

{-# OPTIONS --without-K --exact-split --safe #-}

open import MLTT.Spartan
open import Fin.Type
open import Fin.Bishop
open import UF.FunExt
open import UF.DiscreteAndSeparated
open import Notation.Order
open import Naturals.Order
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Embeddings
open import CoNaturals.GenericConvergentSequence
  renaming (ℕ-to-ℕ∞ to ι
         ; Zero-smallest to zero-minimal
         ; ∞-largest to ∞-maximal)
open import NotionsOfDecidability.Decidable
open import NotionsOfDecidability.Complemented
open import MLTT.Two-Properties
open import Taboos.WLPO

open import TWA.Thesis.Chapter2.Finite
open import TWA.Thesis.Chapter2.Sequences

module TWA.Thesis.Chapter4.LPOWorking (fe : FunExt) where

fe₀ = fe 𝓤₀ 𝓤₀

open import Taboos.BasicDiscontinuity fe₀
open import TWA.Thesis.Chapter4.ApproxOrder fe
open import TWA.Thesis.Chapter4.ApproxOrder-Examples fe


```
