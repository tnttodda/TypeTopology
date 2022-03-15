```agda
{-# OPTIONS --without-K --exact-split #-}


open import SpartanMLTT
open import UF-FunExt

module SearchableTypes (fe : FunExt) where

open import Two-Properties public hiding (zero-is-not-one)
open import NaturalsOrder public
open import NaturalsAddition public renaming (_+_ to _+ℕ_)
open import IntegersB public
open import IntegersOrder public
open import IntegersAddition public renaming (_+_ to _+ℤ_)
open import IntegersNegation public renaming (-_  to  −ℤ_)
open import UF-Subsingletons public
open import NaturalsOrder public
open import DecidableAndDetachable
open import UF-Equiv
open import UF-Subsingletons-FunExt
open import InfiniteSearch1 (dfunext (fe _ _))
  hiding (predicate;everywhere-decidable;decidable)
```

We start with decidable predicates on a given type.

```agda
everywhere-prop-valued : {𝓦 𝓤 : Universe} {X : 𝓤 ̇} → (X → 𝓦 ̇ ) → 𝓦 ⊔ 𝓤 ̇
everywhere-prop-valued {𝓦} {𝓤} {X} p 
 = Π x ꞉ X , is-prop (p x)

predicate : {𝓦 𝓤 : Universe} {X : 𝓤 ̇} → (𝓦 ⁺) ⊔ 𝓤 ̇
predicate {𝓦} {𝓤} {X} 
 = Σ p ꞉ (X → 𝓦 ̇ ) , everywhere-prop-valued p

everywhere-decidable : {𝓦 𝓤 : Universe} {X : 𝓤 ̇} → (X → 𝓦 ̇ ) → 𝓦 ⊔ 𝓤 ̇
everywhere-decidable {𝓦} {𝓤} {X} p
 = Π x ꞉ X , decidable (p x)

decidable-predicate : {𝓦 𝓤 : Universe} → 𝓤 ̇ → (𝓦 ⁺) ⊔ 𝓤 ̇
decidable-predicate {𝓦} {𝓤} X
 = Σ p ꞉ (X → 𝓦 ̇ )
 , everywhere-decidable p × everywhere-prop-valued p
```

Some predicates use equivalence relations to determine
information about the predicate.

We define equivalence relations in the usual way.

```agda
record equivalence-relation {𝓥 𝓤 : Universe} (X : 𝓤 ̇ ) : 𝓤 ⊔ 𝓥 ⁺ ̇  where
  field
    _≣_ : X → X → 𝓥 ̇
    ≣-refl  : (x     : X) → x ≣ x
    ≣-sym   : (x y   : X) → x ≣ y → y ≣ x
    ≣-trans : (x y z : X) → x ≣ y → y ≣ z → x ≣ z
```

The class of predicates quotiented (?) by a particular
equivalence relation is defined as follows.

```agda
_informs_ : {𝓦 𝓤 𝓥 : Universe} {X : 𝓤 ̇ }
          → equivalence-relation {𝓥} X
          → (X → 𝓦 ̇ ) → 𝓦 ⊔ 𝓤 ⊔ 𝓥 ̇
A informs p = ∀ x y → x ≣ y → p x → p y
 where open equivalence-relation A

decidable-predicate-informed-by
 : {𝓦 𝓤 𝓥 : Universe} {X : 𝓤 ̇ }
 → equivalence-relation {𝓥} X
 → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺ ̇ 
decidable-predicate-informed-by {𝓦} {𝓤} {𝓥} {X} A
 = Σ (p , di) ꞉ decidable-predicate {𝓦} X
 , A informs p
```

Trivially, identity informs every predicate.

```agda
Identity : (X : 𝓤 ̇ ) → equivalence-relation {𝓤} {𝓤} X
equivalence-relation._≣_     (Identity X)       = _≡_
equivalence-relation.≣-refl  (Identity X) x     = refl
equivalence-relation.≣-sym   (Identity X) x y   = _⁻¹
equivalence-relation.≣-trans (Identity X) x y z = _∙_

decidable-predicate' : {𝓦 𝓤 : Universe} (X : 𝓤 ̇ )
                     → (𝓦 ⁺) ⊔ 𝓤 ̇ 
decidable-predicate' {𝓦} X
 = decidable-predicate-informed-by {𝓦} (Identity X)

Id-informs-everything : {𝓦 𝓤 : Universe} {X : 𝓤 ̇ }
                      → (p : X → 𝓦 ̇ ) → Identity X informs p
Id-informs-everything p x x refl = id

Id-informs-is-prop : {𝓦 𝓤 : Universe} {X : 𝓤 ̇ }
                   → ((p , di) : decidable-predicate {𝓦} X)
                   → is-prop (Identity X informs p)
Id-informs-is-prop (p , d , i)
 = Π-is-prop (fe _ _)
     (λ _ → Π-is-prop (fe _ _)
       (λ y → Π-is-prop (fe _ _)
         (λ _ → Π-is-prop (fe _ _)
           (λ _ → i y))))


to-subtype-≃ : {X : 𝓦 ̇ } {A : X → 𝓥 ̇ }
             → ((x : X) → A x)
             → ((x : X) → is-prop (A x))
             → X ≃ Σ A
to-subtype-≃ {_} {_} {X} {A} f i
 = (λ x → x , f x)
 , ((pr₁ , λ (x , Ax) → ap (x ,_) (i x (f x) Ax))
 , ( pr₁ , λ _ → refl))

decidable-predicate-≃ : {𝓦 𝓤 : Universe} {X : 𝓤 ̇ }
                      → decidable-predicate  {𝓦} X
                      ≃ decidable-predicate' {𝓦} X
decidable-predicate-≃ {𝓦} {𝓤} {X}
 = to-subtype-≃
     (λ (p , di) → Id-informs-everything p)
     Id-informs-is-prop
```

Some predicates are informed by other equivalence relations.

For example, so-called 'continuous' predicates as defined by
closeness functions are informed by a particular equivalence
relation.

First, recall our definition of closeness functions.

```agda
record closeness-function (X : 𝓤 ̇ ) : 𝓤 ̇ where
  field
    c : X × X → ℕ∞ 
    equal→inf-close : (x     : X) → c (x , x) ≡ ∞
    inf-close→equal : (x y   : X) → c (x , y) ≡ ∞ → x ≡ y
    symmetricity : (x y   : X) → c (x , y) ≡ c (y , x)
    ultrametric : (x y z : X) → min (c (x , y)) (c (y , z)) ≼ c (x , z)

≼-min : ∀ x y z → x ≼ y → x ≼ z → x ≼ min y z
≼-min x y z x≼y x≼z n r = Lemma[a≡₁→b≡₁→min𝟚ab≡₁] (x≼y n r) (x≼z n r)

≼-trans : ∀ x y z → x ≼ y → y ≼ z → x ≼ z
≼-trans x y z p q n = q n ∘ p n

_-Close-via_ : {X : 𝓤 ̇ } (δ : ℕ) → closeness-function X
             → equivalence-relation X
equivalence-relation._≣_     (δ -Close-via C) x y
 = (δ ↑) ≼ c (x , y)
 where open closeness-function C
equivalence-relation.≣-refl  (δ -Close-via C) x
 = transport ((δ ↑) ≼_) (equal→inf-close x ⁻¹) (∞-maximal (δ ↑))
 where open closeness-function C
equivalence-relation.≣-sym   (δ -Close-via C) x y
 = transport ((δ ↑) ≼_) (symmetricity x y)
 where open closeness-function C
equivalence-relation.≣-trans (δ -Close-via C) x y z δ≼cxy δ≼cyz
 = ≼-trans (δ ↑) (min (c (x , y)) (c (y , z))) (c (x , z))
     (≼-min (δ ↑) (c (x , y)) (c (y , z)) δ≼cxy δ≼cyz)
     (ultrametric x y z)
 where open closeness-function C
```

Continuous predicates are those for which there is some δ : ℕ
such that the equivalence relation of being δ-close via any
closeness function informs the predicate.

```agda
continuous-predicate : {𝓦 𝓤 : Universe} {X : 𝓤 ̇ }
                     → closeness-function X → (𝓦 ⁺) ⊔ 𝓤 ̇
continuous-predicate {𝓦} C
 = Σ δ ꞉ ℕ , decidable-predicate-informed-by {𝓦} (δ -Close-via C)

```
