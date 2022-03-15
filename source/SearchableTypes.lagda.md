```agda
{-# OPTIONS --without-K --exact-split #-}


open import SpartanMLTT
open import UF-FunExt
open import UF-Subsingletons

module SearchableTypes (fe : FunExt) (pe : PropExt) where

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
  hiding (predicate;everywhere-decidable;decidable;trivial-predicate)
```

We start with decidable predicates on a given type.

```agda
everywhere-prop-valued : {𝓦 𝓤 : Universe} {X : 𝓤 ̇}
                       → (X → 𝓦 ̇ ) → 𝓦 ⊔ 𝓤 ̇
everywhere-prop-valued {𝓦} {𝓤} {X} p 
 = Π x ꞉ X , is-prop (p x)

predicate : {𝓦 𝓤 : Universe} {X : 𝓤 ̇} → (𝓦 ⁺) ⊔ 𝓤 ̇
predicate {𝓦} {𝓤} {X} 
 = Σ p ꞉ (X → 𝓦 ̇ ) , everywhere-prop-valued p

everywhere-decidable : {𝓦 𝓤 : Universe} {X : 𝓤 ̇}
                     → (X → 𝓦 ̇ ) → 𝓦 ⊔ 𝓤 ̇
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
record equivalence-relation {𝓥 𝓤 : Universe} (X : 𝓤 ̇ ) : 𝓤 ⊔ 𝓥 ⁺ ̇
  where field
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
```

Therefore, decidable predicates on X are equivalent to decidable
predicates on X informed by identity; the quotienting by _≡_ does not
remove any decidable predicates.

```agda
informs-is-prop : {𝓦 𝓥 𝓤 : Universe} {X : 𝓤 ̇ }
                → (A : equivalence-relation {𝓥} X)
                → (p : X → 𝓦 ̇ )
                → (i : everywhere-prop-valued p)
                → is-prop (A informs p)
informs-is-prop A p i
 = Π-is-prop (fe _ _)
     (λ _ → Π-is-prop (fe _ _)
       (λ y → Π-is-prop (fe _ _)
         (λ _ → Π-is-prop (fe _ _)
           (λ _ → i y))))

to-subtype-≃ : {X : 𝓦 ̇ } {A : X → 𝓥 ̇ }
             → ((x : X) → A x × is-prop (A x))
             → X ≃ Σ A
to-subtype-≃ {_} {_} {X} {A} fi
 = (λ x → x , f x)
 , ((pr₁ , λ (x , Ax) → ap (x ,_) (i x (f x) Ax))
 , ( pr₁ , λ _ → refl))
 where
   f = λ x → pr₁ (fi x)
   i = λ x → pr₂ (fi x)

decidable-predicate-≃ : {𝓦 𝓤 : Universe} {X : 𝓤 ̇ }
                      → decidable-predicate  {𝓦} X
                      ≃ decidable-predicate' {𝓦} X
decidable-predicate-≃ {𝓦} {𝓤} {X}
 = to-subtype-≃
     (λ (p , _ , i) → Id-informs-everything p
                    , informs-is-prop (Identity X) p i)
```

We can also define a trivial equivalence relation that identifies
everything.

```agda
Trivial : {𝓥 𝓤 : Universe} (X : 𝓤 ̇ ) → equivalence-relation {𝓥} {𝓤} X
equivalence-relation._≣_     (Trivial X)           = λ _ _ → 𝟙
equivalence-relation.≣-refl  (Trivial X) x         = ⋆
equivalence-relation.≣-sym   (Trivial X) x y   _   = ⋆ 
equivalence-relation.≣-trans (Trivial X) x y z _ _ = ⋆ 
```

The trivial predicate that satisfies everything, and the empty
predicate that satisfies nothing, is informed by the trivial
equivalence relation.

```agda
trivial-predicate : {𝓦 𝓤 : Universe} → (X : 𝓤 ̇ )
                  → decidable-predicate {𝓦} X
trivial-predicate X = (λ x → 𝟙) , (λ x → inl ⋆)    , (λ x → 𝟙-is-prop)

empty-predicate : {𝓦 𝓤 : Universe} → (X : 𝓤 ̇ )
                → decidable-predicate {𝓦} X
empty-predicate   X = (λ x → 𝟘) , (λ x → inr λ ()) , (λ x → 𝟘-is-prop)

Trivial-informs-trivial : {𝓦 𝓥 𝓤 : Universe} {X : 𝓤 ̇ }
                        → (Trivial {𝓥} X) informs (λ x → 𝟙 {𝓦})
Trivial-informs-trivial _ _ _ _ = ⋆

Trivial-informs-empty : {𝓦 𝓥 𝓤 : Universe} {X : 𝓤 ̇ }
                        → (Trivial {𝓥} X) informs (λ x → 𝟘 {𝓦})
Trivial-informs-empty _ _ _ ()
```

In fact, these are the *only* predicates informed by the trivial
equivalence relation.

```agda
use-propext : {𝓦 𝓤 : Universe} {X : 𝓤 ̇ }
            → (p p' : X → 𝓦 ̇ )
            → everywhere-prop-valued p
            → everywhere-prop-valued p'
            → ((x : X) → p x ⇔ p' x)
            → p ≡ p'
use-propext {𝓦} p p' i i' γ
 = dfunext (fe _ _) (λ x → pe 𝓦 (i x) (i' x) (pr₁ (γ x)) (pr₂ (γ x)))

¬-is-prop : {X : 𝓤 ̇ } → is-prop (¬ X)
¬-is-prop = Π-is-prop (fe _ _) (λ _ → 𝟘-is-prop)

everywhere-decidable-is-prop : {𝓦 𝓤 : Universe} {X : 𝓤 ̇ }
                             → (p : X → 𝓦 ̇ )
                             → everywhere-prop-valued p
                             → is-prop (everywhere-decidable p)
everywhere-decidable-is-prop p i
 = Π-is-prop (fe _ _)
     (λ x → +-is-prop (i x) ¬-is-prop (λ px ¬px → ¬px px))

is-prop-is-prop : {X : 𝓤 ̇ } → is-prop X → is-prop (is-prop X)
is-prop-is-prop i
 = Π-is-prop (fe _ _)
     (λ _ → Π-is-prop (fe _ _) (λ _ → props-are-sets i))

everywhere-prop-valued-is-prop : {𝓦 𝓤 : Universe} {X : 𝓤 ̇ }
                               → (p : X → 𝓦 ̇ )
                               → everywhere-prop-valued p
                               → is-prop (everywhere-prop-valued p)
everywhere-prop-valued-is-prop p i
 = Π-is-prop (fe _ _) (λ x → is-prop-is-prop (i x))

decidable-predicate-≡
 : {𝓦 𝓤 : Universe} {X : 𝓤 ̇ }
 → ((p , d , i) (p' , d' , i') : decidable-predicate {𝓦} X)
 → ((x : X) → p x ⇔ p' x)
 → (p , d , i) ≡ (p' , d' , i')
decidable-predicate-≡ (p , d , i) (p' , d' , i') γ
 = to-subtype-≡
     (λ p (pd , pi) (pd' , pi')
      → ×-is-prop
          (everywhere-decidable-is-prop p pi)
          (everywhere-prop-valued-is-prop p pi)
          (pd , pi) (pd' , pi'))
     (use-propext p p' i i' γ)

is-prop-trivial : {𝓦 𝓥 𝓤 : Universe} {X : 𝓤 ̇ }
                → (p : decidable-predicate {𝓦} X)
                → (Trivial {𝓥} X) informs (pr₁ p)
                → (x : X)
                → (p ≡ trivial-predicate {𝓦} X)
                + (p ≡   empty-predicate {𝓦} X)
is-prop-trivial {𝓦} {𝓥} {𝓤} {X} (p , d , i) η x
 = Cases (d x)
     (λ  px → inl (decidable-predicate-≡
                     (p , d , i) (trivial-predicate X)
                     (λ y → (λ _ → ⋆) , (λ _ → η x y ⋆ px))))
     (λ ¬px → inr (decidable-predicate-≡
                    (p , d , i) (empty-predicate X)
                    (λ y → (λ py → 𝟘-elim (¬px (η y x ⋆ py))) , λ ())))
```

So quotienting a universe of predicates on X by identity does nothing,
and doing so by the trivial equivalence relation removes every
non-constant predicate.

Let's look at some other equivalence relations and see what predicates
fall out of the quotienting.

So-called 'continuous' predicates as defined by closeness functions
are informed by a particular equivalence relation.

First, recall our definition of closeness functions.

```agda
record closeness-function (X : 𝓤 ̇ ) : 𝓤 ̇ where
  field
    c : X × X → ℕ∞ 
    eic : (x     : X) → c (x , x) ≡ ∞
    ice : (x y   : X) → c (x , y) ≡ ∞ → x ≡ y
    sym : (x y   : X) → c (x , y) ≡ c (y , x)
    ult : (x y z : X) → min (c (x , y)) (c (y , z)) ≼ c (x , z)

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
 = transport ((δ ↑) ≼_) (eic x ⁻¹) (∞-maximal (δ ↑))
 where open closeness-function C
equivalence-relation.≣-sym   (δ -Close-via C) x y
 = transport ((δ ↑) ≼_) (sym x y)
 where open closeness-function C
equivalence-relation.≣-trans (δ -Close-via C) x y z δ≼cxy δ≼cyz
 = ≼-trans (δ ↑) (min (c (x , y)) (c (y , z))) (c (x , z))
     (≼-min (δ ↑) (c (x , y)) (c (y , z)) δ≼cxy δ≼cyz)
     (ult x y z)
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

0 information literally gives us zero information -- equiv to trivial
equivalence relation.

```agda

0-info' : {𝓥 𝓤 : Universe} {X : 𝓤 ̇ }
        → (C : closeness-function X)
        → (x y : X)
        → let _≣₁_ = equivalence-relation._≣_ (0 -Close-via C) in
          let _≣₂_ = equivalence-relation._≣_ (Trivial {𝓥} X) in
          (x ≣₁ y) ⇔ (x ≣₂ y)
0-info' C x y = (λ _ → ⋆) , (λ _ x ())

eq-close : {𝓥 𝓤 : Universe} {X : 𝓤 ̇ }
        → (A B : equivalence-relation {𝓥} X)
        → ((x y : X) → equivalence-relation._≣_ A x y
                     ⇔ equivalence-relation._≣_ B x y)
        → (p : X → 𝓦 ̇ )
        → (A informs p)
        ⇔ (B informs p)
eq-close A B γ p = (λ Ap x y Bxy → Ap x y (pr₂ (γ x y) Bxy))
                 , (λ Bp x y Axy → Bp x y (pr₁ (γ x y) Axy))
        
0-info : {𝓦 𝓤 : Universe} {X : 𝓤 ̇ }
       → (C : closeness-function X)
       → (p : X → 𝓦 ̇ )
       → ((0 -Close-via C) informs p)
       ≃ ((Trivial {𝓦} X) informs p)
0-info C p = f , (g , fg) , (g , gf)
 where
   f : _ → _
   f ϕ x y _ = ϕ x y (λ _ ())
   g : _ → _
   g ϕ x y _ = ϕ x y ⋆
   fg : f ∘ g ∼ id
   fg ϕ = dfunext (fe _ _) (λ _ → dfunext (fe _ _)
          (λ _ → dfunext (fe _ _) (λ _ → {!!})))
   gf : g ∘ f ∼ id
   gf ϕ = {!!}
```

information is transitive

```agda

```

If the underlying type X is discrete, every decidable predicate is
trivially continuous with any modulus of continuity using the discrete
sequence closeness function.

```agda
d-closeness : {X : 𝓤 ̇ } → is-discrete X → closeness-function X
closeness-function.c   (d-closeness ds) = discrete-clofun ds
closeness-function.eic (d-closeness ds) = equal→inf-close
 where open is-clofun (discrete-is-clofun ds)
closeness-function.ice (d-closeness ds) = inf-close→equal
 where open is-clofun (discrete-is-clofun ds)
closeness-function.sym (d-closeness ds) = symmetricity
 where open is-clofun (discrete-is-clofun ds)
closeness-function.ult (d-closeness ds) = ultrametric
 where open is-clofun (discrete-is-clofun ds)

close-informs-discrete : {𝓦 𝓤 : Universe} {X : 𝓤 ̇ }
                       → (ds : is-discrete X)
                       → (p : X → 𝓦 ̇ )
                       → (n : ℕ)
                       → (succ n -Close-via d-closeness ds) informs p
close-informs-discrete ds p n x y sn≼cxy
 = transport p (γ (ds x y) sn≼cxy)
 where
   open closeness-function (d-closeness ds)
   γ : (q : decidable (x ≡ y)) → (succ n ↑) ≼ discrete-c' (x , y) q
     → x ≡ y
   γ (inl  x≡y) _ = x≡y
   γ (inr ¬x≡y) r = 𝟘-elim (zero-is-not-one (r 0 refl))



```
