Martin Escardo, 11th September 2018
Reworked and rewritten by Todd Waugh Ambridge, February 2022

A closeness function is a binary function

  c : X × X → ℕ∞

such that

  c (x , y) ≡ ∞ ⇔ x ≡ y.

That is, two points are equal iff they are infinitely close.  If we
have c (x , y) ≡ n ↑ for n : ℕ, the intuition is that x and y can be
distinguished by a finite amount of information of size n.

We discuss further codistance axioms, and then define the canonical
closeness function for:
 * All discrete types D,
 * All discrete-sequence types ℕ → D where D is discrete,
 * ℕ∞ itself.

Furthermore, we show that types equipped with closeness functions
are closed under countable (ℕ-indexed) products; i.e. we define
a closeness function of type Π T × Π T → ℕ∞ where T : ℕ → 𝓤 and
every T n has a closeness function.


\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-FunExt
open import GenericConvergentSequence hiding (min)
open import CoNaturals
open import DiscreteAndSeparated
open import OrderNotation
open import CanonicalMapNotation
open import Two-Properties

module Closeness2 (fe : FunExt) where

open import CoNaturalsArithmetic fe

\end{code}


\begin{code}
record is-clofun {X : 𝓤 ̇ } (c : X × X → ℕ∞) : 𝓤 ̇ where
  field
    equal→inf-close : (x     : X) → c (x , x) ≡ ∞
    inf-close→equal : (x y   : X) → c (x , y) ≡ ∞ → x ≡ y
    symmetricity    : (x y   : X) → c (x , y) ≡ c (y , x)
    ultrametric     : (x y z : X) → min (c (x , y) , c (y , z)) ≼ℕ∞ c (x , z)
\end{code}

The closeness function for a discrete type is defined easily by cases:
                  
    c (x , y) ≡   ∞    if x ≡ y
                  0 ↑  otherwise

\begin{code}
discrete-c' : {X : 𝓤 ̇ } → ((x , y) : X × X) → decidable (x ≡ y) → ℕ∞
discrete-c' (x , y) (inl x≡y) = ∞
discrete-c' (x , y) (inr x≢y) = ι 0

discrete-clofun : {X : 𝓤 ̇ } → is-discrete X → (X × X → ℕ∞)
discrete-clofun d (x , y) = discrete-c' (x , y) (d x y)
\end{code}

Note that we use the helper function `discrete-c'`. This is to allow
the Terminal synthesizer to recognise when a given construction of the
type `decidable (x ≡ y)` (for some `x,y : X`) is constructed as `inl x≡y`
(where `x≡y : x ≡ y`) or `inr x≢y` (where `x≢y : ¬ (x ≡ y)`).

Using the synthesizer in this way allows us to easily prove the four
closeness function properties for the helper function, just using
pattern matching on the given construction of `decidable (x ≡ y)`.

\begin{code}
discrete-c'-eic : {X : 𝓤 ̇ } → (x : X)
                → (dxx : decidable (x ≡ x))
                → discrete-c' (x , x) dxx ≡ ∞
discrete-c'-eic x (inl x≡x) = refl
discrete-c'-eic x (inr x≢x) = 𝟘-elim (x≢x refl)

discrete-c'-ice : {X : 𝓤 ̇ } → (x y : X)
                      → (dxy : decidable (x ≡ y))
                      → discrete-c' (x , y) dxy ≡ ∞ → x ≡ y
discrete-c'-ice x y (inl x≡y) cxy≡∞ = x≡y
discrete-c'-ice x y (inr x≢y) cxy≡∞ = 𝟘-elim (Zero-not-∞ cxy≡∞)
 where
   Zero-not-∞ : ι 0 ≢ ∞
   Zero-not-∞ 0≡∞ = 𝟘-elim (zero-is-not-one (ap (λ - → pr₁ - 0) 0≡∞))
                                 
discrete-c'-sym : {X : 𝓤 ̇ } → (x y : X)
                → (dxy : decidable (x ≡ y))
                → (dyx : decidable (y ≡ x))
                → discrete-c' (x , y) dxy ≡ discrete-c' (y , x) dyx
discrete-c'-sym x y (inl x≡y) (inl y≡x) = refl
discrete-c'-sym x y (inr x≢y) (inr y≢x) = refl
discrete-c'-sym x y (inl x≡y) (inr y≢x) = 𝟘-elim (y≢x (x≡y ⁻¹))
discrete-c'-sym x y (inr x≢y) (inl y≡x) = 𝟘-elim (x≢y (y≡x ⁻¹))

discrete-c'-ult : {X : 𝓤 ̇ } → (x y z : X)
                → (dxy : decidable (x ≡ y))
                → (dyz : decidable (y ≡ z))
                → (dxz : decidable (x ≡ z))
                → min (discrete-c' (x , y) dxy) (discrete-c' (y , z) dyz)
                     ≼ℕ∞ discrete-c' (x , z) dxz
discrete-c'-ult x  y  z       _          _    (inl x≡z ) _ _ = refl
discrete-c'-ult x  y  z (inl x≡y ) (inr y≢z ) (inr x≢z ) _   = id
discrete-c'-ult x  y  z (inr x≢y )       _    (inr x≢z ) _   = id
discrete-c'-ult x .x .x (inl refl) (inl refl) (inr x≢x )     = 𝟘-elim (x≢x refl)
\end{code}

We can now easily prove that any discrete type has a closeness function
that satisfies the necessary properties.

```terminal
discrete-is-clofun : {X : 𝓤 ̇ } → (ds : is-discrete X)
                       → is-clofun (discrete-clofun ds)
is-clofun.equal→inf-close (discrete-is-clofun ds) x
 = discrete-c'-eic x      (ds x x)
is-clofun.inf-close→equal (discrete-is-clofun ds) x y
 = discrete-c'-ice x y    (ds x y)
is-clofun.symmetricity    (discrete-is-clofun ds) x y
 = discrete-c'-sym x y    (ds x y) (ds y x)
is-clofun.ultrametric     (discrete-is-clofun ds) x y z
 = discrete-c'-ult x y z  (ds x y) (ds y z) (ds x z)
```

## Discrete-sequence closeness function <a name="discrete-seq"></a>

The closeness function for a type `(ℕ → X)` where `X` is discrete is defined
pointwise by cases as follows:

    c (α , β) n ≡ ₁,    if x ≡⟦ n ⟧ y,
                  ₀,    otherwise.

We again want to use a helper function to allow us to prove properties
using the Terminal synthesizer just by using pattern matching on the type
`decidable (α ̄≡⟦ n ⟧ β)`.

To do this we first prove the following lemma.

```terminal
discrete-decidable-seq : {X : 𝓤 ̇ } → is-discrete X
                       → (α β : ℕ → X) → (n : ℕ) → decidable (α ≡⟦ n ⟧ β)
discrete-decidable-seq d α β 0 = Cases (d (α 0) (β 0)) (inl ∘ γₗ) (inr ∘ γᵣ)
 where
   γₗ :    α 0 ≡ β 0  →    α ≡⟦ 0 ⟧ β
   γₗ e 0 _ = e
   γᵣ : ¬ (α 0 ≡ β 0) → ¬ (α ≡⟦ 0 ⟧ β)
   γᵣ f α≡⟦0⟧β = 𝟘-elim (f (α≡⟦0⟧β 0 ⋆))
discrete-decidable-seq d α β (succ n)
 = Cases (discrete-decidable-seq d α β n) γ₁ (inr ∘ γ₂)
 where
   γ₁ : α ≡⟦ n ⟧ β → decidable (α ≡⟦ succ n ⟧ β)
   γ₁ α≈β = Cases (d (α (succ n)) (β (succ n))) (inl ∘ γₗ) (inr ∘ γᵣ)
    where
      γₗ :     α (succ n) ≡ β (succ n) →    α ≡⟦ succ n ⟧ β
      γₗ e k k≤n = Cases (≤-split k n k≤n)
                     (λ k≤n  → α≈β k k≤n)
                     (λ k≡sn → transport (λ - → α - ≡ β -) (k≡sn ⁻¹) e)
      γᵣ : ¬ (α (succ n) ≡ β (succ n)) → ¬ (α ≡⟦ succ n ⟧ β)
      γᵣ g α≡⟦sn⟧β = g (α≡⟦sn⟧β (succ n) (≤-refl n))
   γ₂ : ¬ (α ≡⟦ n ⟧ β) → ¬ (α ≡⟦ succ n ⟧ β)
   γ₂ f = f ∘ (λ α≈β k k≤n → α≈β k (≤-trans k n (succ n) k≤n (≤-succ n)))
```

We now define the closeness function using a helper function.

```terminal
discrete-seq-c' : {X : 𝓤 ̇ } → ((α , β) : (ℕ → X) × (ℕ → X))
                 → (n : ℕ) → decidable (α ≡⟦ n ⟧ β) → 𝟚
discrete-seq-c' (α , β) n (inl α≡⟦n⟧β) = ₁
discrete-seq-c' (α , β) n (inr α≡⟦n⟧β) = ₀

discrete-seq-c'-dec : {X : 𝓤 ̇ } → ((α , β) : (ℕ → X) × (ℕ → X))
                    → (n : ℕ) → (d₁ : decidable (α ≡⟦      n ⟧ β))
                                (d₂ : decidable (α ≡⟦ succ n ⟧ β))
                    → (discrete-seq-c' (α , β) n d₁ ≥₂ discrete-seq-c' (α , β) (succ n) d₂)
discrete-seq-c'-dec (α , β) n (inl  α≡⟦n⟧β) (inl  α≡⟦sn⟧β) _ = refl
discrete-seq-c'-dec (α , β) n (inl  α≡⟦n⟧β) (inr ¬α≡⟦sn⟧β) _ = refl
discrete-seq-c'-dec (α , β) n (inr ¬α≡⟦n⟧β) (inl  α≡⟦sn⟧β) refl
 = 𝟘-elim (¬α≡⟦n⟧β (λ k k<n → α≡⟦sn⟧β k (≤-trans k n (succ n) k<n (≤-succ n))))
discrete-seq-c'-dec (α , β) n (inr ¬α≡⟦n⟧β) (inr ¬α≡⟦sn⟧β) = 𝟘-elim ∘ zero-is-not-one

discrete-seq-clofun : {X : 𝓤 ̇ } → is-discrete X → ((ℕ → X) × (ℕ → X) → ℕ∞)
discrete-seq-clofun ds (α , β)
 = (λ n → discrete-seq-c'     (α , β) n (discrete-decidable-seq ds α β       n))
 , (λ n → discrete-seq-c'-dec (α , β) n (discrete-decidable-seq ds α β       n)
                                        (discrete-decidable-seq ds α β (succ n)))
```

In order to show that the discrete-sequence closeness function satisfies the four
necessary properties, we first need a way to show that two extended naturals are equal.

Of course, by function extensionality, two sequences `α,β : ℕ → X` are equal `α ≡ β`
if they are equivalent `α ∼ β ≔ Π i ꞉ ℕ , (α i ≡ β i)`.

```terminal
seq-equals : {X : 𝓤 ̇ } {α β : ℕ → X} → α ∼ β → α ≡ β
seq-equals α∼β = fe α∼β
```

However, recall that an extended natural consists of both a binary sequence and a
proof that the sequence is descending.

Therefore, in order to show that, for `(α , α-dec),(β , β-dec) : ℕ∞`,
`(α , α-dec) ≡ (β , β-dec)` we need to construct objects of types:

 1. `α     ≡ β`,     for `α,β : ℕ → 𝟚`,
 
 2. `α-dec ≡ β-dec`, for `α-dec : decreasing-binary-seq α` and, by **1.**,
                         `β-dec : decreasing-binary-seq α`.

Constructing an element of **2.** is non-trivial; but, it is a subsingleton.

In homotopy type theory, a type `X` is called a 'prop' or a 'subsingleton' if,
for any `x,y : X`, `x ≡ x`. This means that the type has at most one element.

```terminal
is-subsingleton : 𝓤 ̇ → 𝓤 ̇
is-subsingleton X = (x y : X) → x ≡ y
```

Given a type family `Y : X → 𝓤` ̇ if, for all `x : X`, `Y x` is a subsingleton,
then `Π Y` is also a subsingleton.

```terminal
Π-is-subsingleton : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
                  → ((x : X) → is-subsingleton (Y x))
                             → is-subsingleton (Π Y)
Π-is-subsingleton Y-is-prop f g = fe (λ x → Y-is-prop x (f x) (g x))
```

A type `X` is called a 'set' if, for any `x,y : X`, the type `x ≡ y` is a subsingleton.

```terminal
is-set : 𝓤 ̇ → 𝓤 ̇
is-set X = (x y : X) → is-subsingleton (x ≡ y)
```

`𝟚` is a set, and thus the relation `_≥₂_` is prop-valued. This allows us to prove
that the type decreasing-binary-seq α, for any `α : ℕ → 𝟚`, is a prop —
thus allowing us to construct **2.**.

```terminal
𝟚-is-set : is-set 𝟚
𝟚-is-set ₀ ₀ refl refl = refl
𝟚-is-set ₁ ₁ refl refl = refl

≥₂-is-prop : (a b : 𝟚) → is-subsingleton (a ≥₂ b)
≥₂-is-prop a b = Π-is-subsingleton (λ _ → 𝟚-is-set a ₁)

decreasing-prop : (α : ℕ → 𝟚) → is-subsingleton (decreasing-binary-seq α)
decreasing-prop α = Π-is-subsingleton (λ n → ≥₂-is-prop (α n) (α (succ n)))

sigma-prop-equals : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
                  → {(x₁ , y₁) (x₂ , y₂) : Σ x ꞉ X , Y x}
                  → x₁ ≡ x₂
                  → ((x : X) → is-subsingleton (Y x))
                  → (x₁ , y₁) ≡ (x₂ , y₂)
sigma-prop-equals {𝓤} {𝓥} {X} {Y} {(x₁ , Yx₁)} {(.x₁ , Yx₂)} refl Y-is-prop
 = ap (x₁ ,_) (Y-is-prop x₁ Yx₁ Yx₂)

ℕ∞-equals : {(α , α-dec) (β , β-dec) : ℕ∞} → α ∼ β → (α , α-dec) ≡ (β , β-dec)
ℕ∞-equals α∼β = sigma-prop-equals (fe α∼β) decreasing-prop
```

We now prove the four necessary properties using the helper function...

```terminal
discrete-seq-c'-eic : {X : 𝓤 ̇ } → (α : ℕ → X)
                     → (n : ℕ) → (d : decidable (α ≡⟦ n ⟧ α))
                     → discrete-seq-c' (α , α) n d ≡ ₁
discrete-seq-c'-eic α n (inl  α≡⟦n⟧α) = refl
discrete-seq-c'-eic α n (inr ¬α≡⟦n⟧α) = 𝟘-elim (¬α≡⟦n⟧α (λ k k≤n → refl))

discrete-seq-c'-ice : {X : 𝓤 ̇ } → (α β : ℕ → X)
                     → (n : ℕ) → (d : decidable (α ≡⟦ n ⟧ β))
                     → discrete-seq-c' (α , β) n d ≡ ₁
                     → α n ≡ β n
discrete-seq-c'-ice α β n (inl  α≡⟦n⟧β) cαβn≡₁ = α≡⟦n⟧β n (≤-refl n)
discrete-seq-c'-ice α β n (inr ¬α≡⟦n⟧β) ()

discrete-seq-c'-sym : {X : 𝓤 ̇ } (α β : ℕ → X)
                     → (n : ℕ) → (d₁ : decidable (α ≡⟦ n ⟧ β))
                                 (d₂ : decidable (β ≡⟦ n ⟧ α))
                     → discrete-seq-c' (α , β) n d₁ ≡ discrete-seq-c' (β , α) n d₂
discrete-seq-c'-sym x y n (inl  α≡⟦n⟧β) (inl  β≡⟦n⟧α) = refl
discrete-seq-c'-sym x y n (inr ¬α≡⟦n⟧β) (inr ¬β≡⟦n⟧α) = refl
discrete-seq-c'-sym x y n (inl  α≡⟦n⟧β) (inr ¬β≡⟦n⟧α)
 = 𝟘-elim (¬β≡⟦n⟧α (λ k k<n → α≡⟦n⟧β k k<n ⁻¹))
discrete-seq-c'-sym x y n (inr ¬α≡⟦n⟧β) (inl  β≡⟦n⟧α)
 = 𝟘-elim (¬α≡⟦n⟧β (λ k k<n → β≡⟦n⟧α k k<n ⁻¹))

discrete-seq-c'-ult : {X : 𝓤 ̇ } (α β η : ℕ → X)
                     → (n : ℕ) → (d₁ : decidable (α ≡⟦ n ⟧ β))
                               → (d₂ : decidable (β ≡⟦ n ⟧ η))
                               → (d₃ : decidable (α ≡⟦ n ⟧ η))
                     → min𝟚 (discrete-seq-c' (α , β) n d₁)
                            (discrete-seq-c' (β , η) n d₂) ≡ ₁
                     → discrete-seq-c' (α , η) n d₃ ≡ ₁
discrete-seq-c'-ult α β η n _             _             (inl  α≡⟦n⟧η) _ = refl
discrete-seq-c'-ult α β η n (inl α≡⟦n⟧β)  (inl  β≡⟦n⟧η) (inr ¬α≡⟦n⟧η) min≡₁
 = 𝟘-elim (¬α≡⟦n⟧η (λ k k<n → α≡⟦n⟧β k k<n ∙ β≡⟦n⟧η k k<n))
discrete-seq-c'-ult α β η n (inl  α≡⟦n⟧β) (inr ¬β≡⟦n⟧α) (inr ¬α≡⟦n⟧η) min₁₀≡₁
 = 𝟘-elim (zero-is-not-one min₁₀≡₁)
discrete-seq-c'-ult α β η n (inr ¬α≡⟦n⟧β) (inl  β≡⟦n⟧α) (inr ¬α≡⟦n⟧η) min₀₁≡₁
 = 𝟘-elim (zero-is-not-one min₀₁≡₁)
discrete-seq-c'-ult α β η n (inr ¬α≡⟦n⟧β) (inr ¬β≡⟦n⟧α) (inr ¬α≡⟦n⟧η) min₀₀≡₁
 = 𝟘-elim (zero-is-not-one min₀₀≡₁)
```

...and this allows us to show that the discrete-sequence closeness function
satisfies the four necessary properties.


```terminal
discrete-seq-is-clofun : {X : 𝓤 ̇ } → (ds : is-discrete X)
                           → is-clofun (discrete-seq-clofun ds)
is-clofun.equal→inf-close (discrete-seq-is-clofun ds) α
 = ℕ∞-equals (λ n → discrete-seq-c'-eic α n (discrete-decidable-seq ds α α n))
is-clofun.inf-close→equal (discrete-seq-is-clofun ds) α β cαβ≡∞
 = fe (λ n → discrete-seq-c'-ice α β n (discrete-decidable-seq ds α β n) (γ n))
 where
   γ : (n : ℕ) → discrete-seq-c' (α , β) n (discrete-decidable-seq ds α β n) ≡ ₁
   γ n = ap (λ - → pr₁ - n) cαβ≡∞
is-clofun.symmetricity    (discrete-seq-is-clofun ds) α β
 = ℕ∞-equals (λ n → discrete-seq-c'-sym α β n (discrete-decidable-seq ds α β n)
                                              (discrete-decidable-seq ds β α n))
is-clofun.ultrametric     (discrete-seq-is-clofun ds) α β η
 = λ n → discrete-seq-c'-ult α β η n (discrete-decidable-seq ds α β n)
                                     (discrete-decidable-seq ds β η n)
                                     (discrete-decidable-seq ds α η n)
```

We quickly note two corollaries needed for our main result.

Firstly, there is an obvious relationship between the closeness value
`c (α , β) : ℕ∞` and the equality of a prefix of `α` and `β`.

(Exercises for the reader:)

```terminal
closeness→equality : {X : 𝓤 ̇ } → (ds : is-discrete X)
                   → (α β : ℕ → X) → (n : ℕ)
                   → (succ n ↑) ≼ discrete-seq-clofun ds (α , β)
                   → α ≡⟦ n ⟧ β
closeness→equality ds α β n cαβ≼n
 = γ (discrete-decidable-seq ds α β n) (cαβ≼n n (all-n n))
 where
   γ : (d : decidable (α ≡⟦ n ⟧ β)) → discrete-seq-c' (α , β) n d ≡ ₁ → α ≡⟦ n ⟧ β
   γ (inl α≡⟦n⟧β) _ = α≡⟦n⟧β
   all-n : (n : ℕ) → pr₁ (succ n ↑) n ≡ ₁
   all-n 0        = refl
   all-n (succ n) = all-n n

equality→closeness : {X : 𝓤 ̇ } → (ds : is-discrete X)
                   → (α β : ℕ → X) → (n : ℕ)
                   → α ≡⟦ n ⟧ β
                   → (succ n ↑) ≼ discrete-seq-clofun ds (α , β)
equality→closeness ds α β n α≡⟦n⟧β k nₖ≡₁
 = γ (discrete-decidable-seq ds α β k)
 where
   n≼ : (k n : ℕ) → pr₁ (n ↑) k ≡ ₁ → k <ℕ n
   n≼ 0        (succ n) nₖ≡₁ = ⋆
   n≼ (succ k) (succ n) nₖ≡₁ = n≼ k n nₖ≡₁
   γ : (d : decidable (α ≡⟦ k ⟧ β)) → discrete-seq-c' (α , β) k d ≡ ₁
   γ (inl  α≡⟦k⟧β) = refl
   γ (inr ¬α≡⟦k⟧β)
    = 𝟘-elim (¬α≡⟦k⟧β (λ i i≤k → α≡⟦n⟧β i (≤-trans i k n i≤k (n≼ k (succ n) nₖ≡₁))))
```

This relationship helps us to show that,

      if (     δ ↑) ≼ c (α , β)
    then (succ δ ↑) ≼ c (x :: α , x :: β).

```terminal
build-up : {X : 𝓤 ̇ } → (ds : is-discrete X) → (xs ys : ℕ → X) → (δ : ℕ)
         → (δ ↑) ≼ discrete-seq-clofun ds (xs , ys)
         → (x : X)
         → (succ δ ↑) ≼ discrete-seq-clofun ds (x :: xs , x :: ys)
build-up {𝓤} {X} ds xs ys δ δ≼cxsys x
 = equality→closeness ds (x :: xs) (x :: ys) δ (γ δ δ≼cxsys)
 where
   γ : (δ : ℕ) → (δ ↑) ≼ discrete-seq-clofun ds (xs , ys)
     → (x :: xs) ≡⟦ δ ⟧ (x :: ys)
   γ δ δ≼cxsys 0        *   = refl
   γ (succ δ) δ≼cxsys (succ k) k≤n = closeness→equality ds xs ys δ δ≼cxsys k k≤n
```

Secondly, by function extensionality, `α ≡ (head α :: tail α)`.

```terminal
head : {X : 𝓤 ̇ } → (ℕ → X) → X
head α   = α 0

tail : {X : 𝓤 ̇ } → (ℕ → X) → (ℕ → X)
tail α n = α (succ n)

head-tail-eta : {X : 𝓤 ̇ } → (α : ℕ → X) → α ≡ head α :: (tail α)
head-tail-eta α = fe γ where
  γ : α ∼ head α :: (tail α)
  γ 0 = refl
  γ (succ n) = refl
```

## Continuity and continuously searchable types <a name="continuity"></a>

Now that we have two examples of closeness functions, we show how they can
be used to give a definition of uniform continuity that is related to the
usual ε-δ definition on metric spaces.

A predicate `p : predicate X` on a type `X` with closeness function `c : X × X → ℕ∞`
is uniformly continuous if there is some `δ : ℕ` such that, for any `x,y : X` with
`(δ ↑) ≼ c (x , y)`, `p(y)` is inhabited if and only if `p(x)` is.

We call `δ` the uniform modulus of `p` on `c`.

```terminal
_is-u-mod-of_on_ : {X : 𝓤 ̇ } → ℕ → predicate X → (X × X → ℕ∞) → 𝓤 ̇ 
_is-u-mod-of_on_ {𝓤} {X} δ p c = Π (x , y) ꞉ (X × X) , ((δ ↑) ≼ c (x , y) → p x → p y)

u-continuous : {X : 𝓤 ̇ } → (X × X → ℕ∞) → predicate X → 𝓤 ̇
u-continuous {𝓤} {X} c p = Σ δ ꞉ ℕ , δ is-u-mod-of p on c
```

This allows us to define the notion of 'continuously searchable' types.
These are types `X` with a closeness function `c : X × X → ℕ∞` that allow us
to search any uniformly continuous decidable predicate on `X`.

```terminal
uc-d-predicate : (X : 𝓤 ̇ ) → (X × X → ℕ∞) → (𝓤₀ ⁺) ⊔ 𝓤 ̇
uc-d-predicate X c = Σ (p , d) ꞉ d-predicate X , u-continuous c p

c-searchable : (X : 𝓤 ̇ ) → (X × X → ℕ∞) → (𝓤₀ ⁺) ⊔ 𝓤 ̇
c-searchable X c = Π ((p , _)  , _) ꞉ uc-d-predicate X c , Σ x₀ ꞉ X , (Σ p → p x₀)
```

Of course, any searchable type is trivially continuously searchable on any
closeness function.

For example, `𝟚` is continuously searchable using the discrete closeness function.

```terminal
c-searchable-types-are-inhabited : {X : 𝓤 ̇ } → (c : X × X → ℕ∞) → c-searchable X c → X
c-searchable-types-are-inhabited {𝓤} {X} c S = pr₁ (S trivial-predicate)
 where
   trivial-predicate : uc-d-predicate X c
   trivial-predicate = ((λ x → 𝟙) , (λ x → inl ⋆)) , (0 , λ x y _ → ⋆)

searchable→c-searchable : {X : 𝓤 ̇ } → (c : X × X → ℕ∞) → searchable X → c-searchable X c
searchable→c-searchable c S ((p , d) , δ , ϕ) = S (p , d)

𝟚-is-discrete : is-discrete 𝟚
𝟚-is-discrete ₀ ₀ = inl refl
𝟚-is-discrete ₁ ₁ = inl refl
𝟚-is-discrete ₀ ₁ = inr (λ ())
𝟚-is-discrete ₁ ₀ = inr (λ ())

𝟚-is-c-searchable : c-searchable 𝟚 (discrete-clofun 𝟚-is-discrete)
𝟚-is-c-searchable
 = searchable→c-searchable (discrete-clofun 𝟚-is-discrete) 𝟚-is-searchable
```

Conversely, any discrete type that is continuously searchable by the discrete
closeness function is also searchable: this is because all predicates on discrete
types are uniformly continuous by this closenss function.

```terminal
all-discrete-predicates-are-continuous
 : {X : 𝓤 ̇ } → (ds : is-discrete X) → d-predicate X
 → uc-d-predicate X (discrete-clofun ds)
all-discrete-predicates-are-continuous {𝓤} {X} ds (p , d)
 = (p , d) , (1 , λ (x , y) → γ x y (ds x y))
 where
   γ : (x y : X) → (q : decidable (x ≡ y)) → (1 ↑) ≼ discrete-c' (x , y) q → p x → p y
   γ x .x (inl refl) 1≼∞ px = px
   γ x  y (inr  _  ) 1≼0 _  = 𝟘-elim (zero-is-not-one (1≼0 0 refl))

c-searchable-discrete→searchable : {X : 𝓤 ̇ } → (ds : is-discrete X)
                                 → c-searchable X (discrete-clofun ds) → searchable X
c-searchable-discrete→searchable ds S (p , d)
 = S (all-discrete-predicates-are-continuous ds (p , d))
```

## Main result <a name="main"></a>

Now we come to the main result for this half.

We wish to show that, for any discrete `X`, `ℕ → X` is continuously searchable
using the discrete-sequence closeness function.

```terminal
→c-searchable : {X : 𝓤 ̇ } → (ds : is-discrete X) → c-searchable X (discrete-clofun ds)
              → c-searchable (ℕ → X) (discrete-seq-clofun ds)
```

The proof here is by induction on the modulus of continuity of the predicate
being searched. In order to convince the Terminal synthesizer that this terminates,
we prove the equivalent statement.

```terminal
→c-searchable' : {X : 𝓤 ̇ } → (ds : is-discrete X) → searchable X
               → ((p , d) : d-predicate (ℕ → X))
               → (δ : ℕ) → δ is-u-mod-of p on (discrete-seq-clofun ds)
               → Σ x₀ ꞉ (ℕ → X) , (Σ p → p x₀)
               
→c-searchable ds S ((p , d) , δ , ϕ)
 = →c-searchable' ds (c-searchable-discrete→searchable ds S) (p , d) δ ϕ
```

The magic of this proof of course comes from continuity — we use two simple lemmas.

**Lemma 1.**

Any uniformly continuous discrete predicate `p : uc-d-predicate X c`, for
any closeness function `c : X × X → ℕ∞`, with modulus of uniform continuity
`0 : ℕ` is satisfied by any construction of `X`.

```terminal
0-mod-always-satisfied : {X : 𝓤 ̇ } → (c : X × X → ℕ∞)
                       → ((p , d) : d-predicate X)
                       → 0 is-u-mod-of p on c
                       → Σ p → Π p 
0-mod-always-satisfied c (p , d) ϕ (x₀ , px₀) x = ϕ (x₀ , x) (λ _ ()) px₀

trivial-predicate : {X : 𝓤 ̇ } → (c : X × X → ℕ∞) → uc-d-predicate X c
trivial-predicate c = ((λ _ → 𝟙) , (λ _ → inl ⋆)) , (0 , λ x y 0≼cxy → ⋆)
```

Lemma 2.

Given any uniformly continuous discrete predicate
`p : uc-d-predicate (ℕ → X) _`, with modulus of uniform continuity
`(succ δ) : ℕ`, we can construct the predicate
`(pₜ x) ≔ (λ xs → x :: xs) : uc-d-predicate (ℕ → X) _`,
for any given `x : X`, which has modulus of uniform continuity `δ : ℕ`.

We call `(pₜ x)` the "`tail-predicate` for `p` via `x`".

```terminal
tail-predicate : {X : 𝓤 ̇ } → (ds : is-discrete X)
               → ((p , d) : d-predicate (ℕ → X))
               → (x : X) → d-predicate (ℕ → X)
tail-predicate ds (p , d) x = (λ xs → p (x :: xs)) , (λ xs → d (x :: xs))

tail-predicate-reduce-mod : {X : 𝓤 ̇ } → (ds : is-discrete X)
                          → ((p , d) : d-predicate (ℕ → X))
                          → (x : X) → (δ : ℕ)
                          → (succ δ) is-u-mod-of p on (discrete-seq-clofun ds)
                          →       δ  is-u-mod-of pr₁ (tail-predicate ds (p , d) x)
                                                   on (discrete-seq-clofun ds)
tail-predicate-reduce-mod {𝓤} {X} ds (p , d) x δ ϕ (xs , ys) δ≼cxsys
 = ϕ (x :: xs , x :: ys) (build-up ds xs ys δ δ≼cxsys x)
```

Given `(pₜ x)` for any `x : X`, we can construct the
"head predicate" `pₕ ≔ (λ x → x :: 𝓔xs x) : d-predicate X` where
`𝓔xs x : ℕ → X` is the sequence that satisfies `(pₜ x)`.

```terminal
head-predicate : {X : 𝓤 ̇ } → (ds : is-discrete X) → searchable X
               → ((p , d) : d-predicate (ℕ → X))
               → (δ : ℕ) → (succ δ) is-u-mod-of p on (discrete-seq-clofun ds)
               → d-predicate X
head-predicate {𝓤} {X} ds S (p , d) δ ϕ
 = ((λ x → p (x :: 𝓔xs x)) , (λ x → d (x :: 𝓔xs x)))
 where
   𝓔xs : X → (ℕ → X)
   𝓔xs x = pr₁ (→c-searchable' ds S (tail-predicate ds (p , d) x)
           δ (tail-predicate-reduce-mod ds (p , d) x δ ϕ))
```

We now construct the searcher for the type `ℕ → X` by induction on
the modulus of continuity of the predicate being searched.

Recall that in both cases we wish to construct some `α : ℕ → X`
such that, if there is `α₀` such that `p(α₀)` then also `p(α)`.

When the modulus of continuity is `0`, by **Lemma 1** we can return
any sequence for α. Because X is searchable, it is inhabited by
some `x : X`, and so we simply set `α ≔ (λ n → x)`.

```terminal
→c-searchable' ds S (p , d) 0        ϕ
 = α , λ (x₀ , px₀) → γ (x₀ , px₀) α
 where
   x = searchable-types-are-inhabited S
   α = λ n → x
   γ : Σ p → Π p
   γ = 0-mod-always-satisfied (discrete-seq-clofun ds) (p , d) ϕ
```

When the modulus of continuity is `(succ δ) : ℕ` for some `δ : ℕ`,
by **Lemma 2** we can construct the `tail-predicate` of `p`, which has
modulus of continuity `δ : ℕ`, via any `x : X` — this predicate
can be searched using the inductive hypothesis.

```terminal
→c-searchable' {𝓤} {X} ds S (p , d) (succ δ) ϕ = α , γ where
  pₕ = pr₁ (head-predicate ds S (p , d) δ ϕ)
  pₜ = λ x' → pr₁ (tail-predicate ds (p , d) x')
```

Therefore, we can now search X for a solution to `pₕ : d-predicate X`,
the `head-predicate` of `p`, and use the inductive hypothesis to search
`ℕ → X` for a solution to `(pₜ x') : uc-d-predicate (ℕ → X) _`, the tail
predicate of `p` via any `x' : X`.

```terminal
  S-head = S (head-predicate ds S (p , d) δ ϕ)

  IH-tail = λ x' → →c-searchable' ds S (tail-predicate ds (p , d) x')
                      δ (tail-predicate-reduce-mod ds (p , d) x' δ ϕ)
```

This gives us two constructions:

 1.  `x  : X` s.t. if there is `x₀` such that `pₕ(x₀)` then also `pₕ(x)`,

```terminal
  x  : X
  x  = pr₁ S-head
  
  γₕ : Σ pₕ → pₕ x
  γₕ = pr₂ S-head
```

 2. `𝓔xs : X → (ℕ → X)` s.t., given any `x' : X`, if there is `xs₀`
                        such that `(pₜ x')(xs₀)` then also `(pₜ x')(𝓔xs x')`.

```terminal
  𝓔xs : X → (ℕ → X)
  𝓔xs x' = pr₁ (IH-tail x')
  γₜ  : (x' : X) → Σ (pₜ x') → (pₜ x') (𝓔xs x') 
  γₜ  x' = pr₂ (IH-tail x')
```

We set `α ≔ (x :: 𝓔xs x)`.
```terminal

  α = x :: 𝓔xs x

  γ : Σ p → p α
  γ (α₀ , pα₀) = step₆ where
```

If there is some `α₀` such that `p(α₀)`, then also (by function
extensionality) `p(x₀ :: xs₀)`, where `x₀ ≔ head α₀` and `xs₀ ≔ tail α₀`.

```terminal
    x₀  = head α₀
    xs₀ = tail α₀
    
    step₁ : p (x₀ :: xs₀)
    step₁ = transport p (head-tail-eta α₀) pα₀
```

Therefore, by definition of `pₜ`, we have `(pₜ x₀)(xs₀)` and further,
by construction of `𝓔xs`, we also have `(pₜ x₀)(𝓔xs x₀)`. 

```terminal
    step₂ : (pₜ x₀) xs₀
    step₂ = step₁
    
    step₃ : (pₜ x₀) (𝓔xs x₀)
    step₃ = γₜ x₀ (xs₀ , step₂)
```

Note that `(pₜ x₀)(𝓔xs x₀) ≡ p(x₀ :: 𝓔xs x₀) ≡ pₕ`.
Therefore, by definition of `pₕ`, we have `pₕ(x₀)` and further,
by construction of `x`, we also have      `pₕ(x)`.

```terminal
    step₄ : pₕ x₀
    step₄ = step₃
    
    step₅ : pₕ x
    step₅ = γₕ (x₀ , step₄)
```

Note that `pₕ(x) ≡ p (x :: 𝓔xs x)`, giving us our conclusion.

```terminal
    step₆ : p (x :: 𝓔xs x)
    step₆ = step₅
```

A corollary to this theorem, of course, is that the Cantor space is
continuously searchable.

```terminal
ℕ→𝟚-is-c-searchable : c-searchable (ℕ → 𝟚) (discrete-seq-clofun 𝟚-is-discrete)
ℕ→𝟚-is-c-searchable = →c-searchable 𝟚-is-discrete 𝟚-is-c-searchable
```

But we still have to prove the full blown Tychonoff theorem using
closeness functions and continuously searchable types.
Have a think about how we can define a closeness function
on an infinite series of types `T : ℕ → 𝓤`, where each `(T n) : 𝓤` has
a closeness function.

Once you've had a think [please click here to read Part II](InfiniteSearch2.html),
where we formalise the Tychonoff theorem for continuously searchable types.
