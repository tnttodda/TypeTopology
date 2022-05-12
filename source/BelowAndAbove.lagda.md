```agda
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

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


```

```
b<a→a≢b : ∀ a b → (b <ℤ a) → a ≢ b
b<a→a≢b a a (n , a<a) refl = γ γ'
 where
   γ' : 0 ≡ succ n
   γ' = pos-lc _ _ (ℤ+-lc _ _ a (a<a ⁻¹ ∙ ℤ-left-succ-pos a n))
   γ : 0 ≢ succ n
   γ ()

ℤ-elim : (P : ℤ → 𝓤 ̇ )
       → ((n : ℕ) → P (pos n)) → ((n : ℕ) → P (negsucc n))
       → Π P
ℤ-elim P Pp Pn (pos     n) = Pp n
ℤ-elim P Pp Pn (negsucc n) = Pn n

succ-to-monotone' : (P : ℤ → ℤ → 𝓤 ̇ )
                  → ((a : ℤ) → P a a)
                  → ((a b c : ℤ) → P a b → P b c → P a c)
                  → ((a : ℤ) → P a (succℤ a))
                  → (a b : ℤ) (n : ℕ) → a +pos n ≡ b → P a b
succ-to-monotone' P r t s a a zero refl = r a
succ-to-monotone' P r t s a b (succ n) refl
 = t a (succℤ a) b (s a)
     (succ-to-monotone' P r t s (succℤ a) (succℤ (a +pos n))
       n (ℤ-left-succ-pos a n))

succ-to-monotone : (P : ℤ → ℤ → 𝓤 ̇ )
                 → ((a : ℤ) → P a a)
                 → ((a b c : ℤ) → P a b → P b c → P a c)
                 → ((a : ℤ) → P a (succℤ a))
                 → (a b : ℤ) → a ≤ℤ b → P a b
succ-to-monotone P r t s a b (n , γ) = succ-to-monotone' P r t s a b n γ

≤-succ-to-monotone : (f : ℤ → ℤ) → ((a : ℤ) → f a ≤ℤ f (succℤ a))
                   → (a b : ℤ) → a ≤ℤ b → f a ≤ℤ f b
≤-succ-to-monotone f = succ-to-monotone (λ x y → f x ≤ℤ f y)
                         (λ x     → ℤ≤-refl  (f x))
                         (λ x y z → ℤ≤-trans (f x) (f y) (f z))
```

downLeft, downMid and downRight

```
downLeft downMid downRight : ℤ → ℤ
downLeft  a = a +ℤ a
downMid   a = succℤ (downLeft a)
downRight a = succℤ (downMid  a)
```

downLeft and downRight properties

```
pred-downMid : (a : ℤ) → predℤ (downMid a) ≡ downLeft a
pred-downMid a = predsuccℤ _

pred-downRight : (a : ℤ) → predℤ (downRight a) ≡ downMid a
pred-downRight a = predsuccℤ _

pred-pred-downRight : (a : ℤ) → predℤ (predℤ (downRight a)) ≡ downLeft a
pred-pred-downRight a = ap predℤ (predsuccℤ _) ∙ predsuccℤ _

downLeft≢downRight : (a b : ℤ) → a ≡ b → downLeft a ≢ downRight a
downLeft≢downRight a a refl dL≡dR = b<a→a≢b _ _ (1 , refl) (dL≡dR ⁻¹)

downLeft-monotone' : (a b : ℤ) → ((n , _) : a ≤ℤ b)
                   → downLeft a +pos (n +ℕ n) ≡ downLeft b
downLeft-monotone' a b (n , refl)
 = ap ((a +ℤ a) +ℤ_) (pos-addition-equiv-to-ℕ n n ⁻¹)
 ∙ ℤ+-rearrangement (a +ℤ a) (pos n) (pos n) ⁻¹
 ∙ ap (λ - → (- +pos n) +pos n) (ℤ+-comm a a)
 ∙ ap (_+pos n)
     (ℤ+-assoc a a (pos n)
     ∙ ap (a +ℤ_) (ℤ+-comm a (pos n))
     ∙ ℤ+-assoc a (pos n) a ⁻¹)
 ∙ ℤ+-assoc (a +pos n) a (pos n)

downLeft<<downRight : (a b : ℤ) → a <ℤ b → downLeft a <ℤ downRight b
downLeft<<downRight a b (n , refl)
 = (succ (succ (succ (n +ℕ n))))
 , ap (succℤ ∘ succℤ)
     (ap succℤ
       (ap (_+pos (n +ℕ n)) (ℤ-left-succ a a ⁻¹)
       ∙ ap ((succℤ a +ℤ a) +ℤ_) (pos-addition-equiv-to-ℕ n n ⁻¹)
       ∙ ℤ+-rearrangement (succℤ a +ℤ a) (pos n) (pos n) ⁻¹
       ∙ ap (λ - → (- +pos n) +pos n) (ℤ+-comm (succℤ a) a)
       ∙ ap (_+pos n)
           (ℤ+-assoc a (succℤ a) (pos n)
         ∙ ap (a +ℤ_) (ℤ+-comm (succℤ a) (pos n))
         ∙ ℤ+-assoc a (pos n) (succℤ a) ⁻¹)
       ∙ ℤ+-assoc (a +pos n) (succℤ a) (pos n))
   ∙ ℤ-left-succ (a +pos n) (succℤ a +pos n) ⁻¹
   ∙ ap (_+ℤ (succℤ a +pos n)) (ℤ-left-succ-pos a n ⁻¹))

downLeft<downRight : (a : ℤ) (n : ℕ)
                   → rec a downLeft (succ n) <ℤ rec a downRight (succ n)
downLeft<downRight a zero = 1 , refl
downLeft<downRight a (succ n) = downLeft<<downRight _ _ (downLeft<downRight a n)

downLeft-≤-succ : (a : ℤ) → downLeft a ≤ℤ downLeft (succℤ a)
downLeft-≤-succ a
 = 2 , (ap succℤ (ℤ-left-succ a a ⁻¹) ∙ ℤ-right-succ (succℤ a) a ⁻¹)

downLeft-monotone : (a b : ℤ) → a ≤ℤ b → downLeft a ≤ℤ downLeft b
downLeft-monotone = ≤-succ-to-monotone downLeft downLeft-≤-succ

downLeftⁿ-monotone : (a b : ℤ) (n : ℕ) → a ≤ℤ b
                   → rec a downLeft (succ n) ≤ℤ rec b downLeft (succ n)
downLeftⁿ-monotone a b 0 a≤b
 = downLeft-monotone a b a≤b
downLeftⁿ-monotone a b (succ n) a≤b
 = downLeft-monotone _ _ (downLeftⁿ-monotone a b n a≤b)

downRight-≤-succ : (a : ℤ) → downRight a ≤ℤ downRight (succℤ a)
downRight-≤-succ a = 2 , ap (succℤ ∘ succℤ) (pr₂ (downLeft-≤-succ a))

downRight-monotone : (a b : ℤ) → a ≤ℤ b → downRight a ≤ℤ downRight b
downRight-monotone = ≤-succ-to-monotone downRight downRight-≤-succ

downRightⁿ-monotone : (a b : ℤ) (n : ℕ) → a ≤ℤ b
                    → rec a downRight (succ n) ≤ℤ rec b downRight (succ n)
downRightⁿ-monotone a b 0 a≤b
 = downRight-monotone a b a≤b
downRightⁿ-monotone a b (succ n) a≤b
 = downRight-monotone _ _ (downRightⁿ-monotone a b n a≤b)
```

below and below'

```
_below_ : ℤ → ℤ → 𝓤₀ ̇ 
a below b = downLeft b ≤ℤ a ≤ℤ downRight b

downLeft-below  : (a : ℤ) → downLeft a below a
downLeft-below  a = (0 , refl) , (2 , refl)

downMid-below   : (a : ℤ) → downMid a below a
downMid-below   a = (1 , refl) , (1 , refl)

downRight-below : (a : ℤ) → downRight a below a
downRight-below a = (2 , refl) , (0 , refl)

_below'_ : ℤ → ℤ → 𝓤₀ ̇
a below' b = (a ≡ downLeft b) + (a ≡ downMid b) + (a ≡ downRight b)

below'-implies-below : (a b : ℤ) → a below' b → a below b
below'-implies-below .(downLeft  b) b (inl      refl ) = downLeft-below b
below'-implies-below .(downMid   b) b (inr (inl refl)) = downMid-below b
below'-implies-below .(downRight b) b (inr (inr refl)) = downRight-below b

below-implies-below' : (a b : ℤ) → a below b → a below' b
below-implies-below' a b ((0 , e) , _)
 = inl (e ⁻¹)
below-implies-below' a b ((1 , e) , _)
 = (inr ∘ inl) (e ⁻¹)
below-implies-below' a b ((2 , e) , _)
 = (inr ∘ inr) (e ⁻¹)
below-implies-below' a b ((succ (succ (succ _)) , _) , (0 , f))
 = (inr ∘ inr) f
below-implies-below' a b ((succ (succ (succ _)) , _) , (1 , f))
 = (inr ∘ inl) (succℤ-lc f)
below-implies-below' a b ((succ (succ (succ _)) , _) , (2 , f))
 = inl (succℤ-lc (succℤ-lc f))
below-implies-below' a b ((succ (succ (succ n)) , e) , (succ (succ (succ m)) , f))
 = 𝟘-elim (k≢2 k≡2)
 where
   k : ℕ
   k = (succ (succ (succ (succ (succ (succ (n +ℕ m)))))))
   η : downLeft b +pos k ≡ downRight b
   η = (ap ((succℤ ^ 6) ∘ downLeft b +ℤ_) (pos-addition-equiv-to-ℕ n m ⁻¹)
     ∙ ap (succℤ ^ 6) (ℤ+-assoc (downLeft b) (pos n) (pos m) ⁻¹)
     ∙ ap (succℤ ^ 5) (ℤ-left-succ-pos (downLeft b +pos n) m ⁻¹)
     ∙ ap (succℤ ^ 4) (ℤ-left-succ-pos (succℤ (downLeft b +pos n)) m ⁻¹)
     ∙ ap (succℤ ^ 3) (ℤ-left-succ-pos ((succℤ ^ 2) (downLeft b +pos n)) m ⁻¹)
     ∙ ap ((succℤ ^ 3) ∘ (_+pos m)) e
     ∙ f)
   ζ : downLeft b +pos 2 ≡ downRight b
   ζ = refl
   k≡2 : k ≡ 2
   k≡2 = pos-lc k 2 (ℤ+-lc (pos k) (pos 2) (downLeft b) (η ∙ ζ ⁻¹))
   k≢2 : k ≢ 2
   k≢2 = λ ()
```

upLeft and upRight

```
upRight : ℤ → ℤ
upRight x = sign x (num x /2)

upLeft : ℤ → ℤ
upLeft x = upRight (predℤ x)
```

upLeft and upRight properties

```
upRight-suc : (a : ℤ) → upRight (succℤ (succℤ a)) ≡ succℤ (upRight a)
upRight-suc (pos zero) = refl
upRight-suc (pos (succ zero)) = refl
upRight-suc (pos (succ (succ x))) = refl
upRight-suc (negsucc zero) = refl
upRight-suc (negsucc (succ zero)) = refl
upRight-suc (negsucc (succ (succ x))) = refl

upRight-pred : (a : ℤ) → upRight (predℤ (predℤ a)) ≡ predℤ (upRight a)
upRight-pred (pos 0) = refl
upRight-pred (pos 1) = refl
upRight-pred (pos (succ (succ x))) = refl
upRight-pred (negsucc 0) = refl
upRight-pred (negsucc 1) = refl
upRight-pred (negsucc (succ (succ x))) = refl

upRight-succ-pos : (a : ℕ) → upRight (pos a) ≤ℤ upRight (succℤ (pos a))
upRight-succ-pos 0 = 0 , refl
upRight-succ-pos 1 = 1 , refl
upRight-succ-pos (succ (succ a))
 = m , (ℤ-left-succ-pos (pos (a /2)) m ∙ ap succℤ (pr₂ IH))
 where
   IH = upRight-succ-pos a
   m = pr₁ IH

upRight-succ-negsucc : (a : ℕ) → upRight (negsucc a) ≤ℤ upRight (succℤ (negsucc a))
upRight-succ-negsucc 0 = 1 , refl
upRight-succ-negsucc 1 = 0 , refl
upRight-succ-negsucc (succ (succ a))
 = m , (ℤ-left-pred-pos (negsucc (a /2)) m
       ∙ ap predℤ (pr₂ IH)
       ∙ upRight-pred _ ⁻¹
       ∙ ap (upRight ∘ predℤ) (predsuccℤ _))
 where
   IH = upRight-succ-negsucc a
   m = pr₁ IH

upRight-≤-succ : (a : ℤ) → upRight a ≤ℤ upRight (succℤ a)
upRight-≤-succ = ℤ-elim (λ a → upRight a ≤ℤ upRight (succℤ a))
                   upRight-succ-pos upRight-succ-negsucc

upRight-monotone : (a b : ℤ) → a ≤ℤ b → upRight a ≤ℤ upRight b
upRight-monotone = ≤-succ-to-monotone upRight upRight-≤-succ

upLeft-monotone : (a b : ℤ) → a ≤ℤ b → upLeft a ≤ℤ upLeft b
upLeft-monotone a b (n , refl) = upRight-monotone _ _ (n , ℤ-left-pred-pos a n)
```

above and above'

```
_above_ : ℤ → ℤ → 𝓤₀ ̇ 
b above a = upLeft a ≤ℤ b ≤ℤ upRight a

_above'_ : ℤ → ℤ → 𝓤₀ ̇
a above' b = (a ≡ upLeft b) + (a ≡ upRight b)

upLeft-≡-+ : (a : ℤ) → (upLeft a ≡ upRight a) + (succℤ (upLeft a) ≡ upRight a)
upLeft-≡-+ a = {!!}
{- upLeft-elim a (λ - → (- ≡ upRight a) + (succℤ - ≡ upRight a))
                 (inr (succpredℤ _)) (inl refl) -}

upLeft≤upRight : (a : ℤ) → upLeft a ≤ℤ upRight a
upLeft≤upRight a = upRight-monotone _ _ (1 , succpredℤ _)

upLeft-above : (a : ℤ) → upLeft a above a
upLeft-above a = ℤ≤-refl _ , upLeft≤upRight a

upRight-above : (a : ℤ) → upRight a above a
upRight-above a = upLeft≤upRight a , ℤ≤-refl _

above'-implies-above : (a b : ℤ) → a above' b → a above b
above'-implies-above .(upLeft  b) b (inl refl) = upLeft-above b
above'-implies-above .(upRight b) b (inr refl) = upRight-above b

impossible : (a b : ℤ) → (pos 2) ≤ℤ b → upLeft a +ℤ b ≢ upRight a
impossible a .(pos 2 +ℤ (pos n)) (n , refl) e
 = Cases (upLeft-≡-+ a)
     (λ g → b<a→a≢b (pos 2 +pos n) (pos 0) (1 +ℕ n , γ   )
       (ℤ+-lc (pos 2 +pos n) (pos 0) (upLeft a) (e ∙ g ⁻¹)))
     (λ g → b<a→a≢b (pos 2 +pos n) (pos 1) (     n , refl)
       (ℤ+-lc (pos 2 +pos n) (pos 1) (upLeft a) (e ∙ g ⁻¹)))
 where
   γ : succℤ (pos 0) +ℤ pos (1 +ℕ n) ≡ (pos 2 +pos n)
   γ = ap (pos 1 +ℤ_) (pos-addition-equiv-to-ℕ 1 n ⁻¹)
     ∙ ℤ+-assoc (pos 1) (pos 1) (pos n) ⁻¹

above-implies-above' : (a b : ℤ) → a above b → a above' b
above-implies-above' a b ((0 , refl) , (m , f)) = inl refl
above-implies-above' a b ((succ n , e) , zero , refl) = inr refl
above-implies-above' a b ((1 , e) , succ m , f)
 = Cases (upLeft-≡-+ b) (λ g → 𝟘-elim η)
                        (λ g → inr (e ⁻¹ ∙ g))
 where
   ζ : pos 2 +ℤ pos m ≡ succℤ (succℤ (pos m))
   ζ = pos-addition-equiv-to-ℕ 2 m
     ∙ ap pos (addition-commutativity 2 m)
   γ : upLeft b +ℤ succℤ (succℤ (pos m)) ≡ upRight b
   γ = ap succℤ (ℤ-left-succ-pos (upLeft b) m ⁻¹)
     ∙ ap (λ - → succℤ (- +pos m)) e
     ∙ f
   η = impossible b (succℤ (succℤ (pos m))) (m , ζ) γ
above-implies-above' a b ((succ (succ n) , e) , succ m , f)
 = 𝟘-elim (impossible b (pos (succ (succ (succ n))) +pos m)
             (succ n +ℕ m , ζ) γ)
 where
   γ : upLeft b +ℤ (pos (succ (succ (succ n))) +pos m) ≡ upRight b
   γ = ℤ+-assoc (upLeft b) (pos (succ (succ (succ n)))) (pos m) ⁻¹
     ∙ ℤ-left-succ-pos _ m
     ∙ ap (λ - → succℤ (- +pos m)) e
     ∙ f
   ζ : pos 2 +pos (succ n +ℕ m) ≡ pos (succ (succ (succ n))) +pos m
   ζ = ap (pos 2 +ℤ_) (pos-addition-equiv-to-ℕ (succ n) m ⁻¹)
     ∙ ℤ+-assoc (pos 2) (pos (succ n)) (pos m) ⁻¹
     ∙ ap (_+pos m)
         (ap succℤ (pos-addition-equiv-to-ℕ 2 n)
       ∙ ap (pos ∘ succ) (addition-commutativity 2 n))
```

Relationship between below and above

```
upRight-downLeft-pos : (b : ℕ) → pos b ≡ upRight (downLeft (pos b))
upRight-downLeft-pos 0 = refl
upRight-downLeft-pos (succ b)
 = ap succℤ (upRight-downLeft-pos b)
 ∙ upRight-suc (downLeft (pos b)) ⁻¹
 ∙ ap (upRight ∘ succℤ) (ℤ-left-succ-pos (pos b) b ⁻¹)

upRight-downLeft-negsucc : (b : ℕ) → negsucc b ≡ upRight (downLeft (negsucc b))
upRight-downLeft-negsucc 0 = refl
upRight-downLeft-negsucc (succ b)
 = ap predℤ (upRight-downLeft-negsucc b)
 ∙ upRight-pred (downLeft (negsucc b)) ⁻¹
 ∙ ap (upRight ∘ predℤ) (ℤ-left-pred-negsucc (negsucc b) b ⁻¹)

upRight-downMid-pos : (b : ℕ) → pos b ≡ upRight (downMid (pos b))
upRight-downMid-pos 0 = refl
upRight-downMid-pos (succ b)
 = ap succℤ (upRight-downMid-pos b)
 ∙ upRight-suc (downMid (pos b)) ⁻¹
 ∙ ap (upRight ∘ succℤ ∘ succℤ) (ℤ-left-succ-pos (pos b) b ⁻¹)

upRight-downMid-negsucc : (b : ℕ) → negsucc b ≡ upRight (downMid (negsucc b))
upRight-downMid-negsucc 0 = refl
upRight-downMid-negsucc (succ b)
 = ap predℤ (upRight-downMid-negsucc b)
 ∙ upRight-pred (downMid (negsucc b)) ⁻¹
 ∙ ap (upRight ∘ predℤ) (predsuccℤ _)
 ∙ ap upRight (ℤ-left-pred-negsucc (negsucc b) b ⁻¹)
 ∙ ap upRight (succpredℤ _ ⁻¹)

upRight-downRight-pos : (b : ℕ) → succℤ (pos b) ≡ upRight (downRight (pos b))
upRight-downRight-pos 0 = refl
upRight-downRight-pos (succ b)
 = ap succℤ (upRight-downRight-pos b)
 ∙ upRight-suc (downRight (pos b)) ⁻¹
 ∙ ap (upRight ∘ succℤ ∘ succℤ ∘ succℤ) (ℤ-left-succ-pos (pos b) b ⁻¹)

upRight-downRight-negsucc : (b : ℕ) → succℤ (negsucc b) ≡ upRight (downRight (negsucc b))
upRight-downRight-negsucc 0 = refl
upRight-downRight-negsucc (succ b)
 = upRight-downLeft-negsucc b
 ∙ ap upRight (succpredℤ _ ⁻¹)
 ∙ ap (upRight ∘ succℤ) (ℤ-left-pred-negsucc (negsucc b) b ⁻¹)
 ∙ ap (upRight ∘ succℤ) (succpredℤ _ ⁻¹)

upRight-downLeft : (a : ℤ) → a ≡ upRight (downLeft a)
upRight-downLeft
 = ℤ-elim (λ b → b ≡ upRight (downLeft b))
     upRight-downLeft-pos upRight-downLeft-negsucc

upRight-downMid : (a : ℤ) → a ≡ upRight (downMid a)
upRight-downMid
 = ℤ-elim (λ b → b ≡ upRight (downMid b))
     upRight-downMid-pos upRight-downMid-negsucc

upRight-downRight : (a : ℤ) → succℤ a ≡ upRight (downRight a)
upRight-downRight
 = ℤ-elim (λ b → succℤ b ≡ upRight (downRight b))
     upRight-downRight-pos upRight-downRight-negsucc

upLeft-downLeft : (a : ℤ) → succℤ (upLeft (downLeft a)) ≡ a
upLeft-downLeft a = upRight-suc (predℤ (downLeft a)) ⁻¹
                  ∙ ap (upRight ∘ succℤ) (succpredℤ _)
                  ∙ upRight-downMid a ⁻¹

upLeft-downMid : (a : ℤ) → upLeft (downMid a) ≡ a
upLeft-downMid a = ap upRight (pred-downMid a)
                 ∙ upRight-downLeft a ⁻¹

upLeft-downRight : (a : ℤ) → upLeft (downRight a) ≡ a
upLeft-downRight a = ap upRight (pred-downRight a)
                   ∙ upRight-downMid a ⁻¹

below-implies-above-dL : (b : ℤ) → b above (downLeft b)
below-implies-above-dL b
 = (1 , upLeft-downLeft  b)
 , (0 , upRight-downLeft b)

below-implies-above-dM : (b : ℤ) → b above (downMid b)
below-implies-above-dM b
 = (0 , upLeft-downMid  b)
 , (0 , upRight-downMid b)

below-implies-above-dR : (b : ℤ) → b above (downRight b)
below-implies-above-dR b
 = (0 , upLeft-downRight  b)
 , (1 , upRight-downRight b)

below'-implies-above : (a b : ℤ) → a below' b → b above a
below'-implies-above .(downLeft  b) b (inl refl)
 = below-implies-above-dL b
below'-implies-above .(downMid   b) b (inr (inl refl))
 = below-implies-above-dM b
below'-implies-above .(downRight b) b (inr (inr refl))
 = below-implies-above-dR b

downLeft-upRight-pos' : (b : ℕ)
                      → (downLeft (upRight (pos b)) +pos 0 ≡ pos b)
                      + (downLeft (upRight (pos b)) +pos 1 ≡ pos b)
downLeft-upRight-pos' 0 = inl refl
downLeft-upRight-pos' 1 = inr refl
downLeft-upRight-pos' (succ (succ b)) with downLeft-upRight-pos' b
... | inl γ = inl (ap succℤ (ℤ-left-succ-pos (pos (b /2)) (b /2))
                  ∙ ap (succℤ ∘ succℤ) γ)
... | inr γ = inr (ap (succℤ ∘ succℤ) (ℤ-left-succ-pos (pos (b /2)) (b /2) ∙ γ))

downLeft-upRight-negsucc' : (b : ℕ)
                          → (downLeft (upRight (negsucc b)) +pos 0 ≡ negsucc b)
                          + (downLeft (upRight (negsucc b)) +pos 1 ≡ negsucc b)
downLeft-upRight-negsucc' 0 = inr refl
downLeft-upRight-negsucc' 1 = inl refl
downLeft-upRight-negsucc' (succ (succ b)) with downLeft-upRight-negsucc' b
... | inl γ = inl (ap predℤ (ℤ-left-pred-negsucc (negsucc (b /2)) (b /2) )
                  ∙ ap (predℤ ∘ predℤ) γ)
... | inr γ = inr (ap (succℤ ∘ predℤ) (ℤ-left-pred-negsucc (negsucc (b /2)) (b /2))
                  ∙ succpredℤ _
                  ∙ ap predℤ (predsuccℤ _ ⁻¹)
                  ∙ ap (predℤ ∘ predℤ) γ)

dLuL-dRuR-pos : (a : ℕ) → let b = pos a in
                ((downLeft (upLeft b) +pos 2 ≡ b) × (b +pos 2 ≡ downRight (upRight b)))
              + ((downLeft (upLeft b) +pos 1 ≡ b) × (b +pos 1 ≡ downRight (upRight b)))
dLuL-dRuR-pos 0 = inl (refl , refl)
dLuL-dRuR-pos 1 = inr (refl , refl)
dLuL-dRuR-pos (succ (succ a)) = {!!}

above-upLeft' : (b : ℤ)
              → ((downLeft (upLeft b) +pos 2 ≡ b) × (b +pos 2 ≡ downRight (upRight b)))
              + ((downLeft (upLeft b) +pos 1 ≡ b) × (b +pos 1 ≡ downRight (upRight b)))
above-upLeft' b = {!!}

downLeft-upRight' : (b : ℤ)
                  → ((downLeft (upRight b) +pos 0) ≡ b)
                  + ((downLeft (upRight b) +pos 1) ≡ b)
downLeft-upRight' = ℤ-elim (λ - → (downLeft (upRight -) +pos 0 ≡ -)
                                + (downLeft (upRight -) +pos 1 ≡ -))
                      downLeft-upRight-pos' downLeft-upRight-negsucc'

{-
downLeft-upLeft-upRight : (b : ℤ)
                        → (downLeft (upLeft b) +pos 0 ≡ downLeft (upRight b))
                        + (downLeft (upLeft b) +pos 2 ≡ downLeft (upRight b))
downLeft-upLeft-upRight b
 = upLeft-elim b
     (λ - → (downLeft - +pos 0 ≡ downLeft (upRight b))
          + (downLeft - +pos 2 ≡ downLeft (upRight b)))
     (inr (downLeft-monotone' (predℤ (upRight b)) (upRight b)
       (1 , succpredℤ _)))
     (inl refl)

downLeft-upLeft' : (b : ℤ)
                  → ((downLeft (upLeft b) +pos 0) ≡ b)
                  + ((downLeft (upLeft b) +pos 1) ≡ b)
                  + ((downLeft (upLeft b) +pos 2) ≡ b)
downLeft-upLeft' b
 = Cases (downLeft-upRight' b) {!inl!} {!!}
 -}

downLeft-upRight : (b : ℤ) → downLeft (upRight b) ≤ℤ b
downLeft-upRight b
 = Cases (downLeft-upRight' b)
     (λ e → transport (downLeft (upRight b) ≤ℤ_) e (ℤ≤-refl _))
     (λ e → transport (downLeft (upRight b) ≤ℤ_) e (1 , refl))

downLeft-upLeft  : (b : ℤ) → downLeft (upLeft b) ≤ℤ b
downLeft-upLeft b
 = ℤ≤-trans _ _ _ (downLeft-monotone _ _ (upLeft≤upRight b)) (downLeft-upRight b)

above-upRight' : (b : ℤ)
               → ((downLeft (upRight b) +pos 0 ≡ b)
                 × (b +pos 2 ≡ downRight (upRight b)))
               + ((downLeft (upRight b) +pos 1 ≡ b)
                 × (b +pos 1 ≡ downRight (upRight b)))
above-upRight' b
 = Cases (downLeft-upRight' b)
     (λ l → inl (l , ap (succℤ ∘ succℤ) (l ⁻¹)))
     (λ r → inr (r , ap succℤ (r ⁻¹)))   
     
above-upRight : (b : ℤ) → b below (upRight b)
above-upRight b = Cases (above-upRight' b)
                    (λ (al , bl) → (0 , al) , (2 , bl))
                    (λ (ar , br) → (1 , ar) , (1 , br))

downRight-predupRight-pos : (b : ℕ) → even (pos b)
                          → pos b ≤ℤ downRight (predℤ (upRight (pos b)))
downRight-predupRight-pos 0 _ = 0 , refl
downRight-predupRight-pos 1 e = 𝟘-elim (e ⋆)
downRight-predupRight-pos (succ (succ b)) e
 = m
 , (ℤ-left-succ-pos (pos (succ b)) m
 ∙ ap succℤ (ℤ-left-succ-pos (pos b) m)
 ∙ ap (succℤ ∘ succℤ)
     (pr₂ IH
     ∙ ap (succℤ ∘ succℤ)
         ((ℤ-left-pred (pos (b /2)) (predℤ (pos (b /2))))
         ∙ ap predℤ (ℤ-right-pred (pos (b /2)) (pos (b /2))))
     ∙ ap succℤ (succpredℤ _)
     ∙ succpredℤ _))
 where
   IH = downRight-predupRight-pos b e
   m = pr₁ IH

downRight-predupRight-negsucc : (b : ℕ) → even (negsucc b)
                              → negsucc b ≤ℤ downRight (predℤ (upRight (negsucc b)))
downRight-predupRight-negsucc 0 e = 𝟘-elim (e ⋆)
downRight-predupRight-negsucc 1 e = 0 , refl
downRight-predupRight-negsucc (succ (succ b)) e
 = m
 , (ℤ-left-pred-pos (negsucc (succ b)) m
 ∙ ap predℤ (ℤ-left-pred-pos (negsucc b) m)
 ∙ ap (predℤ ∘ predℤ) (pr₂ IH)
 ∙ ap predℤ (predsuccℤ _)
 ∙ predsuccℤ _
 ∙ ℤ-left-pred-negsucc (negsucc (succ (b /2))) (b /2) ⁻¹
 ∙ succpredℤ _ ⁻¹
 ∙ ap succℤ (succpredℤ _) ⁻¹)
 where
   IH = downRight-predupRight-negsucc b e
   m = pr₁ IH

above-upLeft : (b : ℤ) → b below (upLeft b)
above-upLeft b
 = (ℤ≤-trans _ _ _ (downLeft-monotone (upLeft b) (upRight b) (upLeft≤upRight b))
     (pr₁ (above-upRight b)))
 , {!!}
 {- (upLeft-elim* b (λ - → b ≤ℤ downRight -)
     (ℤ-elim (λ - → even - → - ≤ℤ downRight (predℤ (upRight -)))
       downRight-predupRight-pos downRight-predupRight-negsucc b)
     (λ _ → pr₂ (above-upRight b))) -}

above'-implies-below : (a b : ℤ) → a above' b → b below a
above'-implies-below .(upLeft  b) b (inl refl) = above-upLeft b
above'-implies-below .(upRight b) b (inr refl) = above-upRight b

above-implies-below : (a b : ℤ) → a above b → b below a
above-implies-below a b = above'-implies-below a b ∘ above-implies-above' a b

below-implies-above : (a b : ℤ) → a below b → b above a
below-implies-above a b = below'-implies-above a b ∘ below-implies-below' a b

above-downLeft : (a : ℤ) → a above (downLeft a)
above-downLeft a = below-implies-above (downLeft a) a (downLeft-below a)

above-downMid : (a : ℤ) → a above (downMid a)
above-downMid a = below-implies-above (downMid a) a (downMid-below a)

above-downRight : (a : ℤ) → a above (downRight a)
above-downRight a = below-implies-above (downRight a) a (downRight-below a)
```

Recursive above

```
_aboveⁿ_ : (a c : ℤ) → ℕ → 𝓤₀ ̇
(a aboveⁿ c) 0 = a above c
(a aboveⁿ c) (succ n) = Σ b ꞉ ℤ , (a above b) × (b aboveⁿ c) n

_belowⁿ_ : (a c : ℤ) → ℕ → 𝓤₀ ̇
(a belowⁿ c) 0 = a below c
(a belowⁿ c) (succ n) = Σ b ꞉ ℤ , (a below b) × (b belowⁿ c) n

aboveⁿ-implies-belowⁿ : (a c : ℤ) (n : ℕ) → (c aboveⁿ a) n → (a belowⁿ c) n
aboveⁿ-implies-belowⁿ a c zero γ = above-implies-below c a γ
aboveⁿ-implies-belowⁿ a c (succ n) (b , η , θ)
 = {!!} -- b , above-implies-below b a θ , aboveⁿ-implies-belowⁿ b c n η

below-up : (a c : ℤ) (n : ℕ) → (a belowⁿ c) (succ n)
         → (upLeft a belowⁿ c) n + (upRight a belowⁿ c) n
below-up a c n (b , η , θ)
 = Cases (above-implies-above' b a (below-implies-above a b η))
     (λ l → inl (transport (λ - → (- belowⁿ c) n) l θ))
     (λ r → inr (transport (λ - → (- belowⁿ c) n) r θ))

data Vec (X : 𝓤 ̇ ) : ℕ → 𝓤 ̇ where
  [] : Vec X 0
  _++_ : ∀ {n} → X → Vec X n → Vec X (succ n)

[_] : {X : 𝓤 ̇ } → X → Vec X 1
[ x ] = x ++ []

_+++_ : {X : 𝓤 ̇ } {n : ℕ} → Vec X n → X → Vec X (succ n)
[] +++ x = [ x ]
(h ++ v) +++ x = h ++ (v +++ x)

below-vec' : (a c : ℤ) → (n : ℕ) → (a belowⁿ c) n → Vec ℤ (succ n)
below-vec' a c zero b = [ a ]
below-vec' a c (succ n) (a' , _ , f) = a ++ below-vec' a' c n f

below-vec : (a c : ℤ) → (n : ℕ) → (a belowⁿ c) n → Vec ℤ (succ (succ n))
below-vec a c n b = (below-vec' a c n b) +++ c

_!!_ : {X : 𝓤 ̇ } {n : ℕ} → Vec X n → (k : ℕ) → k <ℕ n → X
((x ++ v) !! zero) k<n = x
((x ++ v) !! succ k) k<n = (v !! k) k<n

pairwise : {X : 𝓤 ̇ } {n : ℕ} → Vec X (succ n) → (p : X → X → 𝓥 ̇ ) → 𝓥 ̇
pairwise {𝓤} {𝓥} {X} {n} v p
 = (k : ℕ) → (k<n : k <ℕ n) → (k<sn : k <ℕ succ n)
 → p ((v !! k) k<sn) ((v !! succ k) k<n)

below-vec-!!0 : (a c : ℤ) (n : ℕ) (b : (a belowⁿ c) n)
              → (below-vec a c n b !! zero) ⋆ ≡ a
below-vec-!!0 a c zero b = refl
below-vec-!!0 a c (succ n) b = refl

!!-helper : {X : 𝓤 ̇ } {n : ℕ} → (v : Vec X n) → (k₁ k₂ : ℕ)
          → (k₁<n : k₁ <ℕ n) (k₂<n : k₂ <ℕ n)
          → k₁ ≡ k₂
          → (v !! k₁) k₁<n ≡ (v !! k₂) k₂<n
!!-helper (x ++ v) zero .zero k₁<n k₂<n refl = refl
!!-helper (x ++ v) (succ k) .(succ k) k₁<n k₂<n refl
 = !!-helper v k k k₁<n k₂<n refl

below-vec-!!sn : (a c : ℤ) (n : ℕ) (b : (a belowⁿ c) n)
               → (n<sn : n <ℕ succ n)
               → (below-vec a c n b !! succ n) n<sn ≡ c
below-vec-!!sn a c zero b n<sn = refl
below-vec-!!sn a c (succ n) (b , e , f) n<sn
 = below-vec-!!sn b c n f n<sn

pairwise-below-vec : (a c : ℤ) → (n : ℕ) → (b : (a belowⁿ c) n)
                   → pairwise (below-vec a c n b) _below_
pairwise-below-vec a c zero b zero k<n k<sn
 = b
pairwise-below-vec a c (succ n) (b' , e , f) zero k<n k<sn
 = transport (a below_) (below-vec-!!0 b' c n f ⁻¹) e
pairwise-below-vec a c (succ n) (b' , e , f) (succ k) k<n k<sn
 = pairwise-below-vec b' c n f k k<n k<sn

below-everything-in-vec : (a c : ℤ) → (n : ℕ) → (b : (a belowⁿ c) n)
                        → (k : ℕ) → (k<sn : k <ℕ succ n)
                        → (a belowⁿ ((below-vec a c n b !! (succ k)) k<sn)) k
below-everything-in-vec a c zero b zero k<sn
 = b
below-everything-in-vec a c (succ n) (b , η , θ) zero k<sn
 = transport (a below_) (below-vec-!!0 b c n θ ⁻¹) η 
below-everything-in-vec a c (succ n) (b , η , θ) (succ k) k<sn
 = b , η , below-everything-in-vec b c n θ k k<sn
