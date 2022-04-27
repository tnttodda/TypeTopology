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

```

downLeft, downMid and downRight

```
downLeft downMid downRight : ℤ → ℤ
downLeft  a = a +ℤ a
downMid   a = succℤ (downLeft a)
downRight a = succℤ (downMid  a)
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

upLeft' : (x : ℤ) → even x + odd x → ℤ
upLeft' x (inl _) = predℤ (upRight x)
upLeft' x (inr _) =        upRight x

upLeft : ℤ → ℤ
upLeft x = upLeft' x (even-or-odd? x)
```

upLeft elimination

```
upLeft-elim : (x : ℤ) → (P : ℤ → 𝓤 ̇ )
            → P (predℤ (upRight x)) → P (upRight x)
            → P (upLeft x)
upLeft-elim x P Pe Po with even-or-odd? x
... | (inl e) = Pe
... | (inr o) = Po

upLeft²-elim : (x : ℤ) → (P : ℤ → ℤ → 𝓤 ̇ )
             → P (predℤ (upRight x)) (predℤ (upRight (succℤ (succℤ x))))
             → P (upRight x) (upRight (succℤ (succℤ x)))
             → P (upLeft x) (upLeft (succℤ (succℤ x)))
upLeft²-elim x P Pe Po with even-or-odd? x
... | (inl e) = transport (P (predℤ (upRight x)))
                  (ap (upLeft' (succℤ (succℤ x)))
                     (even-or-odd-is-prop (succℤ (succℤ x))
                       (inl (even-succ-succ x e))
                       (even-or-odd? (succℤ (succℤ x)))))
                  Pe
... | (inr o) = transport (P (upRight x))
                  (ap (upLeft' (succℤ (succℤ x)))
                     (even-or-odd-is-prop (succℤ (succℤ x))
                        (inr (odd-succ-succ x o))
                        (even-or-odd? (succℤ (succℤ x)))))
                  Po

upLeft²-elim-pred : (x : ℤ) → (P : ℤ → ℤ → 𝓤 ̇ )
                  → P (predℤ (upRight (predℤ (predℤ x)))) (predℤ (upRight x))
                  → P (upRight (predℤ (predℤ x))) (upRight x)
                  → P (upLeft (predℤ (predℤ x))) (upLeft x)
upLeft²-elim-pred x P Pe Po
 = transport (P (upLeft y))
     (ap upLeft (ap succℤ (succpredℤ (predℤ x)) ∙ succpredℤ x))
     Py
 where
   y : ℤ
   y = predℤ (predℤ x)
   Pe' : P (predℤ (upRight y)) (predℤ (upRight (succℤ (succℤ y))))
   Pe' = transport
           (λ - → P (predℤ (upRight (predℤ (predℤ x)))) (predℤ (upRight -)))
           (succpredℤ _ ⁻¹ ∙ ap succℤ (succpredℤ _ ⁻¹))
           Pe
   Po' : P (upRight y) (upRight (succℤ (succℤ y)))
   Po' = transport
           (λ - → P (upRight (predℤ (predℤ x))) (upRight -))
           (succpredℤ _ ⁻¹ ∙ ap succℤ (succpredℤ _ ⁻¹))
           Po
   Py : P (upLeft (predℤ (predℤ x))) (upLeft (succℤ (succℤ (predℤ (predℤ x)))))
   Py = upLeft²-elim y P Pe' Po'
```

above and above'

```
_above_ : ℤ → ℤ → 𝓤₀ ̇ 
b above a = upLeft a ≤ℤ b ≤ℤ upRight a

_above'_ : ℤ → ℤ → 𝓤₀ ̇
a above' b = (a ≡ upLeft b) + (a ≡ upRight b)

upLeft-≡-+ : (a : ℤ) → (upLeft a ≡ upRight a) + (succℤ (upLeft a) ≡ upRight a)
upLeft-≡-+ a = upLeft-elim a (λ - → (- ≡ upRight a) + (succℤ - ≡ upRight a))
                 (inr (succpredℤ _)) (inl refl)

upLeft≤upRight : (a : ℤ) → upLeft a ≤ℤ upRight a
upLeft≤upRight a = Cases (upLeft-≡-+ a) (0 ,_) (1 ,_)

upLeft-above : (a : ℤ) → upLeft a above a
upLeft-above a = (0 , refl) , upLeft≤upRight a

upRight-above : (a : ℤ) → upRight a above a
upRight-above a = (upLeft≤upRight a) , (0 , refl)

above'-implies-above : (a b : ℤ) → a above' b → a above b
above'-implies-above .(upLeft  b) b (inl refl) = upLeft-above b
above'-implies-above .(upRight b) b (inr refl) = upRight-above b

a<b→a≢b : ∀ a b → (b <ℤ a) → a ≢ b
a<b→a≢b a a (n , a<a) refl = γ γ'
 where
   γ' : 0 ≡ succ n
   γ' = pos-lc _ _ (ℤ+-lc _ _ a (a<a ⁻¹ ∙ ℤ-left-succ-pos a n))
   γ : 0 ≢ succ n
   γ ()

impossible : (a b : ℤ) → (pos 2) ≤ℤ b → upLeft a +ℤ b ≢ upRight a
impossible a .(pos 2 +ℤ (pos n)) (n , refl) e
 = Cases (upLeft-≡-+ a)
     (λ g → a<b→a≢b (pos 2 +pos n) (pos 0) (1 +ℕ n , γ   )
       (ℤ+-lc (pos 2 +pos n) (pos 0) (upLeft a) (e ∙ g ⁻¹)))
     (λ g → a<b→a≢b (pos 2 +pos n) (pos 1) (     n , refl)
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
upRight-suc : (a : ℤ) → upRight (succℤ (succℤ a)) ≡ succℤ (upRight a)
upRight-suc (pos zero) = refl
upRight-suc (pos (succ zero)) = refl
upRight-suc (pos (succ (succ x))) = refl
upRight-suc (negsucc zero) = refl
upRight-suc (negsucc (succ zero)) = refl
upRight-suc (negsucc (succ (succ x))) = refl

pred-upRight-suc : (a : ℤ) → predℤ (upRight (succℤ (succℤ a))) ≡ succℤ (predℤ (upRight a))
pred-upRight-suc (pos zero) = refl
pred-upRight-suc (pos (succ zero)) = refl
pred-upRight-suc (pos (succ (succ x))) = refl
pred-upRight-suc (negsucc zero) = refl
pred-upRight-suc (negsucc (succ zero)) = refl
pred-upRight-suc (negsucc (succ (succ x))) = refl

upLeft-suc : (a : ℤ) → upLeft (succℤ (succℤ a)) ≡ succℤ (upLeft a)
upLeft-suc a
 = upLeft²-elim a (λ a b → b ≡ succℤ a) (pred-upRight-suc a) (upRight-suc a)

pred-upRight-pred : (a : ℤ) → predℤ (upRight (predℤ (predℤ a))) ≡ predℤ (predℤ (upRight a))
pred-upRight-pred (pos zero) = refl
pred-upRight-pred (pos (succ zero)) = refl
pred-upRight-pred (pos (succ (succ x))) = refl
pred-upRight-pred (negsucc zero) = refl
pred-upRight-pred (negsucc (succ zero)) = refl
pred-upRight-pred (negsucc (succ (succ x))) = refl

upRight-pred : (a : ℤ) → upRight (predℤ (predℤ a)) ≡ predℤ (upRight a)
upRight-pred (pos 0) = refl
upRight-pred (pos 1) = refl
upRight-pred (pos (succ (succ x))) = refl
upRight-pred (negsucc 0) = refl
upRight-pred (negsucc 1) = refl
upRight-pred (negsucc (succ (succ x))) = refl

upLeft-pred : (a : ℤ) → upLeft (predℤ (predℤ a)) ≡ predℤ (upLeft a)
upLeft-pred a
 = upLeft²-elim-pred a (λ a b → a ≡ predℤ b) (pred-upRight-pred a) (upRight-pred a)

ℤ-elim : (P : ℤ → 𝓤 ̇ )
       → ((n : ℕ) → P (pos n)) → ((n : ℕ) → P (negsucc n))
       → Π P
ℤ-elim P Pp Pn (pos     n) = Pp n
ℤ-elim P Pp Pn (negsucc n) = Pn n

upLeft-downLeft-pos : (b : ℕ) → succℤ (upLeft (downLeft (pos b))) ≡ pos b
upLeft-downLeft-pos 0 = refl
upLeft-downLeft-pos (succ b)
 = ap (succℤ ∘ upLeft ∘ succℤ) (ℤ-left-succ-pos (pos b) b)
 ∙ ap succℤ (upLeft-suc (downLeft (pos b)))
 ∙ ap succℤ (upLeft-downLeft-pos b)

upLeft-downLeft-negsucc : (b : ℕ) → succℤ (upLeft (downLeft (negsucc b))) ≡ negsucc b
upLeft-downLeft-negsucc 0 = refl
upLeft-downLeft-negsucc (succ b)
 = ap (succℤ ∘ upLeft ∘ predℤ) (ℤ-left-pred-negsucc (negsucc b) b)
 ∙ ap succℤ (upLeft-pred (downLeft (negsucc b)))
 ∙ succpredℤ _ ∙ predsuccℤ _ ⁻¹
 ∙ ap predℤ (upLeft-downLeft-negsucc b)

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

below-implies-above-dL : (b : ℤ) → b above (downLeft b)
below-implies-above-dL b
 = (1 , ℤ-elim (λ b → succℤ (upLeft (downLeft b)) ≡ b)
          upLeft-downLeft-pos upLeft-downLeft-negsucc b)
 , (0 , ℤ-elim (λ b → b ≡ upRight (downLeft b))
          upRight-downLeft-pos upRight-downLeft-negsucc b)

upLeft-downMid-pos : (b : ℕ) → upLeft (downMid (pos b)) ≡ pos b
upLeft-downMid-pos 0 = refl
upLeft-downMid-pos (succ b)
 = ap (upLeft ∘ succℤ) (ℤ-left-succ-pos (pos b) (succ b))
 ∙ upLeft-suc (downMid (pos b))
 ∙ ap succℤ (upLeft-downMid-pos b)

upLeft-downMid-negsucc : (b : ℕ) → upLeft (downMid (negsucc b)) ≡ negsucc b
upLeft-downMid-negsucc 0 = refl
upLeft-downMid-negsucc (succ b)
 = ap (upLeft ∘ succℤ) (ℤ-left-pred-negsucc (negsucc b) (succ b))
 ∙ ap upLeft (succpredℤ (predℤ (downLeft (negsucc b))))
 ∙ ap (upLeft ∘ predℤ) (predsuccℤ (downLeft (negsucc b)) ⁻¹)
 ∙ upLeft-pred (downMid (negsucc b))
 ∙ ap predℤ (upLeft-downMid-negsucc b)

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

below-implies-above-dM : (b : ℤ) → b above (downMid b)
below-implies-above-dM b
 = (0 , ℤ-elim (λ b → upLeft (downMid b) ≡ b)
          upLeft-downMid-pos upLeft-downMid-negsucc b)
 , (0 , ℤ-elim (λ b → b ≡ upRight (downMid b))
          upRight-downMid-pos upRight-downMid-negsucc b)

upLeft-downRight-pos : (b : ℕ) → upLeft (downRight (pos b)) ≡ pos b
upLeft-downRight-pos 0 = refl
upLeft-downRight-pos (succ b)
 = ap (upLeft ∘ succℤ) (ℤ-left-succ-pos (pos b) (succ (succ b)))
 ∙ upLeft-suc (downRight (pos b))
 ∙ ap succℤ (upLeft-downRight-pos b)

upLeft-downRight-negsucc : (b : ℕ) → upLeft (downRight (negsucc b)) ≡ negsucc b
upLeft-downRight-negsucc 0 = refl
upLeft-downRight-negsucc (succ b)
 = ap (upLeft ∘ succℤ ∘ succℤ) (ℤ-left-pred-negsucc (negsucc b) (succ b))
 ∙ ap (upLeft ∘ succℤ) (succpredℤ (predℤ (downLeft (negsucc b))))
 ∙ ap upLeft (succpredℤ (downLeft (negsucc b)))
 ∙ ap upLeft (predsuccℤ (downLeft (negsucc b))) ⁻¹
 ∙ ap (upLeft ∘ predℤ) (predsuccℤ (succℤ (downLeft (negsucc b))) ⁻¹)
 ∙ upLeft-pred (downRight (negsucc b))
 ∙ ap predℤ (upLeft-downRight-negsucc b)

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

below-implies-above-dR : (b : ℤ) → b above (downRight b)
below-implies-above-dR b
 = (0 , ℤ-elim (λ b → upLeft (downRight b) ≡ b)
           upLeft-downRight-pos upLeft-downRight-negsucc b)
 , (1 , ℤ-elim (λ b → succℤ b ≡ upRight (downRight b))
           upRight-downRight-pos upRight-downRight-negsucc b)

below'-implies-above : (a b : ℤ) → a below' b → b above a
below'-implies-above .(downLeft  b) b (inl refl)
 = below-implies-above-dL b
below'-implies-above .(downMid   b) b (inr (inl refl))
 = below-implies-above-dM b
below'-implies-above .(downRight b) b (inr (inr refl))
 = below-implies-above-dR b

{-
above'-implies-below : (a b : ℤ) → a above' b → b below a
above'-implies-below .(upLeft b) b (inl refl) = {!!}
above'-implies-below a b (inr x) = {!!}
-}

below-implies-above : (a b : ℤ) → a below b → b above a
below-implies-above a b = (below'-implies-above a b) ∘ (below-implies-below' a b)

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

get-below : (a c : ℤ) (n : ℕ) → (a belowⁿ c) n → ℤ
get-below a c 0 _ = a
get-below a c (succ _) (b , _) = b

pred : ℕ → ℕ
pred 0 = 0
pred (succ n) = n
{-
get-below' : (a c : ℤ) → (n n' : ℕ) → (b : (a belowⁿ c) n)
           → (k : ℕ) → n' +ℕ k ≡ n
           → Σ a' ꞉ ℤ , (a belowⁿ a') (pred n)
get-below' a c n n' b zero v = a , {!!}
get-below' a c (succ n) n' (a' , f , _) (succ k) v = a' , f
-}
{-
belowⁿ-s : (a b : ℤ) → (n : ℕ) → (a belowⁿ b) n
         → (m : ℕ) → m <ℕ n → (a belowⁿ b) m
belowⁿ-s a c (succ n) (b , x , y) zero ⋆ = {!!}
belowⁿ-s a c (succ n) f (succ m) m<n = {!!}
-}

{-
factual : (a b : ℤ) (n : ℕ) → (a aboveⁿ b) (succ n)
        → (a aboveⁿ upLeft b) n + (a aboveⁿ upRight b) n
factual a b n (a' , f , e)
 = Cases (above-implies-above' a' b e)
     (λ a'≡l → inl (transport (λ - → (a aboveⁿ -) n) a'≡l f))
     (λ a'≡r → inr (transport (λ - → (a aboveⁿ -) n) a'≡r f))

-}
