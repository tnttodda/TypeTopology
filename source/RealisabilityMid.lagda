\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-FunExt
open import Escardo-Simpson-LICS2001
open import UF-PropTrunc
open import OrderedIntervalObject

module RealisabilityMid
 (𝓤 : Universe)
 (fe : FunExt)
 (io : Interval-object fe 𝓤)
 (db : has-double fe 𝓤 io)
 (pt : propositional-truncations-exist)
 (or : is-ordered fe pt io)
 where

open import UF-Base hiding (_≈_)
open import DiscreteAndSeparated
open import Sequence fe
open import NaturalsAddition renaming (_+_ to _+ℕ_)
open import NaturalsOrder renaming (_≤_ to _≤ℕ_
                                  ; _<_ to _<ℕ_
                                  ; ≤-trans to ≤ℕ-trans)
open import UF-Subsingletons
open import UF-Subsingletons-FunExt

open basic-interval-object-development fe io db

-- Define the code types

data 𝟛 : 𝓤₀ ̇ where
  ₃⁰ ₃⁺¹ ₃⁻¹ : 𝟛

𝟛ᴺ : 𝓤₀ ̇
𝟛ᴺ = ℕ → 𝟛

𝟛-is-discrete : is-discrete 𝟛
𝟛-is-discrete ₃⁰  ₃⁰  = inl refl
𝟛-is-discrete ₃⁰  ₃⁺¹ = inr (λ ())
𝟛-is-discrete ₃⁰  ₃⁻¹ = inr (λ ())
𝟛-is-discrete ₃⁺¹ ₃⁰  = inr (λ ())
𝟛-is-discrete ₃⁺¹ ₃⁺¹ = inl refl
𝟛-is-discrete ₃⁺¹ ₃⁻¹ = inr (λ ())
𝟛-is-discrete ₃⁻¹ ₃⁰  = inr (λ ())
𝟛-is-discrete ₃⁻¹ ₃⁺¹ = inr (λ ())
𝟛-is-discrete ₃⁻¹ ₃⁻¹ = inl refl

-- Define the realisability map

q : 𝟛 → 𝕀
q ₃⁻¹ = −1
q ₃⁰  =  O
q ₃⁺¹ = +1

𝕢 : 𝟛ᴺ → 𝕀
𝕢 α = M (λ n → q (α n))

neg : 𝟛 → 𝟛
neg ₃⁻¹ = ₃⁺¹
neg  ₃⁰ = ₃⁰
neg ₃⁺¹ = ₃⁻¹

map : {X : 𝓥 ̇ } {Y : 𝓦 ̇ } → (X → Y) → (ℕ → X) → (ℕ → Y)
map f α n = f (α n)

_realises²_ : (𝟛ᴺ → 𝟛ᴺ → 𝟛ᴺ) → (𝕀 → 𝕀 → 𝕀) → 𝓤 ̇
_*³_ realises² _*ᴵ_ = Π α ꞉ 𝟛ᴺ , Π β ꞉ 𝟛ᴺ , (𝕢 (α *³ β) ≡ 𝕢 α *ᴵ 𝕢 β)

_realises¹_ : (𝟛ᴺ → 𝟛ᴺ) → (𝕀 → 𝕀) → 𝓤 ̇
ϕ realises¹ f = Π α ꞉ 𝟛ᴺ , (𝕢 (ϕ α) ≡ f (𝕢 α))

-- q → 𝕢

−-real' : (h : 𝟛) → q (neg h) ≡ − q h
−-real' ₃⁻¹ = −1-inverse ⁻¹
−-real' ₃⁰  = O-inverse ⁻¹
−-real' ₃⁺¹ = +1-inverse ⁻¹

𝕢-map : (f³ : 𝟛 → 𝟛) (fᴵ : 𝕀 → 𝕀)
      → is-⊕-homomorphism fe 𝓘 𝓘 fᴵ
      → ((h : 𝟛) → q (f³ h) ≡ fᴵ (q h))
      → (map f³) realises¹ fᴵ
𝕢-map f³ fᴵ h g α = ap M (dfunext (fe 𝓤₀ 𝓤) (λ n → g (α n)))
                  ∙ ⊕-homs-are-M-homs fᴵ h (λ n → q (α n)) ⁻¹

−-real : (map neg) realises¹ −_
−-real = 𝕢-map neg −_ −-is-⊕-homomorphism −-real'

id-realises-id : id realises¹ id
id-realises-id α = refl

-- Show that midpoint and multiplication have realisers

-- mid-realisability : mid realises² _⊕_
-- mid-realisability α β = {!!}

data 𝟝 : 𝓤₀ ̇ where
 −2' −1' O' +1' +2' : 𝟝

𝟝ᴺ : 𝓤₀ ̇
𝟝ᴺ = ℕ → 𝟝

add2' : 𝟛 → 𝟛 → 𝟝
add2' ₃⁻¹ ₃⁻¹ = −2'
add2' ₃⁻¹ ₃⁰  = −1'  
add2' ₃⁻¹ ₃⁺¹ = O'
add2' ₃⁰  ₃⁻¹ = −1'
add2' ₃⁺¹ ₃⁻¹ = O'
add2' ₃⁰  ₃⁰  = O'
add2' ₃⁰  ₃⁺¹ = +1'
add2' ₃⁺¹ ₃⁰  = +1'
add2' ₃⁺¹ ₃⁺¹ = +2'

add2 : 𝟛ᴺ → 𝟛ᴺ → 𝟝ᴺ
add2 x y n = add2' (x n) (y n)

half : 𝟝 → 𝕀
half −2' = −1
half −1' = −1 /2
half  O' =  O
half +1' = +1 /2
half +2' = +1

half-real : Π α ꞉ 𝟛ᴺ , Π β ꞉ 𝟛ᴺ , (M (map half (add2 α β)) ≡ 𝕢 α ⊕ 𝕢 β)
half-real α β = ap M (dfunext (fe 𝓤₀ 𝓤) (λ i → γ (α i) (β i)))
              ∙ M-hom (λ n → q (α n)) (λ n → q (β n)) ⁻¹
 where
   γ : (h h' : 𝟛) → half (add2' h h') ≡ (q h ⊕ q h')
   γ ₃⁻¹ ₃⁻¹ = ⊕-idem ⁻¹
   γ ₃⁻¹ ₃⁰  = refl
   γ ₃⁻¹ ₃⁺¹ = refl
   γ ₃⁰  ₃⁻¹ = ⊕-comm
   γ ₃⁺¹ ₃⁻¹ = ⊕-comm
   γ ₃⁰  ₃⁰  = ⊕-idem ⁻¹
   γ ₃⁰  ₃⁺¹ = ⊕-comm
   γ ₃⁺¹ ₃⁰  = refl
   γ ₃⁺¹ ₃⁺¹ = ⊕-idem ⁻¹

div2 : 𝟝ᴺ → 𝟛ᴺ

δc : 𝟝 → 𝟝ᴺ → 𝟛ᴺ
δc −2' α 0 = ₃⁰
δc −2' α 1 = ₃⁰
δc −2' α (succ (succ n)) = div2 (tail (tail α)) n
δc  O' α 0 = ₃⁰
δc  O' α 1 = ₃⁺¹
δc  O' α (succ (succ n)) = div2 (tail (tail α)) n
δc +2' α 0 = ₃⁺¹
δc +2' α 1 = ₃⁰
δc +2' α (succ (succ n)) = div2 (tail (tail α)) n
δc −1' α 0 = ₃⁰
δc −1' α (succ n) = div2 (+1' ∶∶ tail (tail α)) n
δc +1' α 0 = ₃⁺¹
δc +1' α (succ n) = div2 (−1' ∶∶ tail (tail α)) n    

δb : 𝟝 → 𝟝ᴺ → 𝟛ᴺ
δb −2' _ 0 = ₃⁻¹
δb −2' _ 1 = ₃⁰
δb −2' α (succ (succ n)) = div2 (tail (tail α)) n
δb  O' _ 0 = ₃⁰
δb  O' _ 1 = ₃⁻¹
δb  O' α (succ (succ n)) = div2 (tail (tail α)) n
δb +2' _ 0 = ₃⁰
δb +2' _ 1 = ₃⁰
δb +2' α (succ (succ n)) = div2 (tail (tail α)) n
δb −1' _ 0 = ₃⁻¹
δb −1' α (succ n) = div2 (+1' ∶∶ tail (tail α)) n
δb +1' _ 0 = ₃⁰
δb +1' α (succ n) = div2 (−1' ∶∶ tail (tail α)) n

γa : 𝟝 → 𝟝ᴺ → 𝟛ᴺ
γa −2' _ 0 = ₃⁻¹
γa  O' _ 0 = ₃⁰
γa +2' _ 0 = ₃⁺¹
γa −2' α (succ n) = div2 (tail α) n
γa  O' α (succ n) = div2 (tail α) n
γa +2' α (succ n) = div2 (tail α) n
γa −1' α = δb (α 1) α
γa +1' α = δc (α 1) α

div2 α = γa (α 0) α
  
mid : 𝟛ᴺ → 𝟛ᴺ → 𝟛ᴺ
mid α β = div2 (add2 α β)

div2⟨−2:x⟩ : (α : 𝟝ᴺ) → div2 (−2' ∶∶ α) ≡ ₃⁻¹ ∶∶ div2 α
div2⟨O:x⟩  : (α : 𝟝ᴺ) → div2 ( O' ∶∶ α) ≡ ₃⁰  ∶∶ div2 α  
div2⟨+2:x⟩ : (α : 𝟝ᴺ) → div2 (+2' ∶∶ α) ≡ ₃⁺¹ ∶∶ div2 α
div2⟨−1:−2:x⟩ : (α : 𝟝ᴺ) → div2 (−1' ∶∶ (−2' ∶∶ α)) ≡ ₃⁻¹ ∶∶ (₃⁰ ∶∶ div2 α)
div2⟨−1:−1:x⟩ : (α : 𝟝ᴺ) → div2 (−1' ∶∶ (−1' ∶∶ α)) ≡ ₃⁻¹ ∶∶ div2 (+1' ∶∶ α)
div2⟨−1:O:x⟩  : (α : 𝟝ᴺ) → div2 (−1' ∶∶ ( O' ∶∶ α)) ≡ ₃⁰  ∶∶ (₃⁻¹ ∶∶ div2 α)
div2⟨−1:+1:x⟩ : (α : 𝟝ᴺ) → div2 (−1' ∶∶ (+1' ∶∶ α)) ≡ ₃⁰  ∶∶ div2 (−1' ∶∶ α)
div2⟨−1:+2:x⟩ : (α : 𝟝ᴺ) → div2 (−1' ∶∶ (+2' ∶∶ α)) ≡ ₃⁰  ∶∶ (₃⁰ ∶∶ div2 α)
div2⟨+1:−2:x⟩ : (α : 𝟝ᴺ) → div2 (+1' ∶∶ (−2' ∶∶ α)) ≡ ₃⁰  ∶∶ (₃⁰ ∶∶ div2 α)
div2⟨+1:−1:x⟩ : (α : 𝟝ᴺ) → div2 (+1' ∶∶ (−1' ∶∶ α)) ≡ ₃⁰  ∶∶ div2 (+1' ∶∶ α)
div2⟨+1:O:x⟩  : (α : 𝟝ᴺ) → div2 (+1' ∶∶ ( O' ∶∶ α)) ≡ ₃⁰  ∶∶ (₃⁺¹ ∶∶ div2 α)
div2⟨+1:+1:x⟩ : (α : 𝟝ᴺ) → div2 (+1' ∶∶ (+1' ∶∶ α)) ≡ ₃⁺¹ ∶∶ div2 (−1' ∶∶ α)
div2⟨+1:+2:x⟩ : (α : 𝟝ᴺ) → div2 (+1' ∶∶ (+2' ∶∶ α)) ≡ ₃⁺¹ ∶∶ (₃⁰ ∶∶ div2 α)

div2⟨−2:x⟩ α = dfunext (fe 𝓤₀ 𝓤₀) (induction refl λ _ _ → refl)
div2⟨O:x⟩  α = dfunext (fe 𝓤₀ 𝓤₀) (induction refl λ _ _ → refl)
div2⟨+2:x⟩ α = dfunext (fe 𝓤₀ 𝓤₀) (induction refl λ _ _ → refl)
div2⟨−1:−2:x⟩ α = dfunext (fe 𝓤₀ 𝓤₀) γ where
  γ : div2 (−1' ∶∶ (−2' ∶∶ α)) ∼ (₃⁻¹ ∶∶ (₃⁰ ∶∶ div2 α))
  γ 0 = refl
  γ 1 = refl
  γ (succ (succ i)) = refl
div2⟨−1:−1:x⟩ α = dfunext (fe 𝓤₀ 𝓤₀) γ where
  γ : div2 (−1' ∶∶ (−1' ∶∶ α)) ∼ ₃⁻¹ ∶∶ (div2 (+1' ∶∶ α))
  γ 0 = refl
  γ (succ i) = refl
div2⟨−1:O:x⟩ α = dfunext (fe 𝓤₀ 𝓤₀) γ where
  γ : div2 (−1' ∶∶ (O' ∶∶ α)) ∼ (₃⁰ ∶∶ (₃⁻¹ ∶∶ div2 α))
  γ 0 = refl
  γ 1 = refl
  γ (succ (succ i)) = refl
div2⟨−1:+1:x⟩ α = dfunext (fe 𝓤₀ 𝓤₀) γ where
  γ : div2 (−1' ∶∶ (+1' ∶∶ α)) ∼ ₃⁰ ∶∶ (div2 (−1' ∶∶ α))
  γ 0 = refl
  γ (succ i) = refl
div2⟨−1:+2:x⟩ α = dfunext (fe 𝓤₀ 𝓤₀) γ where
  γ : div2 (−1' ∶∶ (+2' ∶∶ α)) ∼ (₃⁰ ∶∶ (₃⁰ ∶∶ div2 α))
  γ 0 = refl
  γ 1 = refl
  γ (succ (succ i)) = refl
div2⟨+1:−2:x⟩ α = dfunext (fe 𝓤₀ 𝓤₀) γ where
  γ : div2 (+1' ∶∶ (−2' ∶∶ α)) ∼ (₃⁰ ∶∶ (₃⁰ ∶∶ div2 α))
  γ 0 = refl
  γ 1 = refl
  γ (succ (succ i)) = refl
div2⟨+1:−1:x⟩ α = dfunext (fe 𝓤₀ 𝓤₀) γ where
  γ : div2 (+1' ∶∶ (−1' ∶∶ α)) ∼ (₃⁰ ∶∶ div2 (+1' ∶∶ α))
  γ 0 = refl
  γ (succ i) = refl
div2⟨+1:O:x⟩ α = dfunext (fe 𝓤₀ 𝓤₀) γ where
  γ : div2 (+1' ∶∶ (O' ∶∶ α)) ∼ (₃⁰ ∶∶ (₃⁺¹ ∶∶ div2 α))
  γ 0 = refl
  γ 1 = refl
  γ (succ (succ i)) = refl
div2⟨+1:+1:x⟩ α = dfunext (fe 𝓤₀ 𝓤₀) γ where
  γ : div2 (+1' ∶∶ (+1' ∶∶ α)) ∼ (₃⁺¹ ∶∶ div2 (−1' ∶∶ α))
  γ 0 = refl
  γ (succ i) = refl
div2⟨+1:+2:x⟩ α = dfunext (fe 𝓤₀ 𝓤₀) γ where
  γ : div2 (+1' ∶∶ (+2' ∶∶ α)) ∼ (₃⁺¹ ∶∶ (₃⁰ ∶∶ div2 α))
  γ 0 = refl
  γ 1 = refl
  γ (succ (succ i)) = refl

{-
transport₁ : (h : 𝟝) (α : 𝟝ᴺ) → M (λ n → q (γa h α n)) ≡ M (λ n → q (γa h (α 0 ∶∶ tail α) n))
transport₁ h α = ap (λ - → M (λ n → q (γa h - n))) (dfunext (fe 𝓤₀ 𝓤₀) γ) where
  γ : α ∼ (α 0 ∶∶ tail α)
  γ 0 = refl
  γ (succ i) = refl

mid-div' : (h : 𝟝) (α : 𝟝ᴺ) (i : ℕ) → M (λ n → q (γa h (h ∶∶ α) (n +ℕ i))) ≡ M (λ n → map half (h ∶∶ α) (n +ℕ i))
mid-div' −2' α zero = M-prop₁ (λ n → q (γa −2' (−2' ∶∶ α) (n +ℕ zero))) ∙ {!!} ∙ M-prop₁ (λ n → map half (−2' ∶∶ α) (n +ℕ zero)) ⁻¹
mid-div' −2' α (succ i) = {!!}
mid-div' −1' α i = {!!}
mid-div' O' α i = {!!}
mid-div' +1' α i = {!!}
mid-div' +2' α i = {!!}

mid-div : (h : 𝟝) (α : 𝟝ᴺ) → 𝕢 (div2 α) ≡ M (map half α) → 𝕢 (div2 (h ∶∶ α)) ≡ M (map half (h ∶∶ α))
mid-div −2' α e = M-prop₁ (λ n → q (div2 (−2' ∶∶ α) n)) ∙ ap (u ⊕_) e ∙ M-prop₁ (map half (−2' ∶∶ α)) ⁻¹
mid-div −1' α e = {!!}
mid-div  O' α e = M-prop₁ (λ n → q (div2 (O' ∶∶ α) n)) ∙ ap (O ⊕_) e ∙ M-prop₁ (map half (O' ∶∶ α)) ⁻¹
mid-div +1' α e = {!!}
mid-div +2' α e = M-prop₁ (λ n → q (div2 (+2' ∶∶ α) n)) ∙ ap (v ⊕_) e ∙ M-prop₁ (map half (+2' ∶∶ α)) ⁻¹
-}

mid-realisability : mid realises² _⊕_
mid-realisability α β = γ (add2 α β) ∙ half-real α β
 where
  γ : (α : 𝟝ᴺ) → 𝕢 (div2 α) ≡ M (map half α)
  γ α = {!!}

data Vec (A : 𝓥 ̇) : ℕ → 𝓥 ̇ where
  [] : Vec A 0
  _∷_ : ∀ {n} → A → Vec A n → Vec A (succ n)

_++_ : {A : 𝓥 ̇} {n : ℕ} → Vec A n → (ℕ → A) → ℕ → A
[] ++ s = s
(x ∷ v) ++ s = x ∶∶ (v ++ s)

hd : {A : 𝓥 ̇ } {n : ℕ} → Vec A (succ n) → A
hd (x ∷ _) = x

first-_ : {A : 𝓥 ̇ } (n : ℕ) → (ℕ → A) → Vec A n
(first- 0) a = []
(first- succ n) a = head a ∷ (first- n) (tail a)

affine-⊕-l : (x a b y : 𝕀) → x ⊕ affine a b y ≡ affine (x ⊕ a) (x ⊕ b) y
affine-⊕-l x a b y = affine-uniqueness·
                       (λ y → x ⊕ affine a b y) (x ⊕ a) (x ⊕ b)
                       (ap (x ⊕_) (affine-equation-l a b))
                       (ap (x ⊕_) (affine-equation-r a b))
                       (λ z y →
                         (ap (x ⊕_) (affine-is-⊕-homomorphism a b z y))
                        ∙ ap (_⊕ (affine a b z ⊕ affine a b y)) (⊕-idem ⁻¹)
                        ∙ ⊕-tran)
                       y ⁻¹

open is-ordered or hiding (M)

𝕀-induction : (P : 𝕀 → 𝓥 ̇ )
            → ((x : 𝕀) → is-prop (P x))
            → P u
            → ((a : ℕ → 𝕀) → ((n : ℕ) → P (a n)) → P (M a))
            → P v
            → (x : 𝕀) → P x
             
≤-affine : (a b i : 𝕀) → a ≤ b → a ≤ affine a b i × affine a b i ≤ b
≤-affine a b i a≤b
 = 𝕀-induction (λ i → a ≤ affine a b i) (λ _ → ≤-prop-valued)
     (transport (a ≤_) (affine-equation-l a b ⁻¹) <-irreflexive)
     (λ α f → transport (a ≤_)
             (⊕-homs-are-M-homs
             (affine a b) (affine-is-⊕-homomorphism a b) α ⁻¹)
             (≤-⊕ₘ f))
     (transport (a ≤_) (affine-equation-r a b ⁻¹) a≤b)
     i
 , 𝕀-induction (λ i → affine a b i ≤ b) (λ _ → ≤-prop-valued)
     (transport (_≤ b) (affine-equation-l a b ⁻¹) a≤b)
     (λ α f → transport (_≤ b)
              (⊕-homs-are-M-homs
              (affine a b) (affine-is-⊕-homomorphism a b) α ⁻¹)
              (≤-⊕ₘ' f))
     (transport (_≤ b) (affine-equation-r a b ⁻¹) <-irreflexive)
     i
                       
M-seq-eq : (a b : 𝕀) → a ≤ b
         → (i : 𝕀) (α : ℕ → 𝕀)
         → let c = affine a b i ⊕ a in
           let d = affine a b i ⊕ b in
           (a ≤ c)
         × (c ≤ d)
         × (d ≤ b)
         × (affine a b (M (i ∶∶ α)) ≡ affine c d (M α))
M-seq-eq a b a≤b i α = a≤c , c≤d , d≤b , γ
 where
  c = affine a b i ⊕ a
  d = affine a b i ⊕ b
  a≤c : a ≤ c
  a≤c = transport (_≤ c) ⊕-idem (≤-⊕₂ (pr₁ (≤-affine a b i a≤b)) <-irreflexive)
  c≤d = ≤-⊕₂ <-irreflexive a≤b
  d≤b = transport (d ≤_) ⊕-idem (≤-⊕₂ (pr₂ (≤-affine a b i a≤b)) <-irreflexive)
  γ = ap (affine a b) (M-prop₁ (i ∶∶ α))
    ∙ affine-is-⊕-homomorphism a b i (M α)
    ∙ affine-⊕-l (affine a b i) a b (M α)

increasing decreasing : (ℕ → 𝕀) → 𝓤₀ ̇
increasing α = (n : ℕ) → α n        ≤ α (succ n)
decreasing α = (n : ℕ) → α (succ n) ≤ α n

tail-_ : {A : 𝓥 ̇ } (n : ℕ) → (ℕ → A) → (ℕ → A)
(tail- 0) α = α
(tail- succ n) α = (tail- n) (tail α)

first-tail-eq : {A : 𝓥 ̇ } (n : ℕ) (α : ℕ → A) → ((first- n) α ++ (tail- n) α) ≡ α
first-tail-eq 0 α = refl
first-tail-eq {𝓥} (succ n) α = dfunext (fe 𝓤₀ 𝓥) γ where
  γ : ((first- succ n) α ++ (tail- succ n) α) ∼ α
  γ 0 = refl
  γ (succ i) = happly (first-tail-eq n (tail α)) i

n-tail-eq : {A : 𝓥 ̇ } (n : ℕ) (α : ℕ → A)
          → (tail- n) α ≡ (α n ∶∶ (tail- n) (α ∘ succ))
n-tail-eq 0 α = first-tail-eq 1 α ⁻¹
n-tail-eq {𝓥} (succ n) α = n-tail-eq n (α ∘ succ)

cs⟨_⟩' ds⟨_⟩' : (ℕ → 𝕀) → 𝕀 → 𝕀 → (ℕ → 𝕀)
cs⟨ α ⟩' a b 0 = a
cs⟨ α ⟩' a b (succ n) = affine (cs⟨ α ⟩' a b n) (ds⟨ α ⟩' a b n) (α n)
                      ⊕ (cs⟨ α ⟩' a b n)
ds⟨ α ⟩' a b 0 = b
ds⟨ α ⟩' a b (succ n) = affine (cs⟨ α ⟩' a b n) (ds⟨ α ⟩' a b n) (α n)
                      ⊕ (ds⟨ α ⟩' a b n)

M-seq-inf : (a b : 𝕀) → a ≤ b → (α : ℕ → 𝕀)
          → let cs = cs⟨ α ⟩' a b in
            let ds = ds⟨ α ⟩' a b in
            (increasing cs) -- (n : ℕ) → cs n ≤ cs (succ n)
          × ((n : ℕ) → cs n ≤ ds n)
          × (decreasing ds)
          × ((n : ℕ)
            → affine a b (M α)
            ≡ affine (cs n) (ds n) (M ((tail- n) α)))
M-seq-inf a b a≤b α = cs→ , cs≤ds , ←ds , γ 
 where
  cs = cs⟨ α ⟩' a b
  ds = ds⟨ α ⟩' a b
  cs≤ds : (n : ℕ) → cs n ≤ ds n
  IH : (n : ℕ) → let c = affine (cs n) (ds n) (α n) ⊕ (cs n) in
                 let d = affine (cs n) (ds n) (α n) ⊕ (ds n) in
                   (cs n ≤ c)
                 × (c ≤ d)
                 × (d ≤ ds n)
                 × (affine (cs n) (ds n) (M (α n ∶∶ (tail- succ n) α))
                  ≡ affine c d (M ((tail- succ n) α)))
  IH n = M-seq-eq (cs n) (ds n) (cs≤ds n) (α n) ((tail- succ n) α)
  cs≤ds 0 = a≤b
  cs≤ds (succ n) = pr₁ (pr₂ (IH n))
  cs→ : increasing cs
  cs→ n = pr₁ (IH n)
  ←ds : decreasing ds
  ←ds n = pr₁ (pr₂ (pr₂ (IH n)))
  γ : (n : ℕ) → affine a b (M α) ≡ affine (cs n) (ds n) (M ((tail- n) α))
  γ 0 = refl
  γ (succ n) = γ n
             ∙ ap (affine (cs n) (ds n)) (ap M (n-tail-eq n α))
             ∙ pr₂ (pr₂ (pr₂ (IH n)))

cs⟨_⟩ ds⟨_⟩ : (ℕ → 𝕀) → (ℕ → 𝕀)
cs⟨ α ⟩ = cs⟨ α ⟩' u v
ds⟨ α ⟩ = ds⟨ α ⟩' u v

M-seq-inf-uv : (α : ℕ → 𝕀)
             → let cs = cs⟨ α ⟩ in
               let ds = ds⟨ α ⟩ in
               (increasing cs)
             × ((n : ℕ) → cs n ≤ ds n)
             × (decreasing ds)
             × ((n : ℕ) → M α ≡ affine (cs n) (ds n) (M ((tail- n) α)))
M-seq-inf-uv α = transport
                   (λ - → let cs = cs⟨ α ⟩ in
                          let ds = ds⟨ α ⟩ in
                          (increasing cs)
                        × ((n : ℕ) → cs n ≤ ds n)
                        × (decreasing ds)
                        × ((n : ℕ)
                          → -
                          ≡ affine (cs n) (ds n) (M ((tail- n) α))))
                 (happly affine-uv-identity (M α))
                 (M-seq-inf u v u≤v α)

cs≤ds : (α : ℕ → 𝕀) (n : ℕ) → cs⟨ α ⟩ n ≤ ds⟨ α ⟩ n
cs≤ds α = pr₁ (pr₂ (M-seq-inf-uv α))
cs-increasing : (α : ℕ → 𝕀) → increasing (cs⟨ α ⟩)
cs-increasing α = pr₁ (M-seq-inf-uv α)
ds-decreasing : (α : ℕ → 𝕀) → decreasing (ds⟨ α ⟩)
ds-decreasing α = pr₁ (pr₂ (pr₂ (M-seq-inf-uv α)))
M-cs-ds : (α : ℕ → 𝕀) (n : ℕ)
        → M α ≡ affine (cs⟨ α ⟩ n) (ds⟨ α ⟩ n) (M ((tail- n) α))
M-cs-ds α = pr₂ (pr₂ (pr₂ (M-seq-inf-uv α)))

_≈_ : (ℕ → 𝕀) → (ℕ → 𝕀) → ℕ → 𝓤 ̇
(α ≈ β) n = (i : ℕ) → i <ℕ n → α i ≡ β i

affine-transport : {a b c d e f : 𝕀}
                 → a ≡ d → b ≡ e → c ≡ f
                 → affine a b c ≡ affine d e f
affine-transport refl refl refl = refl

<ℕ-left-down : (i n : ℕ) → succ i <ℕ n → i <ℕ n
<ℕ-left-down i n si≤n = <-trans i (succ i) n (<-succ i) si≤n

cs-≡ : (α β : ℕ → 𝕀) (n : ℕ) → (α ≈ β) n → (cs⟨ α ⟩ ≈ cs⟨ β ⟩) (succ n)
ds-≡ : (α β : ℕ → 𝕀) (n : ℕ) → (α ≈ β) n → (ds⟨ α ⟩ ≈ ds⟨ β ⟩) (succ n)
cs-≡ α β n α≈β zero i<n = refl
cs-≡ α β n α≈β (succ i) i<n
  = ap (_⊕ cs⟨ α ⟩ i)
      (affine-transport
        (cs-≡ α β n α≈β i (<ℕ-left-down i (succ n) i<n))
        (ds-≡ α β n α≈β i (<ℕ-left-down i (succ n) i<n))
        (α≈β i i<n))
    ∙ ap (affine (cs⟨ β ⟩ i) (ds⟨ β ⟩ i) (β i) ⊕_)
        (cs-≡ α β n α≈β i (<ℕ-left-down i (succ n) i<n))
ds-≡ α β n α≈β zero i<n = refl
ds-≡ α β n α≈β (succ i) i<n
  = ap (_⊕ ds⟨ α ⟩ i)
      (affine-transport
        (cs-≡ α β n α≈β i (<ℕ-left-down i (succ n) i<n))
        (ds-≡ α β n α≈β i (<ℕ-left-down i (succ n) i<n))
        (α≈β i i<n))
    ∙ ap (affine (cs⟨ β ⟩ i) (ds⟨ β ⟩ i) (β i) ⊕_)
        (ds-≡ α β n α≈β i (<ℕ-left-down i (succ n) i<n))
     
append-one : {X : 𝓤 ̇ } → X → (n : ℕ) → Vec X n → Vec X (succ n)
append-one y zero [] = y ∷ []
append-one y (succ n) (x ∷ xs) = x ∷ append-one y n xs

𝕀-induction = {!!}

u-sequence : (a : ℕ → 𝕀) → u ≡ M a → (n : ℕ) → u ≡ a n
u-sequence a u≡Ma n = {!!}

cancellation : (a b c : 𝕀) → a ⊕ b ≡ a ⊕ c → b ≡ c
cancellation a b c = 𝕀-induction (λ a → a ⊕ b ≡ a ⊕ c → b ≡ c)
                       (λ _ → Π-is-prop (fe 𝓤 𝓤) (λ _ → 𝕀-set))
                       {!!}
                       {!!}
                       {!!}
                       a
 where
   xx-cancellation : {i x : 𝕀} → i ⊕ x ≡ i ⊕ x → x ≡ x
   xx-cancellation _ = refl
   uuv-cancellation : u ⊕ u ≡ u ⊕ v → u ≡ v
   uuv-cancellation p =     u       ≡⟨ ⊕-idem ⁻¹ ⟩
                          u ⊕ u     ≡⟨ p ⟩ 
                          u ⊕ v     ≡⟨ ⊕-comm ⟩
                          v ⊕ u     ≡⟨ ap (_⊕ u) (−1-inverse ⁻¹) ⟩
                        − u ⊕ u     ≡⟨ ap (− u ⊕_) (+1-inverse ⁻¹) ⟩
                        − u ⊕ − v   ≡⟨ −-is-⊕-homomorphism u v ⁻¹ ⟩
                       − (u ⊕ v)    ≡⟨ ap −_ (p ⁻¹) ⟩
                       − (u ⊕ u)    ≡⟨ ap −_ ⊕-idem ⟩
                           − u      ≡⟨ −1-inverse ⟩
                            v       ∎
   uMu-cancellation : (a : ℕ → 𝕀) → ((n : ℕ) → (u ⊕ a n) ≡ (u ⊕ u) → a n ≡ u)
                                    → (u ⊕ M a) ≡ (u ⊕ u) → M a ≡ u
   uMu-cancellation a f p = M a         ≡⟨ ap M (dfunext (fe 𝓤₀ 𝓤)
                                           (λ i → f i (s i ∙ ⊕-idem ⁻¹))) ⟩
                            M (λ _ → u) ≡⟨ M-idem u ⟩
                            u           ∎
     where
       r : u ≡ M (λ n → u ⊕ a n)
       r =   u    ≡⟨ ⊕-idem ⁻¹ ⟩
           u ⊕ u  ≡⟨ transport ((u ⊕ u) ≡_)
                       (M-hom (λ _ → u) a)
                       (p ⁻¹ ∙ ap (_⊕ M a) (M-idem u ⁻¹)) ⟩
           M (λ n → u ⊕ a n) ∎
       s : (i : ℕ) → (u ⊕ a i) ≡ u 
       s i = u-sequence (λ n → u ⊕ a n) r i ⁻¹
   uMv-cancellation : (a : ℕ → 𝕀) → ((n : ℕ) → (u ⊕ a n) ≡ (u ⊕ v) → a n ≡ v)
                                    → (u ⊕ M a) ≡ (u ⊕ v) → M a ≡ v
   uMv-cancellation a f p = M a         ≡⟨ ap M (dfunext (fe 𝓤₀ 𝓤)
                                           (λ i → f i (s i))) ⟩
                            M (λ _ → v) ≡⟨ M-idem v ⟩
                            v           ∎
     where
       r : u ⊕ v ≡ M (λ n → u ⊕ a n)
       r = u ⊕ v  ≡⟨ transport ((u ⊕ v) ≡_)
                       (M-hom (λ _ → u) a)
                       (p ⁻¹ ∙ ap (_⊕ M a) (M-idem u ⁻¹)) ⟩
           M (λ n → u ⊕ a n) ∎
       s : (i : ℕ) → (u ⊕ a i) ≡ (u ⊕ v)
       s i = {!!}

-- affine x y b ≡ affine x y c → x ≢ y → b ≡ c

m : (n : ℕ) → Vec 𝕀 (succ n) → 𝕀
m zero (x ∷ []) = x
m (succ n) (x ∷ xs) = x ⊕ m n xs

constant-vec : {X : 𝓤 ̇ } → X → (n : ℕ) → Vec X n
constant-vec x n = (first- n) (λ _ → x)

approximation : 𝓤 ̇
approximation = (x y : ℕ → 𝕀)
              → (Π n ꞉ ℕ , Σ z ꞉ 𝕀 , Σ w ꞉ 𝕀
                 , m n (append-one z n ((first- n) x)) -- x ++ [z]
                 ≡ m n (append-one w n ((first- n) y))) -- y ++ [w]
              → M x ≡ M y

approximation' : 𝓤 ̇
approximation' = (x y : ℕ → 𝕀)
               → (Σ z ꞉ (ℕ → 𝕀) , Σ w ꞉ (ℕ → 𝕀) , Π n ꞉ ℕ
                  , m n (append-one (z n) n ((first- n) x))
                  ≡ m n (append-one (w n) n ((first- n) y)))
               → M x ≡ M y
   
M-prop₁-n : (α : ℕ → 𝕀) (n : ℕ)
          → M α ≡ m n (append-one (M ((tail- n) α)) n ((first- n) α))
M-prop₁-n α zero = refl
M-prop₁-n α (succ n) = M-prop₁ α ∙ ap (α 0 ⊕_) (M-prop₁-n (α ∘ succ) n)

m-seq-fin' : (α : ℕ → 𝕀) (n : ℕ)
           → m n (append-one (M ((tail- n) α)) n ((first- n) α))
           ≡ affine (cs⟨ α ⟩ n) (ds⟨ α ⟩ n) (M ((tail- n) α))
m-seq-fin' α n = M-prop₁-n α n ⁻¹ ∙ M-cs-ds α n

tail-++ : (α β : ℕ → 𝕀) (n : ℕ) → (tail- n) (((first- n) α) ++ β) ≡ β
tail-++ α β zero = refl
tail-++ α β (succ n) = tail-++ (α ∘ succ) β n

first-++ : (α β : ℕ → 𝕀) (n : ℕ)
         → (first- n) ((first- n) α ++ β) ≡ (first- n) α
first-++ α β zero = refl
first-++ α β (succ n) = ap (α 0 ∷_) (first-++ (α ∘ succ) β n)

first-≈ : (α β : ℕ → 𝕀) (n : ℕ) → (((first- n) α ++ β) ≈ α) n
first-≈ α β (succ n) zero i<n = refl
first-≈ α β (succ n) (succ i) i<n = first-≈ (α ∘ succ) β n i i<n

m-seq-fin : (α : ℕ → 𝕀) (z : 𝕀) (n : ℕ)
          → m n (append-one z n ((first- n) α))
          ≡ affine (cs⟨ α ⟩ n) (ds⟨ α ⟩ n) z
m-seq-fin α z n = ap (λ - → m n (append-one z n -)) first-≡
                ∙ ap (λ - → m n (append-one - n ((first- n) β))) tail-≡
                ∙ m-seq-fin' β n
                ∙ affine-transport
                    (cs-≡ β α n (first-≈ α (λ _ → z) n) n (<-succ n))
                    (ds-≡ β α n (first-≈ α (λ _ → z) n) n (<-succ n))
                    (tail-≡ ⁻¹)
 where
  β : ℕ → 𝕀
  β = ((first- n) α) ++ (λ _ → z)
  first-≡ : ((first- n) α) ≡ ((first- n) β)
  first-≡ = first-++ α (λ _ → z) n ⁻¹
  tail-≡  : z ≡ (M ((tail- n) β))
  tail-≡  = (M-idem z ⁻¹) ∙ (ap M (tail-++ α (λ _ → z) n ⁻¹))

approximation'' : 𝓤 ̇
approximation'' = (x y : ℕ → 𝕀)
                → ((n : ℕ) → Σ z ꞉ 𝕀 , Σ w ꞉ 𝕀
                   , affine (cs⟨ x ⟩ n) (ds⟨ x ⟩ n) z
                   ≡ affine (cs⟨ y ⟩ n) (ds⟨ y ⟩ n) w)
                → M x ≡ M y

approx''→approx : approximation'' → approximation
approx''→approx a x y f = a x y γ
 where
   γ : (n : ℕ) →
         Sigma 𝕀
         (λ z →
            Sigma 𝕀
            (λ w →
               affine (cs⟨ x ⟩ n) (ds⟨ x ⟩ n) z ≡
               affine (cs⟨ y ⟩ n) (ds⟨ y ⟩ n) w))
   γ n = z , w
       , (m-seq-fin x z n ⁻¹
        ∙ δ
        ∙ m-seq-fin y w n)
    where
      z = pr₁ (f n)
      w = pr₁ (pr₂ (f n))
      δ = pr₂ (pr₂ (f n))


within : (a b c d : 𝕀) → a ≤ b → c ≤ d → 𝓤₀ ̇
within a b c d a≤b c≤d = (a ≤ d) × (c ≤ b)

within-cs-ds : (ℕ → 𝕀) → (ℕ → 𝕀) → 𝓤₀ ̇
within-cs-ds α β = (n : ℕ)
                 → within (cs⟨ α ⟩ (succ n)) (ds⟨ α ⟩ (succ n))
                          (cs⟨ β ⟩ (succ n)) (ds⟨ β ⟩ (succ n))
                          (cs≤ds α (succ n)) (cs≤ds β (succ n))

half-div2-within : (α : 𝟝ᴺ) → within-cs-ds (λ n → q (div2 (−2' ∶∶ α) n))
                                            (map half (−2' ∶∶ α))
half-div2-within α n = ?
within-inf : (α β : ℕ → 𝕀)
           → ((n : ℕ)
             → within (cs⟨ α ⟩ n) (ds⟨ α ⟩ n)
                      (cs⟨ β ⟩ n) (ds⟨ β ⟩ n)
                      (cs≤ds α n) (cs≤ds β n))
           → M α ≡ M β
within-inf α β f = {!!}

within-approx : (a b c d : 𝕀)
              → within a b c d {!!} {!!}
              → Σ (z , w) ꞉ (𝕀 × 𝕀) , (affine a b z ≡ affine c d w)
within-approx a b c d = {!!}
           

approx→approx' : approximation → approximation'
approx→approx' f x y (zs , ws , γ) = f x y (λ n → zs n , ws n , γ n)

approx'→approx : approximation' → approximation
approx'→approx f x y g = f x y
                           ((λ n → pr₁ (g n))
                         , ((λ n → pr₁ (pr₂ (g n)))
                         , (λ n → pr₂ (pr₂ (g n)))))

unfold : cancellative fe _⊕_
       → (x : 𝕀) (y : ℕ → 𝕀) (w : ℕ → 𝕀)
       → ((n : ℕ) → x ≡ m n (append-one (w n) n ((first- n) y)))
       → (i : ℕ) → Σ z ꞉ 𝕀
       , (((z ⊕ w i) ≡ m i (append-one (w i) i ((first- i) y)))
       × (m (succ i) (append-one (w (succ i)) (succ i) ((first- succ i) y))
          ≡ (z ⊕ (y i ⊕ w (succ i)))))
unfold c x y w f zero = w 0 , ⊕-idem , {!!}
unfold c x y w f (succ i) = {!!}

one-sided-approximation : cancellative fe _⊕_
                      → (x : 𝕀) (y : ℕ → 𝕀)
                      → (Σ w ꞉ (ℕ → 𝕀) , Π n ꞉ ℕ
                      , x ≡ m n (append-one (w n) n ((first- n) y)))
                      → x ≡ M y
one-sided-approximation c x y (w , f) = {!!} -- M-prop₂ w' y (induction (f 0 ∙ γ 0) (λ k _ → γ (succ k)))
 where
   w' : ℕ → 𝕀
   w' 0 = x
   w' (succ n) = w (succ n)
   p : x ≡ w 0
   p = f 0
   γ : (i : ℕ) → w i ≡ (y i ⊕ w (succ i))
   γ i = c (w i) (y i ⊕ w (succ i)) (pr₁ (unfold c x y w f i))
         (⊕-comm ∙ pr₁ (pr₂ (unfold c x y w f i))
          ∙ f i ⁻¹ ∙ f (succ i)
          ∙ {!!} ∙ ⊕-comm)

cancellation-implies-approximation : cancellative fe _⊕_ → approximation
cancellation-implies-approximation c x y f
 = M x ≡⟨ c (M x) (M y) (M z) (seven 0) ⟩
   M y ∎ 
 where
  z w : ℕ → 𝕀
  z n = pr₁ (f (succ n))
  w n = pr₁ (pr₂ (f (succ n)))
  next : (x y : ℕ → 𝕀) (n : ℕ)
       → M (λ i → x i ⊕ y i)
       ≡ (m (succ n) (append-one (y n) (succ n) ((first- succ n) x)))
       ⊕ (M ((first- n) y ++ λ i → x (succ (n +ℕ i)) ⊕ y (succ (n +ℕ i))))
  next x y zero = M-prop₁ (λ i → x i ⊕ y i)
                ∙ ap (λ - → (x 0 ⊕ y 0) ⊕ M -)
                  (dfunext (fe 𝓤₀ 𝓤) 
                  (λ i → ap (λ - → x (succ -) ⊕ y (succ -))
                         (zero-left-neutral i ⁻¹)))
  next x y (succ n)
   = M-prop₁ (λ i → x i ⊕ y i)
   ∙ ap ((x 0 ⊕ y 0) ⊕_) (next (x ∘ succ) (y ∘ succ) n)
   ∙ ⊕-tran
   ∙ ap ((x 0 ⊕ m (succ n)
         (append-one (y (succ n)) (succ n) ((first- (succ n)) (x ∘ succ))))
         ⊕_)
        (ap (λ - → y 0 ⊕ M (((first- n) (y ∘ succ)) ++ -))
          (dfunext (fe 𝓤₀ 𝓤)
          (λ i → ap (λ - → x (succ -) ⊕ y (succ -))
                 (δ n i)))
        ∙ M-prop₁ ((first- succ n) y ++ (λ i → x (succ (succ n +ℕ i))
                  ⊕ y (succ (succ n +ℕ i)))) ⁻¹)
    where
      δ : (n i : ℕ) → succ (n +ℕ i) ≡ succ n +ℕ i
      δ n zero = refl
      δ n (succ i) = ap succ (δ n i)
  seven : (n : ℕ) → M x ⊕ M z ≡ M y ⊕ M z
  seven n = M x ⊕ M z             ≡⟨ M-hom x z ⟩
            M (λ i → x i ⊕ z i)   ≡⟨ next x z n ⟩
            (m (succ n)
              (append-one (pr₁ (f (succ n))) (succ n) ((first- succ n) x))
              ⊕
              M
              ((first- n) (λ n₁ → pr₁ (f (succ n₁))) ++
               (λ i → x (succ (n +ℕ i)) ⊕ pr₁ (f (succ (succ (n +ℕ i)))))))                 ≡⟨ one-sided-approximation c _ (λ i → y i ⊕ z i) {!!} ⟩
            M (λ i → y i ⊕ z i) ≡⟨ M-hom y z ⁻¹ ⟩
            M y ⊕ M z  ∎
   where
     γ : (j : ℕ) → M (λ i → x i ⊕ z i) ≡ m j (append-one (w j) j ((first- j) (λ i → y i ⊕ z i)))
     γ j = M (λ i → x i ⊕ z i)
                               ≡⟨ next x z j ⟩
           (m (succ j) (append-one (z j) (succ j) ((first- succ j) x))
             ⊕ M ((first- j) z ++ (λ i → x (succ (j +ℕ i)) ⊕ z (succ (j +ℕ i)))))
                               ≡⟨ ap (_⊕ M ((first- j) z ++ (λ i → x (succ (j +ℕ i)) ⊕ z (succ (j +ℕ i)))))
                                     (pr₂ (pr₂ (f (succ j)))) ⟩
           (m (succ j) (append-one (w j) (succ j) ((first- succ j) y))
             ⊕ M ((first- j) z ++ (λ i → x (succ (j +ℕ i)) ⊕ z (succ (j +ℕ i)))))
                               ≡⟨ {!next y z j ⁻¹!} ⟩
           y j ≡⟨ {!!} ⟩
           m j (append-one (w j) j ((first- j) (λ i → y i ⊕ z i))) ∎
  
approximation-implies-cancellation : approximation → cancellative fe _⊕_
approximation-implies-cancellation f x y z x⊕z≡y⊕z
 = transport (_≡ y) (M-idem x) (transport (M (λ _ → x) ≡_) (M-idem y)
   (f (λ _ → x) (λ _ → y) (λ n → z , z , m-idem n)))
 where
   m-idem : (n : ℕ) → m n (append-one z n (constant-vec x n))
                    ≡ m n (append-one z n (constant-vec y n))
   m-idem zero = refl
   m-idem (succ zero) = x⊕z≡y⊕z
   m-idem (succ (succ n))
    =    x    ⊕ (x ⊕ w)  ≡⟨ ap (_⊕ (x ⊕ w)) (⊕-idem ⁻¹) ⟩
      (x ⊕ x) ⊕ (x ⊕ w)  ≡⟨ ap ((x ⊕ x) ⊕_) (m-idem (succ n)
                          ∙ ap (y ⊕_) (m-idem n ⁻¹)) ⟩
      (x ⊕ x) ⊕ (y ⊕ w)  ≡⟨ ⊕-tran ⟩
      (x ⊕ y) ⊕ (x ⊕ w)  ≡⟨ ap ((x ⊕ y) ⊕_) (m-idem (succ n)
                          ∙ ap (y ⊕_) (m-idem n ⁻¹)) ⟩
      (x ⊕ y) ⊕ (y ⊕ w)  ≡⟨ ap (_⊕ (y ⊕ w)) ⊕-comm ⟩
      (y ⊕ x) ⊕ (y ⊕ w)  ≡⟨ ⊕-tran ⟩
      (y ⊕ y) ⊕ (x ⊕ w)  ≡⟨ ap ((y ⊕ y) ⊕_) (m-idem (succ n)
                          ∙ ap (y ⊕_) (m-idem n ⁻¹)) ⟩
      (y ⊕ y) ⊕ (y ⊕ w)  ≡⟨ ap (_⊕ (y ⊕ w)) ⊕-idem ⟩
         y    ⊕ (y ⊕ w)  ≡⟨ ap (λ - → y ⊕ (y ⊕ -)) (m-idem n) ⟩
         y    ⊕ (y ⊕ w') ∎
    where
      w  = m n (append-one z n (constant-vec x n))
      w' = m n (append-one z n (constant-vec y n))      
