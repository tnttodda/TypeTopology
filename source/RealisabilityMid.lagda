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
 (hd : has-double fe 𝓤 io)
 (pt : propositional-truncations-exist)
 (or : is-ordered fe pt io)
 where

open import UF-Base
open import DiscreteAndSeparated
open import Sequence fe
open import NaturalsAddition renaming (_+_ to _+ℕ_)
open import UF-Subsingletons
open import UF-Subsingletons-FunExt

open basic-interval-object-development fe io hd

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
δc −1' α (succ n) = div2 (+1' ∶∶ tail α) n
δc +1' α 0 = ₃⁺¹
δc +1' α (succ n) = div2 (−1' ∶∶ tail α) n    

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
δb −1' α (succ n) = div2 (+1' ∶∶ tail α) n
δb +1' _ 0 = ₃⁰
δb +1' α (succ n) = div2 (−1' ∶∶ tail α) n

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

first-_ : {A : 𝓥 ̇ } (n : ℕ) → (ℕ → A) → Vec A n
(first- 0) a = []
(first- succ n) a = head a ∷ (first- n) (tail a)

affine-⊕-l : (x a b y : 𝕀) → x ⊕ affine a b y ≡ affine (x ⊕ a) (x ⊕ b) y
affine-⊕-l x a b y = affine-uniqueness· (λ y → x ⊕ affine a b y) (x ⊕ a) (x ⊕ b)
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
≤-affine a b i a≤b = 𝕀-induction (λ i → a ≤ affine a b i) (λ _ → ≤-prop-valued)
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
         → Σ c ꞉ 𝕀 , Σ d ꞉ 𝕀 ,
           (a ≤ c)
         × (c ≤ d)
         × (d ≤ b)
         × (affine a b (M (i ∶∶ α)) ≡ affine c d (M α))
M-seq-eq a b a≤b i α = c , d , a≤c , c≤d , d≤b , γ
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

tail-_ : {A : 𝓥 ̇ } (n : ℕ) → (ℕ → A) → (ℕ → A)
(tail- 0) α = α
(tail- succ n) α = (tail- n) (tail α)

increasing decreasing : (ℕ → 𝕀) → 𝓤₀ ̇
increasing α = (n : ℕ) → α n        ≤ α (succ n)
decreasing α = (n : ℕ) → α (succ n) ≤ α n


M-thing : (a b : 𝕀) → a ≤ b → {n : ℕ}
          → (v : Vec 𝕀 n) (α : ℕ → 𝕀)
          → Σ c ꞉ 𝕀 , Σ d ꞉ 𝕀 ,
            (a ≤ c)
          × (c ≤ d)
          × (d ≤ b)
          × (affine a b (M (v ++ α)) ≡ affine c d (M α))
M-thing a b a≤b [] α = a , b , ≤-reflexive , a≤b , ≤-reflexive , refl
M-thing a b a≤b (x ∷ v) α = IHc , IHd , ≤-trans Ha≤c IHa≤c , IHc≤d , ≤-trans IHd≤b Hd≤b
                            , (Hγ ∙ IHγ)
 where
  H = M-seq-eq a b a≤b x (v ++ α)
  Hc   = pr₁ H
  Hd   = pr₁ (pr₂ H)
  Ha≤c = pr₁ (pr₂ (pr₂ H))
  Hc≤d = pr₁ (pr₂ (pr₂ (pr₂ H)))
  Hd≤b = pr₁ (pr₂ (pr₂ (pr₂ (pr₂ H))))
  Hγ : affine a b (M (x ∶∶ (v ++ α))) ≡
         affine (pr₁ H) (pr₁ (pr₂ H)) (M (v ++ α))
  Hγ   = pr₂ (pr₂ (pr₂ (pr₂ (pr₂ H))))
  IH = M-thing Hc Hd Hc≤d v α
  IHc   = pr₁ IH
  IHd   = pr₁ (pr₂ IH)
  IHa≤c = pr₁ (pr₂ (pr₂ IH))
  IHc≤d = pr₁ (pr₂ (pr₂ (pr₂ IH)))
  IHd≤b = pr₁ (pr₂ (pr₂ (pr₂ (pr₂ IH))))
  IHγ : affine Hc Hd (M (v ++ α)) ≡ affine (pr₁ IH) (pr₁ (pr₂ IH)) (M α)
  IHγ   = pr₂ (pr₂ (pr₂ (pr₂ (pr₂ IH))))

first-tail-eq : {A : 𝓥 ̇ } (n : ℕ) (α : ℕ → A) → ((first- n) α ++ (tail- n) α) ≡ α
first-tail-eq 0 α = refl
first-tail-eq {𝓥} (succ n) α = dfunext (fe 𝓤₀ 𝓥) γ where
  γ : ((first- succ n) α ++ (tail- succ n) α) ∼ α
  γ 0 = refl
  γ (succ i) = happly (first-tail-eq n (tail α)) i 

M-seq-inf : (a b : 𝕀) → a ≤ b
          → (α : ℕ → 𝕀)
          → Σ cs ꞉ (ℕ → 𝕀) , Σ ds ꞉ (ℕ → 𝕀) ,
            increasing cs × decreasing ds
          × ((n : ℕ)
          → affine a      b      (M α)
          ≡ affine (cs n) (ds n) (M ((tail- n) α)))
M-seq-inf a b a≤b α = cs , ds , cs≤cs , ds≤ds , γ -- cs , ds , {!!} , {!!} , γ
 where
  IH = λ n → M-thing a b a≤b ((first- n) α) ((tail- n) α) 
  cs = λ n → pr₁ (IH n)
  ds = λ n → pr₁ (pr₂ (IH n))
  γ : (n : ℕ) → affine a b (M α) ≡ affine (cs n) (ds n) (M ((tail- n) α))
  γ n = transport
          (λ - → affine a b (M -) ≡ affine (cs n) (ds n) (M ((tail- n) α)))
          (first-tail-eq n α)
          (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ (IH n))))))
  cs≤cs : increasing cs
  cs≤cs n = {!!}
  ds≤ds : decreasing ds
  ds≤ds = {!!}
  IH₂ : (h : 𝕀) (n : ℕ) → affine (cs n) (ds n) (M ({!!} ∶∶ (tail- n) α))
                ≡ affine (cs (succ n)) (ds (succ n)) (M ((tail- n) α))
  IH₂ n = {!!}
   
𝕀-induction = {!!}

{-
is-interval-object : (𝓘 : Convex-body 𝓤) (𝓥 : Universe) → ⟨ 𝓘 ⟩ → ⟨ 𝓘 ⟩ → 𝓤 ⊔ 𝓥 ⁺ ̇
is-interval-object 𝓘 𝓥 u v =
    (𝓐 : Convex-body 𝓥) (a b : ⟨ 𝓐 ⟩) -- h = affine a b
   → ∃! h ꞉ (⟨ 𝓘 ⟩ → ⟨ 𝓐 ⟩) , (h u ≡ a)
                            × (h v ≡ b)
                            × ((x y : ⟨ 𝓘 ⟩) → h (x ⊕⟨ 𝓘 ⟩ y) ≡ h x ⊕⟨ 𝓐 ⟩ h y)
-}

affine-cancellation : (x y b c : 𝕀)
                    → affine x y b ≡ affine x y c
                    → b ≡ c
affine-cancellation x y b c = {!!}

u-cancellation : (a b c : 𝕀) → u ⊕ b ≡ u ⊕ c → b ≡ c
u-cancellation a b c u⊕b≡u⊕c = {!!}
 -- affine u (u ⊕ v) b ≡ affine u (u ⊕ v) c
 -- affine u v b ≡ affine u v c

v-cancellation : (a b c : 𝕀) → v ⊕ b ≡ v ⊕ c → b ≡ c
v-cancellation = {!!}

M-cancellation : {!!}
M-cancellation = {!!}

cancellation : (a b c : 𝕀) → a ⊕ b ≡ a ⊕ c → b ≡ c
cancellation a b c = 𝕀-induction (λ a → a ⊕ b ≡ a ⊕ c → b ≡ c)
                       (λ _ → Π-is-prop (fe 𝓤 𝓤) (λ _ → 𝕀-set))
                       {!!}
                       {!!}
                       {!!}
                       a

m : (n : ℕ) → Vec 𝕀 (succ n) → 𝕀
m zero (x ∷ []) = x
m (succ n) (x ∷ xs) = x ⊕ m n xs

constant-vec : {X : 𝓤 ̇ } → X → (n : ℕ) → Vec X n
constant-vec x zero = []
constant-vec x (succ n) = x ∷ constant-vec x n

append-one : {X : 𝓤 ̇ } → X → (n : ℕ) → Vec X n → Vec X (succ n)
append-one y zero [] = y ∷ []
append-one y (succ n) (x ∷ xs) = x ∷ append-one y n xs

approximation : 𝓤 ̇
approximation = (x y : ℕ → 𝕀)
              → (Π n ꞉ ℕ , Σ z ꞉ 𝕀 , Σ w ꞉ 𝕀
                 , m n (append-one z n ((first- n) x))
                 ≡ m n (append-one w n ((first- n) y)))
              → M x ≡ M y

first-constant-≡ : (x : 𝕀) (n : ℕ) → (first- n) (λ _ → x) ≡ constant-vec x n
first-constant-≡ x zero = refl
first-constant-≡ x (succ n) = ap (x ∷_) (first-constant-≡ x n)

approximation-implies-cancellation : approximation → cancellative fe _⊕_
approximation-implies-cancellation f x y z x⊕z≡y⊕z
 = transport (_≡ y) (M-idem x) (transport (M (λ _ → x) ≡_) (M-idem y)
   (f (λ _ → x) (λ _ → y) (λ n → z , z ,
      (ap (λ - → m n (append-one z n -)) (first-constant-≡ x n)
     ∙ m-idem n
     ∙ ap (λ - → m n (append-one z n -)) (first-constant-≡ y n ⁻¹)))))
 where
   m-idem : (n : ℕ)
          → m n (append-one z n (constant-vec x n))
          ≡ m n (append-one z n (constant-vec y n))
   m-idem zero = refl
   m-idem (succ zero) = x⊕z≡y⊕z
   m-idem (succ (succ n))
    = x ⊕ (x ⊕ w)
    ≡⟨ ap (_⊕ (x ⊕ w)) (⊕-idem ⁻¹) ⟩
      (x ⊕ x) ⊕ (x ⊕ w)
    ≡⟨ ap ((x ⊕ x) ⊕_) (m-idem (succ n) ∙ ap (y ⊕_) (m-idem n ⁻¹)) ⟩
      (x ⊕ x) ⊕ (y ⊕ w)
    ≡⟨ ⊕-tran ⟩
      (x ⊕ y) ⊕ (x ⊕ w)
    ≡⟨ ap ((x ⊕ y) ⊕_) (m-idem (succ n) ∙ ap (y ⊕_) (m-idem n ⁻¹)) ⟩
      (x ⊕ y) ⊕ (y ⊕ w)
    ≡⟨ ap (_⊕ (y ⊕ w)) ⊕-comm ⟩
      (y ⊕ x) ⊕ (y ⊕ w)
    ≡⟨ ⊕-tran ⟩
      (y ⊕ y) ⊕ (x ⊕ w)
    ≡⟨ ap ((y ⊕ y) ⊕_) (m-idem (succ n) ∙ ap (y ⊕_) (m-idem n ⁻¹)) ⟩
      (y ⊕ y) ⊕ (y ⊕ w)
    ≡⟨ ap (_⊕ (y ⊕ w)) ⊕-idem ⟩
      y ⊕ (y ⊕ w)
    ≡⟨ ap (λ - → y ⊕ (y ⊕ -)) (m-idem n) ⟩
      (y ⊕ (y ⊕ w')) ∎
    where
      w  = m n (append-one z n (constant-vec x n))
      w' = m n (append-one z n (constant-vec y n))      
