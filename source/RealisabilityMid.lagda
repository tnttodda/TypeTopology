\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-FunExt
open import Escardo-Simpson-LICS2001
open import UF-PropTrunc
open import OrderedIntervalObject

module RealisabilityMid
 (fe : FunExt)
 (io : Interval-object fe 𝓤)
 (db : has-double fe 𝓤 io)
 (pt : propositional-truncations-exist)
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

data 𝟛 : 𝓤₀ ̇ where
  ₃⁰ ₃⁺¹ ₃⁻¹ : 𝟛

𝟛ᴺ : 𝓤₀ ̇
𝟛ᴺ = ℕ → 𝟛

q : 𝟛 → 𝕀
q ₃⁻¹ = −1
q ₃⁰  =  O
q ₃⁺¹ = +1

map : {X : 𝓥 ̇ } {Y : 𝓦 ̇ } → (X → Y) → (ℕ → X) → (ℕ → Y)
map f α n = f (α n)

𝕢 : 𝟛ᴺ → 𝕀
𝕢 α = M (map q α)

neg : 𝟛 → 𝟛
neg ₃⁻¹ = ₃⁺¹
neg  ₃⁰ = ₃⁰
neg ₃⁺¹ = ₃⁻¹

_realises¹_ : (𝟛ᴺ → 𝟛ᴺ) → (𝕀 → 𝕀) → 𝓤 ̇
ϕ realises¹ f = Π α ꞉ 𝟛ᴺ , (𝕢 (ϕ α) ≡ f (𝕢 α))

_realises²_ : (𝟛ᴺ → 𝟛ᴺ → 𝟛ᴺ) → (𝕀 → 𝕀 → 𝕀) → 𝓤 ̇
_*³_ realises² _*ᴵ_ = Π α ꞉ 𝟛ᴺ , Π β ꞉ 𝟛ᴺ , (𝕢 (α *³ β) ≡ 𝕢 α *ᴵ 𝕢 β)

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

data Vec (A : 𝓥 ̇) : ℕ → 𝓥 ̇ where
  [] : Vec A 0
  _∷_ : ∀ {n} → A → Vec A n → Vec A (succ n)

first-_ : {A : 𝓥 ̇ } (n : ℕ) → (ℕ → A) → Vec A n
(first- 0) a = []
(first- succ n) a = head a ∷ (first- n) (tail a)

append-one : {X : 𝓤 ̇ } → X → (n : ℕ) → Vec X n → Vec X (succ n)
append-one y zero [] = y ∷ []
append-one y (succ n) (x ∷ xs) = x ∷ append-one y n xs

m : (n : ℕ) → Vec 𝕀 (succ n) → 𝕀
m 0 (x ∷ []) = x
m (succ n) (x ∷ xs) = x ⊕ m n xs

approximation : 𝓤 ̇
approximation = (x y : ℕ → 𝕀)
              → (Π n ꞉ ℕ , Σ (z , w) ꞉ 𝕀 × 𝕀
                 , m n (append-one z n ((first- n) x))
                 ≡ m n (append-one w n ((first- n) y)))
              → M x ≡ M y

n-approx' : ℕ → (ℕ → 𝕀) → (ℕ → 𝕀) → 𝓤 ̇
n-approx' n x y = Σ (z , w) ꞉ 𝕀 × 𝕀
                , m (succ n) (append-one z (succ n) ((first- (succ n)) x))
                ≡ m (succ n) (append-one w (succ n) ((first- (succ n)) y))

⊕-hom-l : {a b c : 𝕀} → a ⊕ (b ⊕ c) ≡ (a ⊕ b) ⊕ (a ⊕ c)
⊕-hom-l {a} {b} {c} = ⊕-is-⊕-homomorphism-r fe 𝓘 a b c

half-div2-approx : (a b : 𝟝) (α : 𝟝ᴺ) (n : ℕ)
                 → n-approx' n (map q (div2 (a ∶∶ (b ∶∶ α))))
                               (map half (a ∶∶ (b ∶∶ α)))

half-div2-approx −2' b α 0 = (u , u) , refl
half-div2-approx −2' b α (succ n)
 = pr₁ IH , ap (u ⊕_) (pr₂ IH)
 where
  IH : n-approx' n (map q (div2 (b ∶∶ α))) (map half (b ∶∶ α))
  IH = transport (λ - → n-approx' n (λ i → q (div2 (b ∶∶ -) i))
                                    (map half (b ∶∶ -)))
         head-tail-eta
         (half-div2-approx b (head α) (tail α) n)

half-div2-approx  O' b α 0 = (u , u) , refl
half-div2-approx  O' b α (succ n)
 = pr₁ IH , ap ((u ⊕ v) ⊕_) (pr₂ IH)
 where
  IH : n-approx' n (map q (div2 (b ∶∶ α))) (map half (b ∶∶ α))
  IH = transport (λ - → n-approx' n (map q (div2 (b ∶∶ -)))
                                    (map half (b ∶∶ -)))
         head-tail-eta
         (half-div2-approx b (head α) (tail α) n)

half-div2-approx +2' b α 0 = (u , u) , refl
half-div2-approx +2' b α (succ n)
 = pr₁ IH , ap (v ⊕_) (pr₂ IH)
 where
  IH : n-approx' n (map q (div2 (b ∶∶ α))) (map half (b ∶∶ α))
  IH = transport (λ - → n-approx' n (map q (div2 (b ∶∶ -)))
                                    (map half (b ∶∶ -)))
         head-tail-eta
         (half-div2-approx b (head α) (tail α) n)

half-div2-approx −1' −2' α 0 = ((u ⊕ v) , (u ⊕ (u ⊕ v))) , (⊕-idem ⁻¹)
half-div2-approx −1' −2' α 1 = ((u ⊕ v) , (u ⊕ v))
                             , (ap (u ⊕_) ⊕-idem ∙ ⊕-idem ⁻¹)
half-div2-approx −1' −2' α (succ (succ n))
 = pr₁ IH , (ap (λ - → (u ⊕ ((u ⊕ v) ⊕ -))) (pr₂ IH) ∙ γ)
 where
  IH : n-approx' n (map q (div2 α)) (map half α)
  IH = transport (λ - → n-approx' n (map q (div2 -))
                                    (map half -))
         (ap (head α ∶∶_) (head-tail-eta {_} {_} {tail α})
                         ∙ head-tail-eta {_} {_} {α})
         (half-div2-approx (head α) (head (tail α)) (tail (tail α)) n)
  γ : {x : 𝕀} → (u ⊕ ((u ⊕ v) ⊕ x)) ≡ ((u ⊕ (u ⊕ v)) ⊕ (u ⊕ x))
  γ {x} = ap (_⊕ ((u ⊕ v) ⊕ x)) (⊕-idem ⁻¹)
        ∙ ⊕-tran

half-div2-approx −1' −1' α 0 = ((u ⊕ v) , (u ⊕ (u ⊕ v)))
                             , (⊕-idem ⁻¹)
half-div2-approx −1' −1' α (succ n)
 = pr₁ IH , (ap (u ⊕_) (pr₂ IH) ∙ γ)
 where
  IH : n-approx' n (map q (div2 (+1' ∶∶ α))) (map half (+1' ∶∶ α))
  IH = transport (λ - → n-approx' n (map q (div2 (+1' ∶∶ -)))
                                    (map half (+1' ∶∶ -)))
         (head-tail-eta {_} {_} {α})
         (half-div2-approx +1' (head α) (tail α) n)
  γ : {x : 𝕀} → (u ⊕ ((v ⊕ (u ⊕ v)) ⊕ x)) ≡ ((u ⊕ (u ⊕ v)) ⊕ ((u ⊕ (u ⊕ v)) ⊕ x))
  γ {x} = ⊕-hom-l
        ∙ ap (_⊕ (u ⊕ x)) ⊕-hom-l
        ∙ ⊕-tran
        ∙ ap (_⊕ ((u ⊕ (u ⊕ v)) ⊕ x)) ⊕-comm

half-div2-approx −1'  O' α 0 = (u , (u ⊕ (u ⊕ v)))
                             , (⊕-comm ∙ ⊕-idem ⁻¹)
half-div2-approx −1'  O' α 1 = (u , u)
                             , (ap ((u ⊕ v) ⊕_) ⊕-idem
                             ∙ (ap (_⊕ ((u ⊕ v) ⊕ u)) ⊕-comm ∙ ⊕-idem) ⁻¹)
half-div2-approx −1'  O' α (succ (succ n))
 = pr₁ IH , (ap (λ - → (u ⊕ v) ⊕ (u ⊕ -)) (pr₂ IH) ∙ γ)
 where
  IH : n-approx' n (map q (div2 α)) (map half α)
  IH = transport (λ - → n-approx' n (map q (div2 -))
                                    (map half -))
         (ap (head α ∶∶_) (head-tail-eta {_} {_} {tail α})
                        ∙ head-tail-eta {_} {_} {α}) 
         (half-div2-approx (head α) (head (tail α)) (tail (tail α)) n)
  γ : {x : 𝕀} → (u ⊕ v) ⊕ (u ⊕ x) ≡ ((u ⊕ (u ⊕ v)) ⊕ ((u ⊕ v) ⊕ x))
  γ {x} = ⊕-hom-l ∙ ap (_⊕ ((u ⊕ v) ⊕ x)) ⊕-comm

half-div2-approx −1' +1' α 0 = (u , (u ⊕ (u ⊕ v)))
                             , (⊕-comm ∙ ⊕-idem ⁻¹)
half-div2-approx −1' +1' α (succ n)
 = pr₁ IH , (ap (λ - → (u ⊕ v) ⊕ -) (pr₂ IH) ∙ γ)
 where
   IH : n-approx' n (map q (div2 (−1' ∶∶ α))) (map half (−1' ∶∶ α))
   IH = transport (λ - → n-approx' n (map q (div2 (−1' ∶∶ -)))
                                     (map half (−1' ∶∶ -)))
          (head-tail-eta {_} {_} {α})
          (half-div2-approx −1' (head α) (tail α) n)
   γ : {x : 𝕀} → (u ⊕ v) ⊕ ((u ⊕ (u ⊕ v)) ⊕ x) ≡ ((u ⊕ (u ⊕ v)) ⊕ ((v ⊕ (u ⊕ v)) ⊕ x))
   γ {x} = ap ((u ⊕ v) ⊕_) ⊕-comm
         ∙ ⊕-tran
         ∙ ap ((u ⊕ x) ⊕_)
             (ap (_⊕ (u ⊕ (u ⊕ v))) (⊕-idem ⁻¹)
             ∙ ⊕-tran
             ∙ ap (_⊕ (v ⊕ (u ⊕ v))) ⊕-comm)
         ∙ ⊕-tran
         ∙ ap ((u ⊕ (u ⊕ v)) ⊕_) ⊕-comm

half-div2-approx −1' +2' α 0 = (u , (u ⊕ (u ⊕ v)))
                             , (⊕-comm ∙ ⊕-idem ⁻¹)
half-div2-approx −1' +2' α 1 = (u , u)
                             , (⊕-comm ∙ ap (((u ⊕ v) ⊕ u) ⊕_) ⊕-comm
                                       ∙ ap (_⊕ (v ⊕ u)) ⊕-comm)
half-div2-approx −1' +2' α (succ (succ n))
 = pr₁ IH , (ap (λ - → (u ⊕ v) ⊕ ((u ⊕ v) ⊕ -)) (pr₂ IH) ∙ ⊕-tran)
 where
  IH : n-approx' n (map q (div2 α)) (map half α)
  IH = transport (λ - → n-approx' n (map q (div2 -))
                                    (map half -))
         (ap (head α ∶∶_) (head-tail-eta {_} {_} {tail α})
                         ∙ head-tail-eta {_} {_} {α})
         (half-div2-approx (head α) (head (tail α)) (tail (tail α)) n)

half-div2-approx +1' −2' α 0 = (((u ⊕ v) ⊕ u) , (u ⊕ u))
                             , (ap (_⊕ ((u ⊕ v) ⊕ u)) ⊕-comm
                             ∙ ⊕-tran)
half-div2-approx +1' −2' α 1 = (v , v)
                             , (⊕-comm
                             ∙ ap (_⊕ (u ⊕ v)) ⊕-comm)
half-div2-approx +1' −2' α (succ (succ n))
 = pr₁ IH , (ap (λ - → (u ⊕ v) ⊕ ((u ⊕ v) ⊕ -)) (pr₂ IH) ∙ γ)
 where
   IH : n-approx' n (map q (div2 α)) (map half α)
   IH = transport (λ - → n-approx' n (map q (div2 -))
                                     (map half -))
          (ap (head α  ∶∶_) (head-tail-eta {_} {_} {tail α})
                          ∙ head-tail-eta {_} {_} {α})
          (half-div2-approx (head α) (head (tail α)) (tail (tail α)) n)
   γ : {x : 𝕀} → (u ⊕ v) ⊕ ((u ⊕ v) ⊕ x) ≡ (v ⊕ (u ⊕ v)) ⊕ (u ⊕ x)
   γ {x} = ap (_⊕ ((u ⊕ v) ⊕ x)) ⊕-comm ∙ ⊕-tran
   
half-div2-approx +1' −1' α 0 = (((u ⊕ v) ⊕ u) , (u ⊕ u))
                             , (ap (_⊕ ((u ⊕ v) ⊕ u)) ⊕-comm
                             ∙ ⊕-tran)
half-div2-approx +1' −1' α (succ n)
 = pr₁ IH , (ap ((u ⊕ v) ⊕_) (pr₂ IH) ∙ γ)
 where
  IH : n-approx' n (map q (div2 (+1' ∶∶ α))) (map half (+1' ∶∶ α))
  IH = transport (λ - → n-approx' n (map q (div2 (+1' ∶∶ -)))
                                     (map half (+1' ∶∶ -)))
          (head-tail-eta {_} {_} {α})
          (half-div2-approx +1' (head α) (tail α) n)
  γ : {x : 𝕀} → (u ⊕ v) ⊕ ((v ⊕ (u ⊕ v)) ⊕ x) ≡ ((v ⊕ (u ⊕ v)) ⊕ ((u ⊕ (u ⊕ v)) ⊕ x))
  γ {x} = ⊕-hom-l
        ∙ ap (λ - → ((- ⊕ (v ⊕ (u ⊕ v))) ⊕ ((u ⊕ v) ⊕ x))) ⊕-comm
        ∙ ap (_⊕ ((u ⊕ v) ⊕ x)) ⊕-tran
        ∙ ap (λ - → ((- ⊕ (u ⊕ (u ⊕ v))) ⊕ ((u ⊕ v) ⊕ x))) ⊕-idem 
        ∙ ⊕-tran

half-div2-approx +1' O' α 0 = (v , (v ⊕ (u ⊕ v)))
                            , (⊕-comm ∙ ⊕-idem ⁻¹)
half-div2-approx +1' O' α 1 = (v , v)
                            , (ap ((u ⊕ v) ⊕_) ⊕-idem
                            ∙ ⊕-idem ⁻¹
                            ∙ ap (_⊕ ((u ⊕ v) ⊕ v)) ⊕-comm)
half-div2-approx +1' O' α (succ (succ n))
 = pr₁ IH
 , (ap (λ - → (u ⊕ v) ⊕ (v ⊕ -)) (pr₂ IH) ∙ γ)
 where
  IH : n-approx' n (map q (div2 α)) (map half α)
  IH = transport (λ - → n-approx' n (map q (div2 -))
                                    (map half -))
         (ap (head α  ∶∶_) (head-tail-eta {_} {_} {tail α})
                          ∙ head-tail-eta {_} {_} {α})
         (half-div2-approx (head α) (head (tail α)) (tail (tail α)) n)
  γ : {x : 𝕀} → ((u ⊕ v) ⊕ (v ⊕ x)) ≡ ((v ⊕ (u ⊕ v)) ⊕ ((u ⊕ v) ⊕ x))
  γ {x} = ap (_⊕ (v ⊕ x)) (⊕-idem ⁻¹)
        ∙ ⊕-tran
        ∙ ap (_⊕ ((u ⊕ v) ⊕ x)) ⊕-comm

half-div2-approx +1' +1' α 0 = ((u ⊕ v) , (v ⊕ (u ⊕ v)))
                             , (⊕-idem ⁻¹)
half-div2-approx +1' +1' α (succ n)
 = pr₁ IH , (ap (v ⊕_) (pr₂ IH) ∙ γ)
 where
  IH : n-approx' n (map q (div2 (−1' ∶∶ α))) (map half (−1' ∶∶ α))
  IH = transport (λ - → n-approx' n (map q (div2 (−1' ∶∶ -)))
                                    (map half (−1' ∶∶ -)))
         (head-tail-eta {_} {_} {α})
         (half-div2-approx −1' (head α) (tail α) n)
  γ : {x : 𝕀} → v ⊕ ((u ⊕ (u ⊕ v)) ⊕ x) ≡ ((v ⊕ (u ⊕ v)) ⊕ ((v ⊕ (u ⊕ v)) ⊕ x))
  γ {x} = ap (_⊕ ((u ⊕ (u ⊕ v)) ⊕ x)) (⊕-idem ⁻¹)
        ∙ ⊕-tran
        ∙ ap (_⊕ (v ⊕ x)) (⊕-hom-l ∙ ap (_⊕ (v ⊕ (u ⊕ v))) ⊕-comm)
        ∙ ⊕-tran
        ∙ ap (_⊕ ((v ⊕ (u ⊕ v)) ⊕ x)) ⊕-comm

half-div2-approx +1' +2' α 0 = ((u ⊕ v) , (v ⊕ (u ⊕ v)))
                             , (⊕-idem ⁻¹)
half-div2-approx +1' +2' α 1 = ((u ⊕ v) , (u ⊕ v))
                             , (ap (v ⊕_) ⊕-idem ∙ ⊕-idem ⁻¹)
half-div2-approx +1' +2' α (succ (succ n))
 = pr₁ IH , (ap (λ - → v ⊕ ((u ⊕ v) ⊕ -)) (pr₂ IH) ∙ γ)
 where
  IH : n-approx' n (map q (div2 α)) (map half α)
  IH = transport (λ - → n-approx' n (map q (div2 -))
                                    (map half -))
         (ap (head α  ∶∶_) (head-tail-eta {_} {_} {tail α})
                          ∙ head-tail-eta {_} {_} {α})
         (half-div2-approx (head α) (head (tail α)) (tail (tail α)) n)
  γ : {x : 𝕀} → v ⊕ ((u ⊕ v) ⊕ x) ≡ ((v ⊕ (u ⊕ v)) ⊕ (v ⊕ x))
  γ {x} = ⊕-hom-l
  
mid-realisability' : approximation → mid realises² _⊕_
mid-realisability' a α β = γ (add2 α β) ∙ half-real α β
 where
  γ : (α : 𝟝ᴺ) → 𝕢 (div2 α) ≡ M (map half α)
  γ α = a (map q (div2 α)) (map half α) δ
   where
    δ : (n : ℕ) → Σ (z , w) ꞉ 𝕀 × 𝕀
      , m n (append-one z n ((first- n) (map q (div2 α))))
      ≡ m n (append-one w n ((first- n) (map half α)))
    δ 0 = (u , u) , refl
    δ (succ n)
     = transport (λ - → n-approx' n (map q (div2 -))
                                    (map half -))
         (ap (head α ∶∶_) (head-tail-eta {_} {_} {tail α})
                         ∙ head-tail-eta {_} {_} {α})
         (half-div2-approx (head α) (head (tail α)) (tail (tail α)) n)


multi-canc : (w z : 𝕀) (y : ℕ → 𝕀) (n : ℕ)
           → m n (append-one w n ((first- n) y))
           ≡ m n (append-one z n ((first- n) y))
           → w ≡ z
multi-canc w .w y zero refl = refl
multi-canc w z y (succ n) e = multi-canc w z (y ∘ succ) n
                              (⊕-canc _ _ _ (⊕-comm ∙ e ∙ ⊕-comm))

one-sided-approx : (x : 𝕀) (y : ℕ → 𝕀)
                 → ((n : ℕ) → Σ w ꞉ 𝕀 , x ≡ m n (append-one w n ((first- n) y)))
                 → x ≡ M y
one-sided-approx x y f = M-prop₂ ws y γ where
  ws : ℕ → 𝕀
  ws 0 = x
  ws (succ i) = pr₁ (f (succ i))
  γ : (i : ℕ) → ws i ≡ (y i ⊕ ws (succ i))
  γ zero = pr₂ (f 1)
  γ (succ i) = multi-canc (ws (succ i)) (y (succ i) ⊕ ws (succ (succ i)))
               y (succ i) (pr₂ (f (succ i)) ⁻¹  ∙ (pr₂ (f (succ (succ i))) ∙ δ'' y (ws (succ (succ i))) i))
   where
    δ'' : (y : ℕ → 𝕀) (z : 𝕀) (i : ℕ)
        → m (succ (succ i)) (append-one z (succ (succ i)) ((first- (succ (succ i))) y))
        ≡ m (succ i) (append-one (y (succ i) ⊕ z) (succ i) ((first- (succ i)) y))
    δ'' y z zero = refl
    δ'' y z (succ i) = ap (y 0 ⊕_) (δ'' (y ∘ succ) z i)

_++_ : {n i : ℕ} {X : 𝓤 ̇ } → Vec X n → Vec X i → Vec X (n +ℕ i)
_++_ {zero} {zero} {X} [] v₂ = v₂
_++_ {zero} {succ i} {X} [] v₂ = transport (Vec X) (ap succ (zero-left-neutral i ⁻¹)) v₂
_++_ {succ n} {zero} {X} v₁ [] = v₁
_++_ {succ n} {succ i} {X} (v ∷ v₁) v₂ = transport (Vec X) (ap succ (δ n i)) (v ∷ (v₁ ++ v₂))
 where
  δ : ∀ n i → succ (n +ℕ i) ≡ succ n +ℕ i
  δ n zero = refl
  δ n (succ i) = ap succ (δ n i)

_++'_ : {n : ℕ} {X : 𝓤 ̇ } → Vec X n → (ℕ → X) → (ℕ → X)
[] ++' y = y
((x ∷ _) ++' _) zero = x
((_ ∷ v₁) ++' y) (succ n) = (v₁ ++' y) n

five : (n : ℕ) (a b c : ℕ → 𝕀) (e : 𝕀)
     → m (succ n) (append-one e (succ n) ((first- succ n) a))
       ⊕ M ((first- n) b ++' λ i → (c (succ (i +ℕ n))))
     ≡ M ((append-one (a n ⊕ e) n ((first- n) λ i → a i ⊕ b i))
         ++' (λ i → c (succ (i +ℕ n))))
five zero a b c e = M-prop₁ _ ⁻¹
five (succ n) a b c e = ap ((a 0 ⊕ (a 1 ⊕
                             m n (append-one e n ((first- n) (λ n₁ → a (succ (succ n₁)))))))
                           ⊕_)
                          (M-prop₁ ((first- succ n) b ++' (λ i → c (succ (i +ℕ succ n)))))
                      ∙ ⊕-tran
                      ∙ ap ((a 0 ⊕ b 0) ⊕_) (five n (tail a) (tail b) (tail c) e)
                      ∙ M-prop₁ (append-one (a (succ n) ⊕ e) (succ n)
                                  ((first- succ n) (λ i → a i ⊕ b i))
                                  ++' (λ i → c (succ (i +ℕ succ n)))) ⁻¹

equals : (x : ℕ → 𝕀) (n : ℕ) → M x ≡ M (append-one (x n) n ((first- n) x) ++' (λ i → x (succ (i +ℕ n))))
equals x zero = M-prop₁ x
              ∙ M-prop₁ (append-one (x zero) zero ((first- zero) x) ++'
                          (λ i → x (succ (i +ℕ zero)))) ⁻¹
equals x (succ n) = M-prop₁ x
                  ∙ ap (x 0 ⊕_) (equals (tail x) n)
                  ∙ M-prop₁ (append-one (x (succ n)) (succ n) ((first- succ n) x) ++'
                              (λ i → x (succ (i +ℕ succ n)))) ⁻¹

next : (x y : ℕ → 𝕀) (n : ℕ)
     → M (λ i → x i ⊕ y i) ≡ m (succ n) (append-one (y n) (succ n) ((first- succ n) x))
                           ⊕ M (((first- n) y) ++' (λ i → (x (succ (i +ℕ n))) ⊕ (y (succ (i +ℕ n)))))
next x y n = equals (λ i → x i ⊕ y i) n
           ∙ five n x y (λ i → x i ⊕ y i) (y n) ⁻¹

equals2 : (x y : ℕ → 𝕀) (w : 𝕀) (n : ℕ)
        → (append-one w n ((first- n) x)) ++' y
        ≡ ((first- n) x) ++' (w ∶∶ y)
equals2 x y w zero = dfunext (fe 𝓤₀ 𝓤) (induction refl λ _ _ → refl)
equals2 x y w (succ n) = dfunext (fe 𝓤₀ 𝓤) (induction refl (λ k _ → happly (equals2 (tail x) y w n) k))

tail-_ : {X : 𝓤 ̇ } → ℕ → (ℕ → X) → (ℕ → X)
(tail- 0) α = α
(tail- succ n) α = tail ((tail- n) α)

M→m : (α : ℕ → 𝕀) (n : ℕ)
    → M α ≡ m n (append-one (M ((tail- n) α)) n ((first- n) α))
M→m α zero = refl
M→m α (succ n) = M-prop₁ α
               ∙ ap (α 0 ⊕_)
               (transport
                    (λ - → M (tail α)
                         ≡ m n (append-one (M -) n ((first- n) (tail α))))
                    (γ α n) (M→m (tail α) n))
  where
    γ : (α : ℕ → 𝕀) (n : ℕ) → ((tail- n) (tail α)) ≡ ((tail- succ n) α)
    γ α 0 = refl
    γ α (succ n) = ap tail (γ α n)

tl : {X : 𝓤 ̇} {m : ℕ} → Vec X (succ m) → Vec X m
tl (_ ∷ xs) = xs

tail-first' : {X : 𝓤 ̇ } {m : ℕ} → (a : Vec X (succ m)) (β : ℕ → X) (n : ℕ) → (tail- succ n) (a ++' β) ≡ (tail- n) (tl a ++' β)
tail-first' {X} {m} (_ ∷ xs) β 0 = refl
tail-first' {X} {m} (_ ∷ xs) β (succ n) = ap tail (tail-first' {X} {m} (_ ∷ xs) β n)

tail-first : {X : 𝓤 ̇ } → (α β : ℕ → X) (n : ℕ) → (tail- n) (((first- n) α) ++' β) ≡ β
tail-first α β zero = refl
tail-first α β (succ n) = tail-first' ((first- (succ n)) α) β n ∙ tail-first (tail α) β n

first-first : {X : 𝓤 ̇ } → (α β : ℕ → X) (n : ℕ) → ((first- n) ((first- n) α ++' β)) ≡ (first- n) α
first-first α β 0 = refl
first-first α β (succ n) = ap (α 0 ∷_) (first-first (tail α) β n)

approx-holds : approximation
approx-holds x y f = ⊕-canc (M x) (M y) (M (tail z)) seven
 where
  z w : ℕ → 𝕀
  z n = pr₁ (pr₁ (f n))
  w n = pr₂ (pr₁ (f n))
  w'' : (n : ℕ) → (ℕ → 𝕀)
  w'' n =  ((y n ⊕ pr₂ (pr₁ (f (succ n)))) ∶∶
               (λ i → x (succ (i +ℕ n)) ⊕ pr₁ (pr₁ (f (succ (succ (i +ℕ n)))))))
  six : (n : ℕ) → m n (append-one (z n) n ((first- n) x))
                ≡ m n (append-one (w n) n ((first- n) y))
  six n = pr₂ (f n)
  γ' : (n : ℕ) → Σ w* ꞉ 𝕀 , M (λ i → x i ⊕ (tail z) i)
                           ≡ m n (append-one w* n ((first- n) (λ i → y i ⊕ (tail z) i)))
  γ' n = M (w'' n)
       , (next x (tail z) n
       ∙ ap (_⊕ M ((first- n) (tail z) ++' (λ i → x (succ (i +ℕ n)) ⊕ tail z (succ (i +ℕ n)))))
           (six (succ n))
       ∙ five n y (tail z) (λ i → x i ⊕ (tail z) i) (w (succ n))
       ∙ ap M (equals2 (λ i → y i ⊕ (tail z) i) ((λ i → x (succ (i +ℕ n)) ⊕ (tail z) (succ (i +ℕ n)))) (w'' n 0) n)
       ∙ M→m (((first- n) (λ i → y i ⊕ (tail z) i) ++' (w'' n))) n
       ∙ (ap (λ - →
                  m n (append-one (M -) n
                  ((first- n) ((first- n) (λ i → y i ⊕ (tail z) i) ++' (w'' n)))))
                 (tail-first (λ i → y i ⊕ (tail z) i) (w'' n) n)
            ∙ ap (λ - →
                  m n (append-one (M (w'' n)) n -))
                  (first-first (λ i → y i ⊕ (tail z) i) (w'' n) n)))
  seven : M x ⊕ M (z ∘ succ) ≡ M y ⊕ M (z ∘ succ)
  seven = M-hom x (z ∘ succ)
        ∙ one-sided-approx (M (λ i → x i ⊕ pr₁ (pr₁ (f (succ i))))) (λ i → y i ⊕ z (succ i)) γ'
        ∙ M-hom y (z ∘ succ) ⁻¹

mid-realisability : mid realises² _⊕_
mid-realisability = mid-realisability' approx-holds
