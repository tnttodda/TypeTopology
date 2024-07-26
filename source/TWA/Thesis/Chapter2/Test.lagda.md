```agda
{-# OPTIONS --without-K --exact-split --safe #-}

open import MLTT.Spartan
open import UF.Subsingletons
open import UF.Equiv
open import UF.FunExt
open import UF.Subsingletons-FunExt

module TWA.Thesis.Chapter2.Test where

has-h-level* : (X : 𝓤 ̇ ) → ℕ → 𝓤  ̇
has-h-level* {𝓤} X 0 = is-singleton X
has-h-level* X (succ n) = (x y : X) → has-h-level* (x ＝ y) n

prop-𝟙 : (x y : 𝟙 {𝓤}) → is-singleton (x ＝ y)
prop-𝟙 ⋆ ⋆ = refl , γ
 where
  γ : _
  γ refl = refl

prop-singleton : {X : 𝓤 ̇ } → is-singleton X → (x y : X) → is-singleton (x ＝ y)
prop-singleton (c , f) x y
 = pointed-props-are-singletons (f x ⁻¹ ∙ f y) (props-are-sets (singletons-are-props (c , f)))

has-h-level*-monotone
 : {X : 𝓤 ̇ } (n : ℕ) → K-axiom 𝓤 → has-h-level* X n → has-h-level* X (succ n)
has-h-level*-monotone 0 K = prop-singleton
has-h-level*-monotone (succ n) K f x y = has-h-level*-monotone n K (f x y)

conv-𝟚 : 𝟚 → 𝓥 ̇ 
conv-𝟚 ₀ = 𝟘
conv-𝟚 ₁ = 𝟙

conv-𝟚-prop : (a : 𝟚) → is-prop {𝓥} (conv-𝟚 a) 
conv-𝟚-prop ₀ = 𝟘-is-prop
conv-𝟚-prop ₁ = 𝟙-is-prop

conv-𝟚-decidable : (a : 𝟚) → is-decidable {𝓥} (conv-𝟚 a)
conv-𝟚-decidable ₀ = inr (λ ())
conv-𝟚-decidable ₁ = inl ⋆

𝟚-conv : ((x , _) : Ω 𝓥) → is-decidable x → 𝟚
𝟚-conv _ (inl _) = ₁
𝟚-conv _ (inr _) = ₀

is-prop-is-prop : (X : 𝓤 ̇ ) → is-set X → is-prop (is-prop X)
is-prop-is-prop X e p q = dfunext {!!} (λ x → dfunext {!!} (λ y → e (p x y) (q x y)))

pe : propext 𝓥
pe = {!!}

to-Σ-＝ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {σ τ : Σ A}
       → (Σ p ꞉ pr₁ σ ＝ pr₁ τ , transport A p (pr₂ σ) ＝ pr₂ τ)
       → σ ＝ τ
to-Σ-＝ (refl , refl ) = refl

𝟘-resize : 𝟘 {𝓤} → 𝟘 {𝓥}
𝟘-resize ()

pred-equiv : {X : 𝓤 ̇ }
           → (Σ p ꞉ (X → Ω 𝓥) , ((x : X) → pr₁ (p x) + ¬ pr₁ (p x)))
           ≃ (X → 𝟚)
pr₁ pred-equiv (p , d) x = 𝟚-conv (p x) (d x)
pr₁ (pr₁ (pr₂ pred-equiv)) p
 = (λ x → (conv-𝟚 (p x)) , conv-𝟚-prop (p x)) , conv-𝟚-decidable ∘ p
pr₂ (pr₁ (pr₂ pred-equiv)) p = dfunext {!!} γ
 where
  γ : pr₁ pred-equiv (pr₁ (pr₁ (pr₂ pred-equiv)) p) ∼ p
  γ x with p x
  ... | ₀ = refl
  ... | ₁ = refl 
pr₁ (pr₂ (pr₂ pred-equiv)) p
 = (λ x → (conv-𝟚 (p x)) , conv-𝟚-prop (p x)) , conv-𝟚-decidable ∘ p
pr₂ (pr₂ (pr₂ pred-equiv)) (p , d) 
 = to-subtype-＝
     (λ p → Π-is-prop {!!}
       (λ x → +-is-prop (pr₂ (p x))
         (Π-is-prop {!!} (λ _ → 𝟘-is-prop))
         λ z z₁ → z₁ z))
     (dfunext {!!} γ)
 where
  γ : _
  γ x with d x
  ... | inl e = to-Σ-＝ ((pe 𝟙-is-prop (pr₂ (p x)) (λ _ → e) (λ _ → ⋆))
                  , is-prop-is-prop (pr₁ (p x)) (λ x' → props-are-sets (pr₂ (p x)) x') (transport (λ X₁ → (x₁ y : X₁) → x₁ ＝ y)
                                                       (pe 𝟙-is-prop (pr₂ (p x)) (λ _ → e) (λ _ → ⋆))
                                                       (conv-𝟚-prop (𝟚-conv (p x) (inl e)))) (pr₂ (p x)))
  ... | inr e = to-Σ-＝ (pe (λ ()) (pr₂ (p x)) (λ ()) (𝟘-resize ∘ e)
                  , is-prop-is-prop (pr₁ (p x)) (λ x' → props-are-sets ((transport (λ X₁ → (x₁ y : X₁) → x₁ ＝ y)
                                                                                  (pe (λ ()) (pr₂ (p x)) (λ ()) (λ x₁ → 𝟘-resize (e x₁)))
                                                                                  (conv-𝟚-prop (𝟚-conv (p x) (inr e))))) x') (transport (λ X₁ → (x₁ y : X₁) → x₁ ＝ y)
                                                                                  (pe (λ ()) (pr₂ (p x)) (λ ()) (λ x₁ → 𝟘-resize (e x₁)))
                                                                                  (conv-𝟚-prop (𝟚-conv (p x) (inr e)))) (pr₂ (p x)))
```
