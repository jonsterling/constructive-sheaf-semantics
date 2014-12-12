{-# OPTIONS --type-in-type #-}

module basis where

open import category
open import setoid
open import sigma
open import unit

record Basis (ℂ : Category) (pullback : Category.has-pullbacks ℂ) : Set where
  module ℂ = Category ℂ
  open Setoid
  
  field
    _covered-by_ : (d : ℂ.ob) (w : ℂ.Δ d) → Set
    law-1 :
      {c d : ℂ.ob}
      (f : ∣ ℂ.hom c d ∣)
      (g : ∣ ℂ.hom d c ∣)
      (_ : ℂ.hom c c ∋ g ℂ.∘ f ∼ ℂ.id c)
      (_ : ℂ.hom d d ∋ f ℂ.∘ g ∼ ℂ.id d)
        → d covered-by ⟨ Unit , (λ _ → ⟨ c , f ⟩) ⟩

    law-2 :
      {c d : ℂ.ob}
      (f : ℂ.Δ d)
      (let I = Σ.π₁ f ; f[_] = λ i → Σ.π₂ (Σ.π₂ f i))
      (g : ∣ ℂ.hom c d ∣)
      (_ : d covered-by f)
        → c covered-by
            ⟨ I
            , (λ i →
                 let ⟨ p , pb ⟩ = pullback f[ i ] g
                     open ℂ.is-pullback
                 in ⟨ p , proj₂ pb ⟩)
            ⟩

    law-3 :
      {d : ℂ.ob}
      (f : ℂ.Δ d)
      (let I = Σ.π₁ f ; f[_] = λ i → Σ.π₂ (Σ.π₂ f i))
      (let c[_] = λ i → Σ.π₁ (Σ.π₂ f i))
      (_ : d covered-by f)
      (g[_] : (i : I) → ℂ.Δ c[ i ])
      (let J = λ i → Σ.π₁ g[ i ] ; g[_,_] = λ i j → Σ.π₂ (Σ.π₂ g[ i ] j))
      (_ : (i : I) → c[ i ] covered-by g[ i ])
        → d covered-by ⟨ Σ I J , (λ { ⟨ i , j ⟩ → ⟨ _ , f[ i ] ℂ.∘ g[ i , j ] ⟩}) ⟩
