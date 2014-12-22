{-# OPTIONS --type-in-type #-}

module basis where

open import category
open import setoid
open import sigma
open import unit
open import function

record Basis (ℂ : Category) (pullback : Category.has-pullbacks ℂ) : Set where
  module ℂ = Category ℂ
  open Setoid
  
  field
    _covered-by_ : (d : ℂ.ob) (w : ℂ.Δ d) → Set

    law-1 :
      {c d : ℂ.ob}
      (f : ∣ ℂ.hom c d ∣)
      (g : ∣ ℂ.hom d c ∣)
        → ℂ.hom c c ∋ g ℂ.∘ f ∼ ℂ.id c
        → ℂ.hom d d ∋ f ℂ.∘ g ∼ ℂ.id d
        → d covered-by ⟨ f ∶ c [ i ]⇒ d ⟩[ i ∶ Unit ]

    law-2 :
      {c d : ℂ.ob}
      (f : ℂ.Δ d)
      (g : ∣ ℂ.hom c d ∣)
      (let I = Σ.π₁ f
           f[_] = Σ.π₂ ∘ Σ.π₂ f)
        → d covered-by f
        → c covered-by
             ⟨ (let open ℂ.is-pullback (Σ.π₂ (pullback f[ i ] g)) in proj₂) ∶ _ [ i ]⇒ c ⟩[ i ∶ I ]

    law-3 :
      {d : ℂ.ob}
      (f : ℂ.Δ d)
      (let ⟨ I , f′ ⟩ = f
           f[_] = Σ.π₂ ∘ f′
           c[_] = Σ.π₁ ∘ f′)
      (g[_] : (i : I) → ℂ.Δ c[ i ])
      (let J = Σ.π₁ ∘ g[_]
           g = λ ij → let ⟨ i , j ⟩ = ij in Σ.π₂ (Σ.π₂ g[ Σ.π₁ ij ] (Σ.π₂ ij)))
        → d covered-by f
        → ((i : I) → c[ i ] covered-by g[ i ])
        → d covered-by
             ⟨ (let ⟨ i , _ ⟩ = ij in f[ i ] ℂ.∘ g ij) ∶ _ [ ij ]⇒ d ⟩[ ij ∶ Σ I J ]
