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
        → d covered-by
            ⟨ f ∶ c [ i ]⇒ d ⟩[ i ∶ Unit ]

    law-2 :
      {c d : ℂ.ob}
      (f : ℂ.Δ d)
      (g : ∣ ℂ.hom c d ∣)
      (let module f = ℂ.Δ f
           module f×g i = ℂ.Pullback (pullback (f.morphism i) g))
        → d covered-by f
        → c covered-by
             ⟨ f×g.proj₂ i
               ∶ f×g.pullback i [ i ]⇒ c
             ⟩[ i ∶ f.index ]

    law-3 :
      {d : ℂ.ob}
      (f : ℂ.Δ d)
      (let module f = ℂ.Δ f)
      (g : (i : f.index) → ℂ.Δ (f.dom i))
      (let module g i = ℂ.Δ (g i))
        → d covered-by f
        → ((i : _) → f.dom i covered-by g i)
        → d covered-by
             ⟨ (let ⟨ i , j ⟩ = ij in f.morphism i ℂ.∘ g.morphism i j)
               ∶ _ [ ij ]⇒ d
             ⟩[ ij ∶ Σ f.index g.index ]
