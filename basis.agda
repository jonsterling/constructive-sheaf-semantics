{-# OPTIONS --type-in-type #-}

module basis where

open import category
open import setoid
open import sigma
open import unit
open import function

record Basis (ℂ : Category) (pullback : Category.has-pullbacks ℂ) : Set where
  module ℂ = Category ℂ

  open ℂ
  open Setoid
  
  field
    _covered-by_ : (d : ob) (w : Δ d) → Set

    law-1 :
      {c d : ob}
      (f : ∣ hom c d ∣)
      (g : ∣ hom d c ∣)
        → hom c c ∋ g ℂ.∘ f ∼ id c
        → hom d d ∋ f ℂ.∘ g ∼ id d
        → d covered-by
            ⟨ f ∶ c [ i ]⇒ d ⟩[ i ∶ Unit ]

    law-2 :
      {c d : ob}
      (f : Δ d)
      (g : ∣ hom c d ∣)
      (let module f = Δ f
           module f×g i = Pullback (pullback (f.at i) g))
        → d covered-by f
        → c covered-by
             ⟨ f×g.proj₂ i
               ∶ f×g.pullback i [ i ]⇒ c
             ⟩[ i ∶ f.index ]

    law-3 :
      {d : ob}
      (f : Δ d)
      (let module f = Δ f)
      (g : (i : f.index) → Δ (f.dom i))
      (let module g i = Δ (g i))
        → d covered-by f
        → ((i : _) → f.dom i covered-by g i)
        → d covered-by
             ⟨ (let ⟨ i , j ⟩ = ij in f.at i ℂ.∘ g.at i j)
               ∶ _ [ ij ]⇒ d
             ⟩[ ij ∶ Σ f.index g.index ]
