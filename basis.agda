{-# OPTIONS --type-in-type #-}

module basis where

open import category
open import setoid
open import sigma
open import unit
open import function

-- A basis for a Grothendieck topology: a Grothendieck pretopology.
-- <http://ncatlab.org/nlab/show/Grothendieck+pretopology>

record Basis (ℂ : CategoryWithPullbacks) : Set where
  module ℂ = CategoryWithPullbacks ℂ
  private instance category = ℂ.category

  open ℂ
  open Setoid
  
  field
    _covered-by_ : (d : ob) (w : Δ d) → Set

    isomorphisms-cover :
      {c d : ob}
      (f : ∣ hom c d ∣)
      (g : ∣ hom d c ∣)
        → hom c c ∋ g ℂ.∘ f ∼ id c
        → hom d d ∋ f ℂ.∘ g ∼ id d
        → d covered-by
            ⟨ f ∶ c [ i ]⇒ d ⟩[ i ∶ Unit ]

    stability :
      {c d : ob}
      (f : Δ d)
      (g : ∣ hom c d ∣)
      (let module f = Δ f
           module f–×g i = Pullback (pullbacks (f.at i) g))
        → d covered-by f
        → c covered-by
             ⟨ f–×g.proj₂ i
               ∶ f–×g.pullback i [ i ]⇒ c
             ⟩[ i ∶ f.index ]

    transitivity :
      {d : ob}
      (f : Δ d)
      (let module f = Δ f)
      (g : (i : f.index) → Δ (f.dom i))
      (let module g i = Δ (g i))
        → d covered-by f
        → ((i : f.index) → f.dom i covered-by g i)
        → d covered-by
             ⟨ (let ⟨ i , j ⟩ = ij in f.at i ℂ.∘ g.at i j)
               ∶ _ [ ij ]⇒ d
             ⟩[ ij ∶ Σ f.index g.index ]
