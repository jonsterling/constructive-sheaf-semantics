{-# OPTIONS --type-in-type #-}

module basis where

open import category
open import setoid
open import sigma
open import unit
open import function
open import pullbacks

open Pullbacks

-- A basis for a Grothendieck topology: a Grothendieck pretopology.
-- <http://ncatlab.org/nlab/show/Grothendieck+pretopology>

record Basis (ℂ : Category) (pullbacks : has-pullbacks ℂ) : Set where
  private
    module ℂ = Category ℂ
    open ℂ
    open Setoid

  field
    _◂_ : (d : ob) (w : Δ d) → Set

    isomorphisms-cover :
      {c d : ob}
      (f : ∣ hom c d ∣)
      (g : ∣ hom d c ∣)
        → hom c c ∋ g ℂ.∘ f ∼ id c
        → hom d d ∋ f ℂ.∘ g ∼ id d
        → d ◂ ⟨ f ∶ c [ i ]⇒ d ⟩[ i ∶ Unit ]

    stability :
      {c d : ob}
      (f : Δ d)
      (g : ∣ hom c d ∣)
      (let module f = Δ f
           module f–×g i = Pullbacks.Pullback _ (pullbacks (f.at i) g))
        → d ◂ f
        → c ◂ ⟨ f–×g.proj₂ i ∶ f–×g.pullback i [ i ]⇒ c ⟩[ i ∶ f.index ]

    transitivity :
      {d : ob}
      (f : Δ d)
      (let module f = Δ f)
      (g : (i : f.index) → Δ (f.dom i))
      (let module g i = Δ (g i))
        → d ◂ f
        → ((i : f.index) → f.dom i ◂ g i)
        → d ◂ ⟨ (let ⟨ i , j ⟩ = ij in f.at i ℂ.∘ g.at i j) ∶ _ [ ij ]⇒ d ⟩[ ij ∶ Σ f.index g.index ]
