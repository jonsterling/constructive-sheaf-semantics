{-# OPTIONS --type-in-type #-}

open import category

module category.morphism-families (ℂ : Category) where

open import kit.setoid
open Category ℂ

open Setoid

record Co (cod : ob) : Set where
  field
    dom : ob
    morphism : ∣ hom dom cod ∣

record Δ (d : ob) : Set where
  constructor Δ⟨_,_⟩
  field
    index : Set
    fam : index → Co d

  module fam i = Co (fam i)
  open fam public

  at = fam.morphism

mk-fam :
  (I : Set)
  (c[_] : I → ob)
  (d : ob)
  (f[_] : (i : I) → ∣ hom c[ i ] d ∣)
    → Δ d
mk-fam I c[_] d f[_] = record { index = I ; fam = λ i → record { dom = c[ i ] ; morphism = f[ i ] } }

syntax mk-fam I (λ j → c) d (λ i → f) = ⟨ f ∶ c [ j ]⇒ d ⟩[ i ∶ I ]
