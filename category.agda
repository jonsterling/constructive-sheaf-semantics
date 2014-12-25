{-# OPTIONS --type-in-type #-}

module category where

open import setoid
open import sigma
open import equivalence

record Category : Set where
  open Setoid

  infixr 9 _∘_
  
  field
    ob : Set
    hom : ob → ob → Setoid

    id : (X : ob) → ∣ hom X X ∣
    _∘_ : {X Y Z : ob}
      (f : ∣ hom Y Z ∣)
      (g : ∣ hom X Y ∣)
        → ∣ hom X Z ∣

    id-l : {X Y : ob}
      (f : ∣ hom X Y ∣)
        → hom X Y ∋ id Y ∘ f ∼ f
    id-r : {X Y : ob}
      (f : ∣ hom X Y ∣)
        → hom X Y ∋ f ∘ id X ∼ f
    assoc : {U V W X : ob}
      (f : ∣ hom W X ∣)
      (g : ∣ hom V W ∣)
      (h : ∣ hom U V ∣)
        → hom U X ∋ ((f ∘ g) ∘ h) ∼ (f ∘ g ∘ h)

  op : Category
  op = record
    { ob = ob
    ; hom = λ a b → hom b a
    ; id = id
    ; _∘_ = λ {X} {Y} {Z} f g → g ∘ f
    ; id-l = λ {X} {Y} → id-r
    ; id-r = λ {X} {Y} → id-l
    ; assoc = λ f g h → is-equivalence-relation.symmetry (eq-equiv (hom _ _)) (assoc h g f)
    }

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
  {{ℂ : Category}}
  (open Category ℂ)
  (open Setoid)
  (I : Set)
  (c[_] : I → ob)
  (d : ob)
  (f[_] : (i : I) → ∣ hom c[ i ] d ∣)
    → Δ d
mk-fam I c[_] d f[_] = record { index = I ; fam = λ i → record { dom = c[ i ] ; morphism = f[ i ] } }

syntax mk-fam I (λ j → c) d (λ i → f) = ⟨ f ∶ c [ j ]⇒ d ⟩[ i ∶ I ]
