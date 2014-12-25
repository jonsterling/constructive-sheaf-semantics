{-# OPTIONS --type-in-type #-}

module category where

open import kit.setoid
open import kit.sigma
open import kit.equivalence

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
    ; _∘_ = λ f g → g ∘ f
    ; id-l = id-r
    ; id-r = id-l
    ; assoc = λ f g h → symmetry (eq-equiv (hom _ _)) (assoc h g f)
    }

    where
      open is-equivalence-relation

