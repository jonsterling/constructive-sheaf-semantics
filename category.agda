{-# OPTIONS --type-in-type #-}

module category where

open import setoid

record Category : Set where
  open Setoid
  open setoid-notation {{...}}

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
      → Setoid.eq (hom X Y) (id Y ∘ f) f
    id-r : {X Y : ob}
      (f : ∣ hom X Y ∣)
      → Setoid.eq (hom X Y) (f ∘ id X) f
    assoc : {U V W X : ob}
      (f : ∣ hom W X ∣)
      (g : ∣ hom V W ∣)
      (h : ∣ hom U V ∣)
        → Setoid.eq (hom U X) ((f ∘ g) ∘ h) (f ∘ g ∘ h)
