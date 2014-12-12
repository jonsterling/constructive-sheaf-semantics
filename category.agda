{-# OPTIONS --type-in-type #-}

module category where

open import setoid
open import sigma

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

  Co : ob → Set
  Co d = Σ[ c ∶ ob ] ∣ hom c d ∣

  Δ : ob → Set
  Δ d = Σ[ I ∶ Set ] (I → Co d)

  record Pullback {a b c : ob} (f : ∣ hom a c ∣) (g : ∣ hom b c ∣) : Set where
    field
      prod : ob
      π₁ : ∣ hom prod a ∣
      π₂ : ∣ hom prod b ∣
      comm : eq (hom prod {!!}) (g ∘ π₂) (f ∘ π₁)
      pull :
        {q : ob}
        (h₁ : ∣ hom q a ∣)
        (h₂ : ∣ hom q b ∣)
          → Σ![ u ∶ hom q prod ]
                  eq (hom q b) (π₂ ∘ u) h₂
               × eq (hom q a) (π₁ ∘ u) h₁
