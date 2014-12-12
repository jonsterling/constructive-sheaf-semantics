{-# OPTIONS --type-in-type #-}

module category where

open import setoid
open import sigma

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

  Co : ob → Set
  Co d = Σ[ c ∶ ob ] ∣ hom c d ∣

  Δ : ob → Set
  Δ d = Σ[ I ∶ Set ] (I → Co d)

  record is-pullback {a b c : ob} (prod : ob) (f : ∣ hom a c ∣) (g : ∣ hom b c ∣) : Set where
    field
      proj₁ : ∣ hom prod a ∣
      proj₂ : ∣ hom prod b ∣
      comm : hom prod c ∋ (g ∘ proj₂) ∼ (f ∘ proj₁)
      pull :
        {q : ob}
        (h₁ : ∣ hom q a ∣)
        (h₂ : ∣ hom q b ∣)
          → Σ![ u ∶ hom q prod ]
                  hom q b ∋ (proj₂ ∘ u) ∼ h₂
               × hom q a ∋ (proj₁ ∘ u) ∼ h₁

  has-pullbacks : Set
  has-pullbacks =
    {a b c : ob}
    (f : ∣ hom a c ∣)
    (g : ∣ hom b c ∣)
      → Σ[ p ∶ ob ] is-pullback p f g
