module equivalence where

open import relation

record is-equivalence-relation {A : Set} (_∼_ : Rel A A) : Set where
  field
    reflexivity : {X : A} → X ∼ X
    symmetry : {X Y : A} → X ∼ Y → Y ∼ X
    transitivity : {X Y Z : A} → Y ∼ Z → X ∼ Y → X ∼ Z
