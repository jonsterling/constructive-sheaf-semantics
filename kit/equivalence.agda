module kit.equivalence where

open import Agda.Primitive

record is-equivalence-relation {a} {A : Set a} (_∼_ : A → A → Set) : Set (lsuc a) where
  field
    reflexivity : {X : A} → X ∼ X
    symmetry : {X Y : A} → X ∼ Y → Y ∼ X
    transitivity : {X Y Z : A} → Y ∼ Z → X ∼ Y → X ∼ Z
