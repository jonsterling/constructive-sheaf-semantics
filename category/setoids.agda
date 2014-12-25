{-# OPTIONS --type-in-type #-}

module category.setoids where

open import setoid
open import category
open import equivalence

SET : Category
SET =
  let
    open _⇒_
    open is-equivalence-relation
  in
    record
      { ob = Setoid
      ; hom = _[⇒]_
      ; id = λ X → record { op = λ z → z ; ext = λ z → z }
      ; _∘_ = _[∘]_
      ; id-l = λ f x y → ext f
      ; id-r = λ f x y → ext f
      ; assoc = λ f g h x y x∼y → ext f (ext g (ext h x∼y))
      }
