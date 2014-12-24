{-# OPTIONS --type-in-type #-}

module setoids where

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
      ; id = λ X → record { op = λ z → z ; ext = λ M N z → z }
      ; _∘_ = _[∘]_
      ; id-l = ext
      ; id-r = ext
      ; assoc = λ f g h x y x∼y → ext f _ _ (ext g _ _ (ext h _ _ x∼y))
      }
