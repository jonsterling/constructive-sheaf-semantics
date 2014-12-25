{-# OPTIONS --type-in-type #-}

module category.setoids where

open import kit.setoid
open import category

SET : Category
SET = record
  { ob = Setoid
  ; hom = _[⇒]_
  ; id = λ X → record { op = λ z → z ; ext = λ z → z }
  ; _∘_ = _[∘]_
  ; id-l = λ f x y → ext f
  ; id-r = λ f x y → ext f
  ; assoc = λ f g h x y x∼y → ext f (ext g (ext h x∼y))
  }

  where
    open _⇒_
