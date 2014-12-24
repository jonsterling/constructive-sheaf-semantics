{-# OPTIONS --type-in-type #-}

module presheaf where

open import category
open import setoids
open import functor
open import equivalence

Presheaf : (ℂ : Category) → Set
Presheaf ℂ =
  let
    open Category ℂ
  in
    Functor op SET
