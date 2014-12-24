{-# OPTIONS --type-in-type #-}

module list where

open import unit
open import sigma
open import setoid
open import setoids
open import category
open import functor
open import presheaf
open import id

data _* (A : Set) : Set where
  [] : A *
  _∷_ : A → A * → A *

infixr 9 _∷_
