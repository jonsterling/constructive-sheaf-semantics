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

module _ {A : Set} where
  open Setoid
  
  □ : (el : A → Setoid) → A * → Setoid
  □ el [] = [1]
  □ el (x ∷ xs) = el x [×] □ el xs


  □-map : {B : A → Setoid} {el : A → Setoid} (xs : A *) (f : ∀ a → ∣ el a ∣ → ∣ B a ∣) → ∣ □ el xs ∣ → ∣ □ B xs ∣
  □-map [] f p = ⟨⟩
  □-map (x ∷ xs) f ⟨ p , qs ⟩ = ⟨ f _ p , □-map xs f qs ⟩
