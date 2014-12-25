{-# OPTIONS --type-in-type #-}

module kit.list where

open import kit.unit
open import kit.sigma
open import setoid
open import category
open import category.setoids
open import functor
open import presheaf
open import kit.id

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
