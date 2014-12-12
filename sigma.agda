{-# OPTIONS --type-in-type #-}

module sigma where

open import setoid

record Σ (A : Set) (B : A → Set) : Set where
  constructor ⟨_,_⟩
  field
    π₁ : A
    π₂ : B π₁

syntax Σ A (λ a → B) = Σ[ a ∶ A ] B

_×_ : (A B : Set) → Set
A × B = Σ[ x ∶ A ] B

infixr 9 _×_

record Σ! (A : Setoid ) (B : Setoid.car A → Set)  : Set where
  constructor !⟨_,_,_⟩
  open Setoid
  field
    witness : Σ[ a ∶ ∣ A ∣ ] B a
    unique : (a : ∣ A ∣) (p : B a) → A ∋ a ∼ Σ.π₁ witness

syntax Σ! A (λ a → B) = Σ![ a ∈ A ] B
