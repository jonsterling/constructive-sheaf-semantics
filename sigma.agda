{-# OPTIONS --type-in-type #-}

module sigma where

open import setoid
open import equivalence

record Σ (A : Set) (B : A → Set) : Set where
  constructor ⟨_,_⟩
  field
    π₁ : A
    π₂ : B π₁

syntax Σ A (λ a → B) = Σ[ a ∶ A ] B

_×_ : (A B : Set) → Set
A × B = Σ[ x ∶ A ] B

_[×]_ : (S T : Setoid) → Setoid
S [×] T =
  let
    open Setoid ; open is-equivalence-relation
    module S = Setoid S ; module T = Setoid T
  in
    record
      { car = ∣ S ∣ × ∣ T ∣
      ; eq = λ { ⟨ a , b ⟩ ⟨ c , d ⟩ → (S ∋ a ∼ c) × (T ∋ b ∼ d) }
      ; eq-equiv = record { reflexivity = ⟨ reflexivity S.eq-equiv , reflexivity T.eq-equiv ⟩; symmetry = λ { ⟨ p , q ⟩ → ⟨ symmetry S.eq-equiv p , symmetry T.eq-equiv q ⟩ } ; transitivity = λ { ⟨ p , q ⟩ ⟨ r , s ⟩ → ⟨ transitivity S.eq-equiv p r , transitivity T.eq-equiv q s ⟩ } }
      }


infixr 9 _×_

record Σ! (A : Setoid ) (B : Setoid.car A → Set)  : Set where
  constructor _unique-by_
  open Setoid
  field
    witness : Σ[ a ∶ ∣ A ∣ ] B a
    unique : (a : ∣ A ∣) (p : B a) → A ∋ a ∼ Σ.π₁ witness

syntax Σ! A (λ a → B) = Σ![ a ∈ A ] B
