module kit.unit where

open import kit.setoid

record Unit : Set where
  constructor ⟨⟩

[1] : Setoid
[1] = record
  { car = Unit
  ; eq = λ _ _ → Unit
  ; eq-equiv = record
      { reflexivity = λ {X} → ⟨⟩
      ; symmetry = λ {X} {Y} _ → ⟨⟩
      ; transitivity = λ {X} {Y} {Z} _ _ → ⟨⟩
      }
  }

