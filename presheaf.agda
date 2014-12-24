{-# OPTIONS --type-in-type #-}

module presheaf where

open import category
open import setoids
open import functor
open import equivalence
open import unit

Presheaf : (ℂ : Category) → Set
Presheaf ℂ =
  let
    open Category ℂ
  in
    Functor op SET

⟨1⟩ : (ℂ : Category) → Presheaf ℂ
⟨1⟩ _ =
  record
    { app₀ = λ _ → [1]
    ; app₁ = λ {a} {b} f → record
        { op = λ _ → ⟨⟩
        ; ext = λ M N _ → ⟨⟩
        }
    ; map-id = λ {a} x y p → ⟨⟩
    ; map-comp = λ {a} {b} {c} f g x y p → ⟨⟩
    }
