{-# OPTIONS --type-in-type #-}

module presheaf where

open import category
open import setoids
open import functor
open import equivalence
open import unit
open import setoid
open import sigma

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
        ; ext = λ _ → ⟨⟩
        }
    ; map-id = λ {a} x y p → ⟨⟩
    ; map-comp = λ {a} {b} {c} f g x y p → ⟨⟩
    }

_⟨×⟩_ : {ℂ : Category} (F G : Presheaf ℂ) → Presheaf ℂ
F ⟨×⟩ G = record
  { app₀ = λ a → F $ a [×] G $ a
  ; app₁ = λ f → record { op = λ { ⟨ x , y ⟩ → ⟨ F.app₁ f ∙ x , G.app₁ f ∙ y ⟩ }; ext = λ { ⟨ p , q ⟩ → ⟨ ext (F.app₁ f) p , ext (G.app₁ f) q ⟩ } }
  ; map-id = λ { ⟨ x₁ , x₂ ⟩ ⟨ y₁ , y₂ ⟩ ⟨ p , q ⟩ → ⟨ F.map-id x₁ y₁ p , G.map-id x₂ y₂ q ⟩ }
  ; map-comp = λ { f g ⟨ x₁ , x₂ ⟩ ⟨ y₁ , y₂ ⟩ ⟨ p , q ⟩ → ⟨ (F.map-comp f g x₁ y₁ p) , (G.map-comp f g x₂ y₂ q) ⟩ }
  }

  where
    module F = Functor F
    module G = Functor G
    open Functor ; open Setoid ; open _⇒_
