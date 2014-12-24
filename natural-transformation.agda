{-# OPTIONS --type-in-type #-}

module natural-transformation where

open import category
open import functor
open import setoid

record NaturalTransformation {ℂ₁ ℂ₂ : Category} (F₁ F₂ : Functor ℂ₁ ℂ₂) : Set where
  private
    module ℂ₁ = Category ℂ₁
    module ℂ₂ = Category ℂ₂
    module F₁ = Functor F₁
    module F₂ = Functor F₂
    open Setoid

  field
    trans : (a : ℂ₁.ob) → ∣ ℂ₂.hom (F₁.app₀ a) (F₂.app₀ a) ∣
    naturality : (a b : ℂ₁.ob) (f : ∣ ℂ₁.hom a b ∣) → ℂ₂.hom (F₁.app₀ a) (F₂.app₀ b) ∋ trans b ℂ₂.∘ F₁.app₁ f ∼ (F₂.app₁ f ℂ₂.∘ trans a)
  
    
