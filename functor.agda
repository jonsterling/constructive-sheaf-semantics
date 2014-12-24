{-# OPTIONS --type-in-type #-}

module functor where

open import category
open import setoid

record Functor (ℂ₁ ℂ₂ : Category) : Set where
  private
    module ℂ₁ = Category ℂ₁
    module ℂ₂ = Category ℂ₂
    open Setoid

  field
    app₀ : (a : ℂ₁.ob) → ℂ₂.ob
    app₁ : {a b : ℂ₁.ob} (f : ∣ ℂ₁.hom a b ∣) → ∣ ℂ₂.hom (app₀ a) (app₀ b) ∣

    map-id : {a : ℂ₁.ob} → ℂ₂.hom (app₀ a) (app₀ a) ∋ ℂ₂.id (app₀ a) ∼ app₁ (ℂ₁.id a)
    map-comp : {a b c : ℂ₁.ob} (f : ∣ ℂ₁.hom b c ∣) (g : ∣ ℂ₁.hom a b ∣) → ℂ₂.hom (app₀ a) (app₀ c) ∋ app₁ f ℂ₂.∘ app₁ g ∼ app₁ (f ℂ₁.∘ g)

  _$_ = app₀
  infixl 100 _$_

