{-# OPTIONS --type-in-type #-}

module presheaf where

open import category
open import setoid
open import equivalence

record Presheaf (ℂ : Category) : Set where
  module ℂ = Category ℂ
  open Setoid
  
  field
    app₀ : (a : ℂ.ob) → Setoid
    app₁ : {a b : ℂ.ob} (f : ∣ ℂ.hom a b ∣) → ∣ app₀ b ∣ → ∣ app₀ a ∣
    resp : {a b : ℂ.ob} (f g : ∣ ℂ.hom a b ∣) {u v : ∣ app₀ b ∣} → app₀ b ∋ u ∼ v  → app₀ a ∋ (app₁ f u) ∼ (app₁ f v)

    map-id : {a : ℂ.ob} {u : ∣ app₀ a ∣} → app₀ a ∋ (app₁ (ℂ.id a) u) ∼ u
    map-comp : {a b c : ℂ.ob} (f : ∣ ℂ.hom b c ∣) (g : ∣ ℂ.hom a b ∣) {u : ∣ app₀ c ∣} → app₀ a ∋ (app₁ (f ℂ.∘ g) u) ∼ (app₁ g (app₁ f u))
    
  _$_ = app₀
  _⟨$⟩_ = app₁
