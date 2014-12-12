{-# OPTIONS --type-in-type #-}

module presheaf where

open import category
open import setoid
open import equivalence

record Presheaf (ℂ : Category) : Set where
  module ℂ = Category ℂ
  open Setoid
  
  field
    _∙_ : (a : ℂ.ob) → Setoid
    _[∙]_ : {a b : ℂ.ob} (f : ∣ ℂ.hom a b ∣) → ∣ _∙_ b ∣ → ∣ _∙_ a ∣
    resp : {a b : ℂ.ob} (f g : ∣ ℂ.hom a b ∣) {u v : ∣ _∙_ b ∣} → eq (_∙_ b) u v  → eq (_∙_ a) (f [∙] u) (f [∙] v)

    map-id : {a : ℂ.ob} {u : ∣ _∙_ a ∣} → eq (_∙_ a) (ℂ.id a [∙] u) u
    map-comp : {a b c : ℂ.ob} (f : ∣ ℂ.hom b c ∣) (g : ∣ ℂ.hom a b ∣) {u : ∣ _∙_ c ∣} → eq (_∙_ a) ((f ℂ.∘ g) [∙] u) (g [∙] (f [∙] u))
    
