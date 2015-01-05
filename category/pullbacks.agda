{-# OPTIONS --type-in-type #-}

module category.pullbacks where

open import category
open import kit.setoid
open import kit.sigma

module Pullbacks (ℂ : Category) where
  private
    module ℂ = Category ℂ
    open Setoid

  record is-pullback {a b c : ℂ.ob} (prod : ℂ.ob) (f : ∣ ℂ.hom a c ∣) (g : ∣ ℂ.hom b c ∣) : Set where
    field
      proj₁ : ∣ ℂ.hom prod a ∣
      proj₂ : ∣ ℂ.hom prod b ∣
      comm : ℂ.hom prod c ∋ (g ℂ.∘ proj₂) ∼ (f ℂ.∘ proj₁)
      pull :
        {q : ℂ.ob}
        (h₁ : ∣ ℂ.hom q a ∣)
        (h₂ : ∣ ℂ.hom q b ∣)
        (comm' : ℂ.hom q c ∋ (g ℂ.∘ h₂) ∼ (f ℂ.∘ h₁))
          → Σ![ u ∈ ℂ.hom q prod ]
                ℂ.hom q b ∋ (proj₂ ℂ.∘ u) ∼ h₂ × ℂ.hom q a ∋ (proj₁ ℂ.∘ u) ∼ h₁

  record Pullback {a b c : ℂ.ob} (f : ∣ ℂ.hom a c ∣) (g : ∣ ℂ.hom b c ∣) : Set where
    field
      pullback : ℂ.ob
      pullback-proof : is-pullback pullback f g
    open is-pullback pullback-proof public

  has-pullbacks : Set
  has-pullbacks =
    {a b c : ℂ.ob}
    (f : ∣ ℂ.hom a c ∣)
    (g : ∣ ℂ.hom b c ∣)
      → Pullback f g
      
