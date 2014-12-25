{-# OPTIONS --type-in-type #-}

module forcing where

open import basis
open import category
open import functor
open import sheaf
open import site
open import unit
open import setoid
open import sigma
open import sum
open import presheaf
open import void
open import natural-transformation
open import list

module Forcing (S : Site) where
  private
    open Setoid
    module S = Site S
    ℂ = S.category ; module ℂ = Category ℂ
  
  data sort : Set where
    prop : sort
  
  module Language (atom : sort → Set) where
    data L_[_] : sort → sort * → Set where
      [_] : {τ* : _} {τ : sort} → atom τ → L τ [ τ* ]
      ⊤ ⊥ : {τ* : _} → L prop [ τ* ]
      _∧_ _∨_ _⊃_ : {τ* : _} → L prop [ τ* ] → L prop [ τ* ] → L prop [ τ* ]
      `∀[_] `∃[_] : {τ* : _} (τ : sort) → L prop [ τ ∷ τ* ] → L prop [ τ* ]

    ⟨□⟩ : {A : Set} {ℂ : Category} (⟦_⟧ : A → Presheaf ℂ) (τ* : A *) → Presheaf ℂ
    ⟨□⟩ ⟦_⟧ [] = ⟨1⟩ _
    ⟨□⟩ ⟦_⟧ (x ∷ xs) = ⟦ x ⟧ ⟨×⟩ ⟨□⟩ ⟦_⟧ xs

    record Interpretation : Set where
      field
        ⟦_⟧ : sort → Presheaf ℂ
        ⟦_⟧atom : {τ : sort} (c : atom τ) → NaturalTransformation (⟨1⟩ ℂ) ⟦ τ ⟧
        ⟦_⟧tm : {τ* : sort *} {τ : sort} → NaturalTransformation (⟨□⟩ ⟦_⟧ τ*) ⟦ τ ⟧

    module forcing (I : Interpretation) where
      open Interpretation I
      open Functor
      open _⇒_

      _⊩⟨_⟩_[_] : (c : ℂ.ob) (τ* : sort *) {τ : sort} (tm : L τ [ τ* ]) → ∣ □ (λ σ → ⟦ σ ⟧ $ c) τ* ∣ → Set
      c ⊩⟨ τ* ⟩ ⊤ [ e ] = Unit
      c ⊩⟨ τ* ⟩ ⊥ [ e ] = c S.◂ Category.Δ⟨ Void , abort ⟩
      c ⊩⟨ τ* ⟩ φ ∧ ψ [ e ] = (c ⊩⟨ τ* ⟩ φ [ e ]) × (c ⊩⟨ τ* ⟩ ψ [ e ])
      c ⊩⟨ τ* ⟩ φ ∨ ψ [ e ] =
        Σ[ f ∶ ℂ.Δ c ] (∀ i →
          let 
            module f = ℂ.Δ f
            e′ = □-map τ* (λ σ a → app₁ ⟦ σ ⟧ (f.at i) ∙ a) e
          in
            f.dom i ⊩⟨ τ* ⟩ φ [ e′ ] + f.dom i ⊩⟨ τ* ⟩ ψ [ e′ ])

      c ⊩⟨ τ* ⟩ φ ⊃ ψ [ e ] =
        {d : ℂ.ob}
        (f : ∣ ℂ.hom d c ∣)
        (let e′ = □-map τ* (λ σ a → app₁ ⟦ σ ⟧ f ∙ a) e)
          → d ⊩⟨ τ* ⟩ φ [ e′ ]
          → d ⊩⟨ τ* ⟩ ψ [ e′ ]

      c ⊩⟨ τ* ⟩ `∃[ τ ] φ [ e ] =
        Σ[ f ∶ ℂ.Δ c ]
         let
            module f = ℂ.Δ f
          in
            Σ[ γ ∶ (∀ i → ∣ ⟦ τ ⟧ $ f.dom i ∣) ] (∀ i →
              f.dom i ⊩⟨ τ ∷ τ* ⟩ φ [ ⟨ γ i , □-map τ* (λ σ a → app₁ ⟦ σ ⟧ (f.at i) ∙ a) e ⟩ ])

      c ⊩⟨ τ* ⟩ `∀[ τ ] φ [ e ] =
        {d : ℂ.ob}
        (f : ∣ ℂ.hom d c ∣)
        (γ : ∣ ⟦ τ ⟧ $ d ∣)
          → d ⊩⟨ (τ ∷ τ*) ⟩ φ [ ⟨ γ , □-map τ* (λ σ a → app₁ ⟦ σ ⟧ f ∙ a) e ⟩ ]
  
      c ⊩⟨ τ* ⟩ [ x ] [ e ] = {!!}
