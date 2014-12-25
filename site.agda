module site where

open import category
open import basis
open import pullbacks

record Site : Set where
  constructor site⟨_,_⟩
  field
    category : Category
    pullback : Pullbacks.has-pullbacks category
    basis : Basis category pullback

  open Basis basis public 
  open Category category public
  open Pullbacks category public

  record Cov : Set where
    field
      cod : ob
      fam : Δ cod
      covering : cod ◂ fam
