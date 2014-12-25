module site where

open import category
open import basis

record Site : Set where
  constructor site⟨_,_⟩
  field
    category : CategoryWithPullbacks
    basis : Basis category

  open Basis basis public 
  open CategoryWithPullbacks category hiding (category) public

  record Cov : Set where
    field
      cod : ob
      fam : Δ cod
      covering : cod ◂ fam
