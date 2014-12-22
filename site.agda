module site where

open import category
open import basis

record Site : Set where
  constructor site⟨_,_⟩
  field
    category : CategoryWithPullbacks
    basis : Basis category

  open Basis basis
  open CategoryWithPullbacks category

