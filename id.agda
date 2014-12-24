module id where

open import equivalence

data _==_ {a} {A : Set a} (M : A) : A → Set a where
  refl : M == M

{-# BUILTIN EQUALITY _==_ #-}
{-# BUILTIN REFL refl #-}

module _ {a} {A : Set a} where
  ==-symmetry : {M N : A} → M == N → N == M
  ==-symmetry refl = refl

  ==-transitivity : {M N O : A} → N == O → M == N → M == O
  ==-transitivity refl refl = refl

id-equiv : {A : Set} → is-equivalence-relation (_==_ {A = A})
id-equiv = record
  { reflexivity = λ {X} → refl
  ; symmetry = ==-symmetry
  ; transitivity = ==-transitivity
  }

