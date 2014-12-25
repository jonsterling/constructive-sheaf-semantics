{-# OPTIONS --type-in-type #-}

module setoid where

open import equivalence
open import relation

record Setoid : Set where
  field
    car : Set
    eq : Rel car car

    eq-equiv : is-equivalence-relation eq

  ∣_∣ = car
  _∋_∼_ = eq

record _⇒_ (S T : Setoid) : Set where
  open Setoid
  
  field
    op : ∣ S ∣ → ∣ T ∣
    ext : {M N : ∣ S ∣} → S ∋ M ∼ N → T ∋ op M ∼ op N

  infixl 11 _∙_
  _∙_ = op

_[⇒]_ : (S T : Setoid) → Setoid
S [⇒] T =
  let open Setoid ; open _⇒_ ; open is-equivalence-relation
      module S = Setoid S ; module T = Setoid T
  in record
    { car = S ⇒ T
    ; eq = λ f g → (x y : ∣ S ∣) (p : S ∋ x ∼ y) → T ∋ (f ∙ x) ∼ (g ∙ y)
    ; eq-equiv = record
        { reflexivity = λ {X} x y → ext X
        ; symmetry = λ p x y x∼y → symmetry T.eq-equiv (p y x (symmetry S.eq-equiv x∼y))
        ; transitivity = λ {f} {g} g∼h f∼g x y x∼y → transitivity T.eq-equiv (g∼h y y (reflexivity S.eq-equiv)) (f∼g x y x∼y)
        }
    }

_[∘]_ : {A B C : Setoid} → (B ⇒ C) → (A ⇒ B) → (A ⇒ C)
f [∘] g =
  let open _⇒_
  in record
    { op = λ x → f ∙ (g ∙ x)
    ; ext = λ p → ext f (ext g p)
    }
