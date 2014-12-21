module function where

_∘_ :
  {a b c : _}
  {A : Set a}
  {B : A → Set b}
  {C : {x : A} → B x → Set c}
  (f : ∀ {x} (y : B x) → C y)
  (g : (x : A) → B x)
    → ((x : A) → C (g x))
f ∘ g = λ x → f (g x)

κ :
  {a : _}
  {b : _}
  {A : Set a}
  {B : Set b}
  → A
  → B
  → A
κ x y = x
