module kit.sum where

data _+_ (A B : Set) : Set where
  inl : A → A + B
  inr : B → A + B
