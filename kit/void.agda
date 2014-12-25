module kit.void where

data Void : Set where

abort : {A : Set} → (M : Void) → A
abort () 
