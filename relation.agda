{-# OPTIONS --type-in-type #-}

module relation where

Rel : Set → Set → Set
Rel A B = A → B → Set
