{-# OPTIONS --type-in-type #-}

module sheaf where

open import category
open import category.pullbacks
open import functor
open import presheaf
open import kit.setoid
open import kit.sigma
open import site

record Sheaf (S : Site) : Set where
  private
    module S = Site S
    ℂ = S.category ; module ℂ = Category ℂ
    open Setoid
    open _⇒_

  open Functor public

  field
    presheaf : Presheaf ℂ
    descent :
      (U : S.Cov)
      (let F = presheaf
           module F = Functor F
           module U = S.Cov U ; module [U] = ℂ.Δ U.fam ; ∪U = U.cod
           module U–×U– i j = Pullbacks.Pullback _ (S.pullback ([U].at i) ([U].at j)))
       (s[_] : ∀ i → ∣ F $ [U].dom i ∣)
         → (∀ i j →
               let
                 Ui×Uj = U–×U–.pullback i j
                 proj₁* = F.app₁ (U–×U–.proj₁ i j)
                 proj₂* = F.app₁ (U–×U–.proj₂ i j)
               in
                 F $ Ui×Uj ∋ proj₁* ∙ s[ i ] ∼ (proj₂* ∙ s[ j ]))
          → Σ![ s ∈ F $ ∪U ] (∀ i → F $ [U].dom i ∋ s[ i ] ∼ ((F.app₁ ([U].at i)) ∙ s))
