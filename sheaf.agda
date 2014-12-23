{-# OPTIONS --type-in-type #-}

module sheaf where

open import category
open import presheaf
open import setoid
open import sigma
open import site

record Sheaf (S : Site) : Set where
  private
    module S = Site S
    module ℂ× = CategoryWithPullbacks S.category
    module ℂ = Category ℂ×.category
    open Setoid

  open Presheaf public

  field
    presheaf : Presheaf ℂ×.category
    descent :
      (U : S.Cov)
      (let F = presheaf
           module F = Presheaf F
           module U = S.Cov U ; module [U] = ℂ.Δ U.fam ; ∪U = U.cod
           module U–×U– i j = ℂ.Pullback (ℂ×.pullbacks ([U].at i) ([U].at j)))
       (s[_] : ∀ i → ∣ F $ [U].dom i ∣)
         → (∀ i j →
               let
                 Uᵢ×Uⱼ = U–×U–.pullback i j
                 proj₁* = F.app₁ (U–×U–.proj₁ i j)
                 proj₂* = F.app₁ (U–×U–.proj₂ i j)
               in
                 F $ Uᵢ×Uⱼ ∋ proj₁* s[ i ] ∼ proj₂* s[ j ])
          → Σ![ s ∈ F $ ∪U ] (∀ i → F $ [U].dom i ∋ s[ i ] ∼ F.app₁ ([U].at i) s)
