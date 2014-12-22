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
    ℂ = ℂ×.category
    module ℂ = Category ℂ
    open Setoid
  
  field
    presheaf : Presheaf ℂ
    descent :
      ([U] : S.Cov)
      (let F = presheaf
           module F = Presheaf F
           module [U] = S.Cov [U]
           U = [U].fam ; module U = ℂ.Δ U
           I = U.index ; open Presheaf)
       (s[_] : (i : I) → ∣ F $ U.dom i ∣)
       (_ :
         (i j : I)
         (let module Uᵢ×Uⱼ = ℂ.Pullback (ℂ×.pullbacks (U.at i) (U.at j)))
           → F.app₀ Uᵢ×Uⱼ.pullback ∋ F.app₁ Uᵢ×Uⱼ.proj₁ s[ i ] ∼ F.app₁ Uᵢ×Uⱼ.proj₂ s[ j ])
        → Σ![ s ∈ F $ [U].cod ]
              ((i : I) → (F $ U.dom i) ∋ s[ i ] ∼ F.app₁ (U.at i) s)
