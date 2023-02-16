-- Dead binding elimination,
-- Using co-de-Bruijn representation.
module CoDeBruijn.DeadBinding where

-- TODO: make compile
open import Data.Nat using (_+_)
open import Data.List using (List ; _∷_ ; [])
open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; cong₂ ; sym)
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import Core
open import CoDeBruijn.Lang
open import OPE

-- Only remove directly dead bindings.
dbe : (Γ : Ctx) → Expr τ Γ → Expr τ ⇑ Γ
dbe {τ} .(τ ∷ []) Var =
  Var ↑ oz os
dbe Γ (App u e₁ e₂) =
  let e₁' ↑ θ₁ = dbe _ e₁
      e₂' ↑ θ₂ = dbe _ e₂
      u'  ↑ θ  = cover-Union (θ₁ ₒ o-Union₁ u) (θ₂ ₒ o-Union₂ u)
  in App u' e₁' e₂' ↑ θ
dbe Γ (Lam {σ} b e) =
  let e' ↑ θ' = dbe _ e
      b' ↑ θ  = cover-Bind (θ' ₒ o-Bind b)
  in Lam b' e' ↑ θ
dbe Γ (Let dead u e₁ e₂) =   -- NOTE: We check liveness given based on the the variable usage in the input Expr.
  let e₂' ↑ θ₂ = dbe _ e₂  -- But dbe e₂ might reveal the variable to be dead even if previously marked live!
  in e₂' ↑ (θ₂ ₒ o-Union₂ u)
dbe Γ (Let {σ} live u e₁ e₂) =
  let e₁' ↑ θ₁  = dbe _ e₁
      e₂' ↑ θ₂  = dbe _ e₂
      b'  ↑ θ₂' = cover-Bind (θ₂ ₒ o-Bind live)
      u'  ↑ θ   = cover-Union (θ₁ ₒ o-Union₁ u) (θ₂' ₒ o-Union₂ u)
  in (Let b' u' e₁' e₂') ↑ θ
dbe .[] (Val v) = Val v ↑ oz
dbe Γ (Plus u e₁ e₂) =
  let e₁' ↑ θ₁ = dbe _ e₁
      e₂' ↑ θ₂ = dbe _ e₂
      u'  ↑ θ  = cover-Union (θ₁ ₒ o-Union₁ u) (θ₂ ₒ o-Union₂ u)
  in Plus u' e₁' e₂' ↑ θ

-- TODO: iterate!
-- TODO: prove semantics-preserving
