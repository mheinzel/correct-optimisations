-- Dead binding elimination,
-- Using co-de-Bruijn representation.
module DBECdB where

open import Data.Nat using (_+_)
open import Data.List using (List ; _∷_ ; [])
open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; cong₂ ; sym)
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import Lang hiding (Expr ; eval)
import Lang
open import LangCdB
open import OPE

-- Only remove directly dead bindings.
dbe : (Γ : Ctx) → Expr τ Γ → Expr τ ⇑ Γ
dbe {τ} .(τ ∷ []) Var =
  Var ↑ Keep τ Empty
dbe Γ (App u e₁ e₂) =
  let e₁' ↑ ope₁ = dbe _ e₁
      e₂' ↑ ope₂ = dbe _ e₂
      u'  ↑ ope  = cover-Union (ope-trans ope₁ (ope-Union₁ u)) (ope-trans ope₂ (ope-Union₂ u))
  in App u' e₁' e₂' ↑ ope
dbe Γ (Lam {σ} b e) =
  let e' ↑ ope' = dbe _ e
      b' ↑ ope  = cover-Bind (ope-trans ope' (ope-Bind b))
  in Lam b' e' ↑ ope
dbe Γ (Let dead u e₁ e₂) =   -- NOTE: We check liveness given based on the the variable usage in the input Expr.
  let e₂' ↑ ope₂ = dbe _ e₂  -- But dbe e₂ might reveal the variable to be dead even if previously marked live!
  in e₂' ↑ ope-trans ope₂ (ope-Union₂ u)
dbe Γ (Let {σ} live u e₁ e₂) =
  let e₁' ↑ ope₁  = dbe _ e₁
      e₂' ↑ ope₂  = dbe _ e₂
      b'  ↑ ope₂' = cover-Bind (ope-trans ope₂ (ope-Bind live))
      u'  ↑ ope   = cover-Union (ope-trans ope₁ (ope-Union₁ u)) (ope-trans ope₂' (ope-Union₂ u))
  in (Let b' u' e₁' e₂') ↑ ope
dbe .[] (Val v) = Val v ↑ Empty
dbe Γ (Plus u e₁ e₂) =
  let e₁' ↑ ope₁ = dbe _ e₁
      e₂' ↑ ope₂ = dbe _ e₂
      u'  ↑ ope  = cover-Union (ope-trans ope₁ (ope-Union₁ u)) (ope-trans ope₂ (ope-Union₂ u))
  in Plus u' e₁' e₂' ↑ ope

-- TODO: iterate!
-- TODO: prove semantics-preserving
