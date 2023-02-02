-- Dead binding elimination, but in a single pass (equivalent to strongly live variable analysis)
-- Using co-de-Bruijn representation.
module StronglyDBECdB where

open import Data.Nat using (_+_)
open import Data.List using (List ; _∷_ ; [])
open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; cong₂ ; sym)
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import Lang hiding (Expr ; eval)
import Lang
open import LangCdB
open import OPE

let-? : ∀ {σ τ Γ₁ Γ₂ Γ Γ₂'} → Bind σ Γ₂ Γ₂' → Union Γ₁ Γ₂' Γ → Expr σ Γ₁ → Expr τ Γ₂ → Expr τ ⇑ Γ
let-? dead u e₁ e₂ = e₂ ↑ (ope-Union₂ u)
let-? live u e₁ e₂ = Let live u e₁ e₂ ↑ ope-id _

-- Also remove bindings that are tagged live in the input Expr,
-- but where the body is revealed to not use the top variable after the recursive call.
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
dbe Γ (Let {σ} b u e₁ e₂) =
  let e₁' ↑ ope₁  = dbe _ e₁
      e₂' ↑ ope₂  = dbe _ e₂
      b'  ↑ ope₂' = cover-Bind (ope-trans ope₂ (ope-Bind b))
      u'  ↑ ope   = cover-Union (ope-trans ope₁ (ope-Union₁ u)) (ope-trans ope₂' (ope-Union₂ u))
      e'  ↑ ope-? = let-? b' u' e₁' e₂'
  in e' ↑ (ope-trans ope-? ope)
dbe .[] (Val v) = Val v ↑ Empty
dbe Γ (Plus u e₁ e₂) =
  let e₁' ↑ ope₁ = dbe _ e₁
      e₂' ↑ ope₂ = dbe _ e₂
      u'  ↑ ope  = cover-Union (ope-trans ope₁ (ope-Union₁ u)) (ope-trans ope₂ (ope-Union₂ u))
  in Plus u' e₁' e₂' ↑ ope

-- IDEA: We could show that this is a fixpoint? dbe (dbe e) ≡ dbe e
-- TODO: prove semantics preserving!
