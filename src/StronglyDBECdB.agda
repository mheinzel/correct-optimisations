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
let-? dead u e₁ e₂ = e₂ ↑ (o-Union₂ u)
let-? live u e₁ e₂ = Let live u e₁ e₂ ↑ oi

-- Also remove bindings that are tagged live in the input Expr,
-- but where the body is revealed to not use the top variable after the recursive call.
dbe : Expr τ Γ → Expr τ ⇑ Γ
dbe Var =
  Var ↑ oz os
dbe (App u e₁ e₂) =
  let e₁' ↑ θ₁ = dbe e₁
      e₂' ↑ θ₂ = dbe e₂
      u'  ↑ θ  = cover-Union (θ₁ ₒ o-Union₁ u) (θ₂ ₒ o-Union₂ u)
  in App u' e₁' e₂' ↑ θ
dbe (Lam b e) =
  let e' ↑ θ' = dbe e
      b' ↑ θ  = cover-Bind (θ' ₒ o-Bind b)
  in Lam b' e' ↑ θ
dbe (Let {σ} b u e₁ e₂) =
  let e₁' ↑ θ₁  = dbe e₁
      e₂' ↑ θ₂  = dbe e₂
      b'  ↑ θ₂' = cover-Bind (θ₂ ₒ o-Bind b)
      u'  ↑ θ   = cover-Union (θ₁ ₒ o-Union₁ u) (θ₂' ₒ o-Union₂ u)  -- TODO: can this be simplified?
      e'  ↑ θ?  = let-? b' u' e₁' e₂'
  in e' ↑ (θ? ₒ θ)
dbe (Val v) = Val v ↑ oz
dbe (Plus u e₁ e₂) =
  let e₁' ↑ θ₁ = dbe e₁
      e₂' ↑ θ₂ = dbe e₂
      u'  ↑ θ  = cover-Union (θ₁ ₒ o-Union₁ u) (θ₂ ₒ o-Union₂ u)
  in Plus u' e₁' e₂' ↑ θ

-- IDEA: We could show that this is a fixpoint? dbe (dbe e) ≡ dbe e

-- TODO: prove semantics preserving!
dbe-correct :
  {Γₑ : Ctx} (e : Expr τ Γ) (env : Env Γₑ) (θ : Γ ⊑ Γₑ) →
  let e' ↑ θ' = dbe e
  in eval e' (θ' ₒ θ) env ≡ eval e θ env
dbe-correct Var env θ =
  cong (λ x → lookup Top (project-Env x env)) (law-oiₒ θ)
dbe-correct (App u e₁ e₂) env θ =
  let
      e₁' ↑ θ₁ = dbe e₁
      e₂' ↑ θ₂ = dbe e₂
      h₁ = dbe-correct e₁ env (o-Union₁ u ₒ θ)
      h₂ = dbe-correct e₂ env (o-Union₂ u ₒ θ)
      u' ↑ θ' = cover-Union (θ₁ ₒ o-Union₁ u) (θ₂ ₒ o-Union₂ u)
  in
    eval e₁' (o-Union₁ u' ₒ θ' ₒ θ) env
      (eval e₂' (o-Union₂ u' ₒ θ' ₒ θ) env)
  ≡⟨ {!!} ⟩  -- TODO: how cumbersome will this be?
    eval e₁' (θ₁ ₒ o-Union₁ u ₒ θ) env
      (eval e₂' (θ₂ ₒ o-Union₂ u ₒ θ) env)
  ≡⟨ cong₂ (λ f x → f x) h₁ h₂ ⟩
    eval e₁ (o-Union₁ u ₒ θ) env
      (eval e₂ (o-Union₂ u ₒ θ) env)
  ∎
{-
dbe-correct (Lam b e) env θ = {!!}
dbe-correct (Let b u e₁ e₂) env θ = {!!}
dbe-correct (Val v) env θ = {!!}
dbe-correct (Plus u e₁ e₂) env θ = {!!}
-}
