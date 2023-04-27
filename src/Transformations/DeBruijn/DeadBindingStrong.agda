-- Dead Binding Elimination using strongly live variable analysis
--
-- Based on DeadBinding.
module Transformations.DeBruijn.DeadBindingStrong where

open import Data.Nat using (_+_)
open import Data.List using (List ; _∷_ ; [])
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; cong₂ ; sym ; trans)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Function using (_$_)

open import Data.OPE
open import Postulates using (extensionality)

open import Language.Core
open Language.Core.Env {U} {⟦_⟧}
open Language.Core.Ref {U} {⟦_⟧}
open import Language.DeBruijn
open import Transformations.DeBruijn.StronglyLive

private
  variable
    σ τ : U
    Γ Γ' Δ : Ctx

transform : {θ : Δ ⊑ Γ} → LiveExpr σ θ → Δ ⊑ Γ' → Expr σ Γ'
transform (Var x) θ' = Var (ref-o θ')
transform (App {θ₁ = θ₁} {θ₂ = θ₂} e₁ e₂) θ' =
  App
    (transform e₁ (Δ₁⊑∪-domain θ₁ θ₂ ₒ θ'))
    (transform e₂ (Δ₂⊑∪-domain θ₁ θ₂ ₒ θ'))
transform (Lam {θ = θ} e₁) θ' =
  Lam (transform e₁ (un-pop θ ₒ θ' os))
transform (Let {θ₁ = θ₁} {θ₂ = θ₂ o'} e₁ e₂) θ' =
  transform e₂ θ'
transform (Let {θ₁ = θ₁} {θ₂ = θ₂ os} e₁ e₂) θ' =
  Let
    (transform e₁ (Δ₁⊑∪-domain θ₁ θ₂ ₒ θ'))
    (transform e₂ ((Δ₂⊑∪-domain θ₁ θ₂ ₒ θ') os))
transform (Val v) θ' =
  Val v
transform (Plus {θ₁ = θ₁} {θ₂ = θ₂} e₁ e₂) θ' =
  Plus
    (transform e₁ (Δ₁⊑∪-domain θ₁ θ₂ ₒ θ'))
    (transform e₂ (Δ₂⊑∪-domain θ₁ θ₂ ₒ θ'))

-- eval ∘ transform ≡ evalLive
transform-correct :
  {θ : Δ ⊑ Γ} (e : LiveExpr σ θ) (θ' : Δ ⊑ Γ') (env : Env Γ') →
  eval (transform e θ') env ≡ evalLive e env θ'
transform-correct (Var x) θ' env =
  refl
transform-correct (App {θ₁ = θ₁} {θ₂ = θ₂} e₁ e₂) θ' env =
  cong₂ _$_
    (transform-correct e₁ (Δ₁⊑∪-domain θ₁ θ₂ ₒ θ') env)
    (transform-correct e₂ (Δ₂⊑∪-domain θ₁ θ₂ ₒ θ') env)
transform-correct (Lam {θ = θ} e₁) θ' env =
  extensionality _ _ λ v →
    transform-correct e₁ (un-pop θ ₒ θ' os) (Cons v env)
transform-correct (Let {θ₁ = θ₁} {θ₂ = θ₂ o'} e₁ e₂) θ' env =
  transform-correct e₂ θ' env
transform-correct (Let {θ₁ = θ₁} {θ₂ = θ₂ os} e₁ e₂) θ' env =
  trans
    (transform-correct e₂ _ (Cons (eval (transform e₁ _) env) env))
    (cong (λ x → evalLive e₂ (Cons x env) _) (transform-correct e₁ _ env))
transform-correct (Val v) θ' env =
  refl
transform-correct (Plus {θ₁ = θ₁} {θ₂ = θ₂} e₁ e₂) θ' env =
  cong₂ _+_
    (transform-correct e₁ (Δ₁⊑∪-domain θ₁ θ₂ ₒ θ') env)
    (transform-correct e₂ (Δ₂⊑∪-domain θ₁ θ₂ ₒ θ') env)

dbe : Expr σ Γ → Expr σ ⇑ Γ
dbe e = let Δ , θ , le = analyse e in transform le oi ↑ θ

dbe-correct :
  (e : Expr σ Γ) (env : Env Γ) →
  let e' ↑ θ = dbe e
  in eval e' (project-Env θ env) ≡ eval e env
dbe-correct e env =
  let Δ , θ , le = analyse e
  in
    eval (transform le oi) (project-Env θ env)
  ≡⟨ transform-correct le oi (project-Env θ env) ⟩
    evalLive le (project-Env θ env) oi
  ≡⟨ evalLive-correct le env oi θ ⟩
    eval (forget le) env
  ≡⟨ cong (λ x → eval x env) (analyse-preserves e) ⟩
    eval e env
  ∎
