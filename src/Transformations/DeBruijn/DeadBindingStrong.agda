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

dbe : {θ : Δ ⊑ Γ} → LiveExpr σ θ → Δ ⊑ Γ' → Expr σ Γ'
dbe (Var x) θ' = Var (ref-o θ')
dbe (App {θ₁ = θ₁} {θ₂ = θ₂} e₁ e₂) θ' =
  App
    (dbe e₁ (Δ₁⊑∪-domain θ₁ θ₂ ₒ θ'))
    (dbe e₂ (Δ₂⊑∪-domain θ₁ θ₂ ₒ θ'))
dbe (Lam {θ = θ} e₁) θ' =
  Lam (dbe e₁ (un-pop θ ₒ θ' os))
dbe (Let {θ₁ = θ₁} {θ₂ = θ₂ o'} e₁ e₂) θ' =
  dbe e₂ θ'
dbe (Let {θ₁ = θ₁} {θ₂ = θ₂ os} e₁ e₂) θ' =
  Let
    (dbe e₁ (Δ₁⊑∪-domain θ₁ θ₂ ₒ θ'))
    (dbe e₂ ((Δ₂⊑∪-domain θ₁ θ₂ ₒ θ') os))
dbe (Val v) θ' =
  Val v
dbe (Plus {θ₁ = θ₁} {θ₂ = θ₂} e₁ e₂) θ' =
  Plus
    (dbe e₁ (Δ₁⊑∪-domain θ₁ θ₂ ₒ θ'))
    (dbe e₂ (Δ₂⊑∪-domain θ₁ θ₂ ₒ θ'))

-- eval ∘ dbe ≡ evalLive
dbe-correct :
  {θ : Δ ⊑ Γ} (e : LiveExpr σ θ) (θ' : Δ ⊑ Γ') (env : Env Γ') →
  eval (dbe e θ') env ≡ evalLive e env θ'
dbe-correct (Var x) θ' env =
  refl
dbe-correct (App {θ₁ = θ₁} {θ₂ = θ₂} e₁ e₂) θ' env =
  cong₂ _$_
    (dbe-correct e₁ (Δ₁⊑∪-domain θ₁ θ₂ ₒ θ') env)
    (dbe-correct e₂ (Δ₂⊑∪-domain θ₁ θ₂ ₒ θ') env)
dbe-correct (Lam {θ = θ} e₁) θ' env =
  extensionality _ _ λ v →
    dbe-correct e₁ (un-pop θ ₒ θ' os) (Cons v env)
dbe-correct (Let {θ₁ = θ₁} {θ₂ = θ₂ o'} e₁ e₂) θ' env =
  dbe-correct e₂ θ' env
dbe-correct (Let {θ₁ = θ₁} {θ₂ = θ₂ os} e₁ e₂) θ' env =
  trans
    (dbe-correct e₂ _ (Cons (eval (dbe e₁ _) env) env))
    (cong (λ x → evalLive e₂ (Cons x env) _) (dbe-correct e₁ _ env))
dbe-correct (Val v) θ' env =
  refl
dbe-correct (Plus {θ₁ = θ₁} {θ₂ = θ₂} e₁ e₂) θ' env =
  cong₂ _+_
    (dbe-correct e₁ (Δ₁⊑∪-domain θ₁ θ₂ ₒ θ') env)
    (dbe-correct e₂ (Δ₂⊑∪-domain θ₁ θ₂ ₒ θ') env)

optimise : Expr σ Γ → Expr σ ⇑ Γ
optimise e = let Δ , θ , e' = analyse e in dbe e' oi ↑ θ

optimise-correct :
  (e : Expr σ Γ) (env : Env Γ) →
  let e' ↑ θ = optimise e
  in eval e' (project-Env θ env) ≡ eval e env
optimise-correct e env =
  let Δ , θ , le = analyse e
  in
    eval (dbe le oi) (project-Env θ env)
  ≡⟨ dbe-correct le oi (project-Env θ env) ⟩
    evalLive le (project-Env θ env) oi
  ≡⟨ evalLive-correct le env oi θ ⟩
    eval (forget le) env
  ≡⟨ cong (λ x → eval x env) (analyse-preserves e) ⟩
    eval e env
  ∎
