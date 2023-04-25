{-# OPTIONS --allow-unsolved-metas #-}  -- TODO

-- A simpler version of (strong?) Dead Binding Elimination without using annotations.
module Transformations.DeBruijn.DeadBindingDirect where

open import Data.Nat using (_+_; ℕ)
open import Data.List using (List ; _∷_ ; [])
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; cong₂ ; sym)
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import Data.OPE
open import Language.Core
open Language.Core.Env {U} {⟦_⟧}
open Language.Core.Ref {U} {⟦_⟧}
open import Language.DeBruijn
open import Language.CoDeBruijn using (o-Ref; project-Env)  -- TODO: put somewhere else
open import Transformations.Recursion

private
  variable
    σ τ : U
    Γ : Ctx

-- Note that we cannot avoid renaming the subexpressions at each layer (quadratic complexity).
optimise : Expr σ Γ → Expr σ ⇑ Γ
optimise (Var x) =
  Var Top ↑ o-Ref x
optimise (App e₁ e₂) =
  let e₁' ↑ θ₁ = optimise e₁
      e₂' ↑ θ₂ = optimise e₂
  in App
       (rename-Expr (Δ₁⊑∪-domain θ₁ θ₂) e₁')
       (rename-Expr (Δ₂⊑∪-domain θ₁ θ₂) e₂') ↑ (θ₁ ∪ θ₂)
optimise (Lam e₁) =
  let e₁' ↑ θ = optimise e₁
  in Lam (rename-Expr (un-pop θ) e₁') ↑ pop θ
optimise (Let e₁ e₂) =  -- TODO: split on θ₂ ! This makes it strong, we can't do it non-strong?
  let e₁' ↑ θ₁ = optimise e₁
      e₂' ↑ θ₂ = optimise e₂
  in Let
       (rename-Expr (Δ₁⊑∪-domain θ₁ (pop θ₂)) e₁')
       (rename-Expr (un-pop θ₂ ₒ Δ₂⊑∪-domain θ₁ (pop θ₂) os) e₂') ↑ (θ₁ ∪ pop θ₂)
optimise (Val v) =
  (Val v) ↑ oe
optimise (Plus e₁ e₂) =
  let e₁' ↑ θ₁ = optimise e₁
      e₂' ↑ θ₂ = optimise e₂
  in Plus
       (rename-Expr (Δ₁⊑∪-domain θ₁ θ₂) e₁')
       (rename-Expr (Δ₂⊑∪-domain θ₁ θ₂) e₂') ↑ (θ₁ ∪ θ₂)

optimise-correct-Var :
  (x : Ref σ Γ) (env : Env Γ) →
  lookup Top (project-Env (o-Ref x) env) ≡ lookup x env
optimise-correct-Var Top env = {!!}
optimise-correct-Var (Pop x) (Cons v env) = optimise-correct-Var x env
  
optimise-correct :
  (e : Expr σ Γ) (env : Env Γ) →
  let e' ↑ θ = optimise e
  in eval e' (project-Env θ env) ≡ eval e env
optimise-correct (Var x) env =
  optimise-correct-Var x env
optimise-correct (App e₁ e₂) env =
  let e₁' ↑ θ₁ = optimise e₁
      e₂' ↑ θ₂ = optimise e₂
  in
    eval (rename-Expr (Δ₁⊑∪-domain θ₁ θ₂) e₁') (project-Env (θ₁ ∪ θ₂) env)
      (eval (rename-Expr (Δ₂⊑∪-domain θ₁ θ₂) e₂') (project-Env (θ₁ ∪ θ₂) env))
  ≡⟨ {!optimise-correct e₁ env!} ⟩
    eval e₁ env
      (eval (rename-Expr (Δ₂⊑∪-domain θ₁ θ₂) e₂') (project-Env (θ₁ ∪ θ₂) env))
  ≡⟨ cong (eval e₁ env) {!optimise-correct e₂ env!} ⟩
    eval e₁ env (eval e₂' (project-Env θ₂ env))
  ≡⟨ cong (eval e₁ env) (optimise-correct e₂ env) ⟩
    eval e₁ env (eval e₂ env)
  ∎
optimise-correct (Lam e₁) env = {!!}
optimise-correct (Let e₁ e₂) env = {!!}
optimise-correct (Val v) env = {!!}
optimise-correct (Plus e₁ e₂) env = {!!}
