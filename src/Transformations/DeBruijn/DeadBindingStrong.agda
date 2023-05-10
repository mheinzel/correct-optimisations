{-# OPTIONS --allow-unsolved-metas #-}  -- TODO: finish proof

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

open import Data.Thinning
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

-- NOTE: we could also stay in the annotated setting, something like:
-- transform : {θ : Δ ⊑ Γ} → LiveExpr σ θ → (θ' : Δ ⊑ Γ') → LiveExpr σ θ'
-- But this requires us to show a lot of equalities about operations on Thinnings.
-- This could probably be avoided with something like
-- transform : {θ : Δ ⊑ Γ} → LiveExpr σ θ → Δ ⊑ Γ' → Σ[ θ' ∈ (Δ ⊑ Γ') ] LiveExpr σ θ'
-- but that doesn't seem super elegant.
-- However, we don't need this in the first place for our story.

transform : {θ : Δ ⊑ Γ} → LiveExpr σ θ → Δ ⊑ Γ' → Expr σ Γ'
transform (Var x) θ' = Var (ref-o θ')
transform (App {θ₁ = θ₁} {θ₂ = θ₂} e₁ e₂) θ' =
  App
    (transform e₁ (un-∪₁ θ₁ θ₂ ₒ θ'))
    (transform e₂ (un-∪₂ θ₁ θ₂ ₒ θ'))
transform (Lam {θ = θ} e₁) θ' =
  Lam (transform e₁ (un-pop θ ₒ os θ'))
transform (Let {θ₁ = θ₁} {θ₂ = o' θ₂} e₁ e₂) θ' =
  transform e₂ θ'
transform (Let {θ₁ = θ₁} {θ₂ = os θ₂} e₁ e₂) θ' =
  Let
    (transform e₁ (un-∪₁ θ₁ θ₂ ₒ θ'))
    (transform e₂ (os (un-∪₂ θ₁ θ₂ ₒ θ')))
transform (Val v) θ' =
  Val v
transform (Plus {θ₁ = θ₁} {θ₂ = θ₂} e₁ e₂) θ' =
  Plus
    (transform e₁ (un-∪₁ θ₁ θ₂ ₒ θ'))
    (transform e₂ (un-∪₂ θ₁ θ₂ ₒ θ'))

-- eval ∘ transform ≡ evalLive
transform-correct :
  {θ : Δ ⊑ Γ} (e : LiveExpr σ θ) (θ' : Δ ⊑ Γ') (env : Env Γ') →
  eval (transform e θ') env ≡ evalLive e env θ'
transform-correct (Var x) θ' env =
  refl
transform-correct (App {θ₁ = θ₁} {θ₂ = θ₂} e₁ e₂) θ' env =
  cong₂ _$_
    (transform-correct e₁ (un-∪₁ θ₁ θ₂ ₒ θ') env)
    (transform-correct e₂ (un-∪₂ θ₁ θ₂ ₒ θ') env)
transform-correct (Lam {θ = θ} e₁) θ' env =
  extensionality _ _ λ v →
    transform-correct e₁ (un-pop θ ₒ os θ') (Cons v env)
transform-correct (Let {θ₁ = θ₁} {θ₂ = o' θ₂} e₁ e₂) θ' env =
  transform-correct e₂ θ' env
transform-correct (Let {θ₁ = θ₁} {θ₂ = os θ₂} e₁ e₂) θ' env =
  trans
    (transform-correct e₂ _ (Cons (eval (transform e₁ _) env) env))
    (cong (λ x → evalLive e₂ (Cons x env) _) (transform-correct e₁ _ env))
transform-correct (Val v) θ' env =
  refl
transform-correct (Plus {θ₁ = θ₁} {θ₂ = θ₂} e₁ e₂) θ' env =
  cong₂ _+_
    (transform-correct e₁ (un-∪₁ θ₁ θ₂ ₒ θ') env)
    (transform-correct e₂ (un-∪₂ θ₁ θ₂ ₒ θ') env)

transform-correct' :
  {θ : Δ ⊑ Γ} (le : LiveExpr σ θ) (env : Env Γ) →
  eval (transform le θ) env ≡ eval (forget le) env
transform-correct' (Var x) env = {!!}
transform-correct' (App e₁ e₂) env =
  {!transform-correct' e₁ env!}
  --       eval (transform e₁ (un-∪₁ θ₁ θ₂ ₒ (θ₁ ∪ θ₂))) env
  -- ≡⟨ ? ⟩ eval (transform e₁ θ₁) env
  -- ≡⟨ h ⟩ eval (forget e₁) env
  --
  --       eval (transform e₁ (un-∪₁ θ₁ θ₂ ₒ oi)) (project-Env (θ₁ ∪ θ₂) env)
  -- ≡⟨ ? ⟩ eval (transform e₁ oi) (project-Env θ₁ env)
  -- ≡⟨ h ⟩ eval (forget e₁) env
transform-correct' (Lam {θ = θ} e₁) env =
  extensionality _ _ λ v →
    trans
      (cong (λ x → eval (transform e₁ x) (Cons v env)) (law-pop-inv θ))
      (transform-correct' e₁ (Cons v env))
transform-correct' (Let e₁ e₂) env = {!!}
transform-correct' (Val v) env = {!!}
transform-correct' (Plus e₁ e₂) env = {!!}
 
{-
-- Not even sure if true ...
law-rename-transform :
  {θ : Δ ⊑ Γ} (le : LiveExpr σ θ) →
  rename-Expr θ (transform le oi) ≡ transform le θ
law-rename-transform (Var x) = {!!}
law-rename-transform (App e₁ e₂) = {!!}
law-rename-transform (Lam {θ = o' θ} e₁) =
  cong Lam (
      rename-Expr (os θ) (transform e₁ (o' (oi ₒ oi)))
    ≡⟨ {!!} ⟩
      ? -- rename-Expr (o' θ) (transform e₁ oi)
    ≡⟨ {!!} ⟩
      ? -- rename-Expr (o' θ) (transform e₁ oi)
    ≡⟨ law-rename-transform e₁ ⟩
      transform e₁ (o' θ)
    ≡⟨ cong (λ x → transform e₁ (o' x)) (sym (law-oiₒ θ)) ⟩
      transform e₁ (o' (oi ₒ θ))
    ∎
  )
law-rename-transform (Lam {θ = θ} e₁) =
  cong Lam (
      rename-Expr (os (pop θ)) (transform e₁ (un-pop θ ₒ os oi))
    ≡⟨ {!!} ⟩
      rename-Expr θ (transform e₁ oi)
    ≡⟨ law-rename-transform e₁ ⟩
      transform e₁ θ
    ≡⟨ cong (transform e₁) (sym (law-pop-inv θ)) ⟩
      transform e₁ (un-pop θ ₒ os (pop θ))
    ∎
  )
law-rename-transform (Let e₁ e₂) = {!!}
law-rename-transform (Val v) = {!!}
law-rename-transform (Plus e₁ e₂) = {!!}
-}

law-eval-transform :
  {θ : Δ ⊑ Γ} (le : LiveExpr σ θ) (env : Env Γ) →
  -- eval (transform le oi) (project-Env θ env) ≡ eval (transform le θ) env
  eval (rename-Expr θ (transform le oi)) env ≡ eval (transform le θ) env
law-eval-transform (Var x) env = {!!}
law-eval-transform (App e e₁) env = {!!}
law-eval-transform (Lam {θ = θ} e₁) env =
  extensionality _ _ λ v →
      eval (rename-Expr (os (pop θ)) (transform e₁ (un-pop θ ₒ os oi))) (Cons v env)
    ≡⟨ {!!} ⟩
      eval (rename-Expr θ (transform e₁ oi)) (Cons v env)
    ≡⟨ law-eval-transform e₁ (Cons v env) ⟩
      eval (transform e₁ θ) (Cons v env)
    ≡⟨ {!!} ⟩
      eval (transform e₁ (un-pop θ ₒ os (pop θ))) (Cons v env)
    ∎
law-eval-transform (Let e e₁) env = {!!}
law-eval-transform (Val x) env = {!!}
law-eval-transform (Plus e e₁) env = {!!}


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
  ≡⟨ {!!} ⟩
    eval (transform le θ) env
  ≡⟨ transform-correct' le env ⟩
    eval (forget le) env
  ≡⟨ cong (λ x → eval x env) (analyse-preserves e) ⟩
    eval e env
  ∎

{-
-- A direct proof would look like this:
dbe-correct' :
  (e : Expr σ Γ) (env : Env Γ) →
  let e' ↑ θ = dbe e
  in eval e' (project-Env θ env) ≡ eval e env
dbe-correct' (Var x) env = {!!}
dbe-correct' (App e₁ e₂) env = {!!}
dbe-correct' (Lam e₁) env = {!!}
dbe-correct' (Let e₁ e₂) env with analyse e₁ | analyse e₂ | dbe-correct' e₁ env | dbe-correct' e₂ (Cons (eval e₁ env) env)
... | Δ₁ , θ₁ , e₁' | Δ₂ , o' θ₂ , e₂' | h₁ | h₂ =
  h₂
... | Δ₁ , θ₁ , e₁' | Δ₂ , os θ₂ , e₂' | h₁ | h₂ =
    eval (transform e₂' (os (un-∪₂ θ₁ θ₂ ₒ oi)))
      (Cons (eval (transform e₁' (un-∪₁ θ₁ θ₂ ₒ oi)) (project-Env (θ₁ ∪ θ₂) env)) (project-Env (θ₁ ∪ θ₂) env))
  ≡⟨ {!!} ⟩
    eval (transform e₂' (os (un-∪₂ θ₁ θ₂ ₒ oi)))
      (Cons (eval (transform e₁' oi) (project-Env θ₁ env)) (project-Env (θ₁ ∪ θ₂) env))
  ≡⟨ cong (λ x → eval (transform e₂' (os (un-∪₂ θ₁ θ₂ ₒ oi))) (Cons x _)) h₁ ⟩
    eval (transform e₂' (os (un-∪₂ θ₁ θ₂ ₒ oi)))
      (Cons (eval e₁ env) (project-Env (θ₁ ∪ θ₂) env))
  ≡⟨ {!!} ⟩
    eval (transform e₂' (os oi)) (Cons (eval e₁ env) (project-Env θ₂ env))
  ≡⟨ h₂ ⟩
    eval e₂ (Cons (eval e₁ env) env)
  ∎
dbe-correct' (Val v) env = {!!}
dbe-correct' (Plus e₁ e₂) env = {!!}
-}
