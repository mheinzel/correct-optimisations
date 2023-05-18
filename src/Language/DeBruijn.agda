module Language.DeBruijn where

open import Data.Nat using (_+_) renaming (ℕ to Nat ; zero to Zero ; suc to Succ)
open import Data.Bool using (Bool)
open import Data.List using (List ; _∷_ ; [])
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; trans ; cong ; cong₂)
open import Function using (_$_)

open import Data.Thinning

open import Postulates using (extensionality)
open import Language.Core
open Language.Core.Env {U} {⟦_⟧}
open Language.Core.Ref {U} {⟦_⟧}

private
  variable
    σ τ : U
    Δ Γ Γ₁ Γ₂ Γ₃ : Ctx

data Expr : U → Ctx → Set where
  Var   : Ref σ Γ → Expr σ Γ
  App   : Expr (σ ⇒ τ) Γ → Expr σ Γ → Expr τ Γ
  Lam   : Expr τ (σ ∷ Γ) → Expr (σ ⇒ τ) Γ
  Let   : (decl : Expr σ Γ) → (body : Expr τ (σ ∷ Γ)) → Expr τ Γ
  Val   : ⟦ σ ⟧ → Expr σ Γ
  Plus  : Expr NAT Γ → Expr NAT Γ → Expr NAT Γ

eval : Expr σ Γ → Env Γ → ⟦ σ ⟧
eval (Var x)       env  = lookup x env
eval (App e₁ e₂)   env  = eval e₁ env (eval e₂ env)
eval (Lam e)       env  = λ v → eval e (Cons v env)
eval (Let e₁ e₂)   env  = eval e₂ (Cons (eval e₁ env) env)
eval (Val v)       env  = v
eval (Plus e₁ e₂)  env  = eval e₁ env + eval e₂ env

-- Number of Let constructors
num-bindings : Expr σ Γ → Nat
num-bindings (Var x)       = Zero
num-bindings (App e₁ e₂)   = num-bindings e₁ + num-bindings e₂
num-bindings (Lam e)       = num-bindings e
num-bindings (Let e₁ e₂)   = Succ (num-bindings e₁ + num-bindings e₂)
num-bindings (Val v)       = Zero
num-bindings (Plus e₁ e₂)  = num-bindings e₁ + num-bindings e₂

rename-Expr : Δ ⊑ Γ → Expr σ Δ → Expr σ Γ
rename-Expr θ (Var x) = Var (rename-Ref θ x)
rename-Expr θ (App e₁ e₂) = App (rename-Expr θ e₁) (rename-Expr θ e₂)
rename-Expr θ (Lam e) = Lam (rename-Expr (os θ) e)
rename-Expr θ (Let e₁ e₂) = Let (rename-Expr θ e₁) (rename-Expr (os θ) e₂)
rename-Expr θ (Val v) = Val v
rename-Expr θ (Plus e₁ e₂) = Plus (rename-Expr θ e₁) (rename-Expr θ e₂)

rename-Expr⇑ : Expr σ ⇑ Γ → Expr σ Γ
rename-Expr⇑ (e ↑ θ) = rename-Expr θ e

weaken : Expr σ Γ → Expr σ (τ ∷ Γ)
weaken = rename-Expr (o' oi)

law-rename-Expr-ₒ :
  (e : Expr σ Γ₁) (θ : Γ₁ ⊑ Γ₂) (ϕ : Γ₂ ⊑ Γ₃) →
  rename-Expr (θ ₒ ϕ) e ≡  rename-Expr ϕ (rename-Expr θ e)
law-rename-Expr-ₒ (Var x) θ ϕ =
  cong Var (law-rename-Ref-ₒ x θ ϕ)
law-rename-Expr-ₒ (App e₁ e₂) θ ϕ =
  cong₂ App (law-rename-Expr-ₒ e₁ θ ϕ) (law-rename-Expr-ₒ e₂ θ ϕ)
law-rename-Expr-ₒ (Lam e₁) θ ϕ =
  cong Lam (law-rename-Expr-ₒ e₁ (os θ) (os ϕ))
law-rename-Expr-ₒ (Let e₁ e₂) θ ϕ =
  cong₂ Let (law-rename-Expr-ₒ e₁ θ ϕ) (law-rename-Expr-ₒ e₂ (os θ) (os ϕ))
law-rename-Expr-ₒ (Val v) θ ϕ =
  refl
law-rename-Expr-ₒ (Plus e₁ e₂) θ ϕ =
  cong₂ Plus (law-rename-Expr-ₒ e₁ θ ϕ) (law-rename-Expr-ₒ e₂ θ ϕ)

law-eval-rename-Expr :
  (e : Expr σ Δ) (θ : Δ ⊑ Γ) (env : Env Γ) →
  eval (rename-Expr θ e) env ≡ eval e (project-Env θ env)
law-eval-rename-Expr (Var x) θ env =
  law-lookup-rename-Ref x θ env
law-eval-rename-Expr (App e₁ e₂) θ env =
  cong₂ _$_
    (law-eval-rename-Expr e₁ θ env)
    (law-eval-rename-Expr e₂ θ env)
law-eval-rename-Expr (Lam e₁) θ env =
  extensionality _ _ λ v →
    law-eval-rename-Expr e₁ (os θ) (Cons v env)
law-eval-rename-Expr (Let e₁ e₂) θ env =
  trans
    (cong (λ x → eval (rename-Expr (os θ) e₂) (Cons x env)) (law-eval-rename-Expr e₁ θ env))
    (law-eval-rename-Expr e₂ (os θ) (Cons _ env))
law-eval-rename-Expr (Val v) θ env =
  refl
law-eval-rename-Expr (Plus e₁ e₂) θ env =
  cong₂ _+_
    (law-eval-rename-Expr e₁ θ env)
    (law-eval-rename-Expr e₂ θ env)
