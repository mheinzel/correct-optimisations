{-# OPTIONS --allow-unsolved-metas #-}  -- TODO: implement renaming

module Language.DeBruijn where

open import Data.Nat using (_+_) renaming (ℕ to Nat ; zero to Zero ; suc to Succ)
open import Data.Bool using (Bool)
open import Data.List using (List ; _∷_ ; [])
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import Data.OPE

open import Language.Core
open Language.Core.Env {U} {⟦_⟧}
open Language.Core.Ref {U} {⟦_⟧}

private
  variable
    σ τ : U
    Δ Γ : Ctx

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
rename-Expr θ e = {!!}
