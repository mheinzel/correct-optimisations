module Lang where

open import Data.Nat using (_+_) renaming (ℕ to Nat ; zero to Zero ; suc to Succ)
open import Data.Bool using (Bool)
open import Data.List using (List ; _∷_ ; [])
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

data U : Set where
  _⇒_   : U → U → U
  BOOL  : U
  NAT   : U

⟦_⟧ : U → Set
⟦ σ ⇒ τ ⟧ = ⟦ σ ⟧ → ⟦ τ ⟧
⟦ BOOL ⟧  = Bool
⟦ NAT ⟧   = Nat

Ctx = List U

variable
  Γ : Ctx
  σ τ : U

data Env : Ctx → Set where
  Nil   : Env []
  Cons  : ⟦ σ ⟧ → Env Γ → Env (σ ∷ Γ)

data Ref (σ : U) : Ctx → Set where
  Top  : Ref σ (σ ∷ Γ)
  Pop  : Ref σ Γ → Ref σ (τ ∷ Γ)

lookup : Ref σ Γ → Env Γ → ⟦ σ ⟧
lookup Top      (Cons v env)   = v
lookup (Pop i)  (Cons v env)   = lookup i env

data Expr (Γ : Ctx) : (σ : U) → Set where
  Var   : Ref σ Γ → Expr Γ σ
  App   : Expr Γ (σ ⇒ τ) → Expr Γ σ → Expr Γ τ
  Lam   : Expr (σ ∷ Γ) τ → Expr Γ (σ ⇒ τ)
  Let   : (decl : Expr Γ σ) → (body : Expr (σ ∷ Γ) τ) → Expr Γ τ
  Val   : ⟦ σ ⟧ → Expr Γ σ
  Plus  : Expr Γ NAT → Expr Γ NAT → Expr Γ NAT

eval : Expr Γ σ → Env Γ → ⟦ σ ⟧
eval (Var x)       env  = lookup x env
eval (App e₁ e₂)   env  = eval e₁ env (eval e₂ env)
eval (Lam e)       env  = λ v → eval e (Cons v env)
eval (Let e₁ e₂)   env  = eval e₂ (Cons (eval e₁ env) env)
eval (Val v)       env  = v
eval (Plus e₁ e₂)  env  = eval e₁ env + eval e₂ env

-- Number of Let constructors
num-bindings : Expr Γ σ → Nat
num-bindings (Var x)       = Zero
num-bindings (App e₁ e₂)   = num-bindings e₁ + num-bindings e₂
num-bindings (Lam e)       = num-bindings e
num-bindings (Let e₁ e₂)   = Succ (num-bindings e₁ + num-bindings e₂)
num-bindings (Val v)       = Zero
num-bindings (Plus e₁ e₂)  = num-bindings e₁ + num-bindings e₂
