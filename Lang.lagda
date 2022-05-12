\begin{code}[hide]
module Lang where

open import Data.Nat using (_+_) renaming (ℕ to Nat ; zero to Zero ; suc to Succ)
open import Data.Bool using (Bool)
open import Data.List using (List ; _∷_ ; [])
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
\end{code}

\newcommand{\CodeLangSyntax}{%
\begin{code}
-- Types
data U : Set where
  BOOL NAT : U

⟦_⟧ : U → Set
⟦ BOOL ⟧  = Bool
⟦ NAT ⟧   = Nat

Ctx = List U

variable
  Γ : Ctx
  σ τ : U

-- Syntax
data Ref (σ : U) : Ctx → Set where
  Top  : Ref σ (σ ∷ Γ)
  Pop  : Ref σ Γ → Ref σ (τ ∷ Γ)

data Expr (Γ : Ctx) : (σ : U) → Set where
  Val : ⟦ σ ⟧ → Expr Γ σ
  Plus : Expr Γ NAT → Expr Γ NAT → Expr Γ NAT
  Let : (decl : Expr Γ σ) → (body : Expr (σ ∷ Γ) τ) → Expr Γ τ
  Var : Ref σ Γ → Expr Γ σ
\end{code}}

\begin{code}[hide]
-- Semantics
data Env : Ctx → Set where
  Nil   : Env []
  Cons  : ⟦ σ ⟧ → Env Γ → Env (σ ∷ Γ)

lookup : Ref σ Γ → Env Γ → ⟦ σ ⟧
lookup Top        (Cons x env)   = x
lookup (Pop ref)  (Cons x env)   = lookup ref env

eval : Expr Γ σ → Env Γ → ⟦ σ ⟧
eval (Val x) env = x
eval (Plus e₁ e₂) env = eval e₁ env + eval e₂ env
eval (Let e body) env = eval body (Cons (eval e env) env)
eval (Var x) env = lookup x env 

-- Number of Let constructors
num-bindings : Expr Γ σ → Nat
num-bindings (Val x) = Zero
num-bindings (Plus e₁ e₂) = num-bindings e₁ + num-bindings e₂
num-bindings (Let e₁ e₂) = Succ (num-bindings e₁ + num-bindings e₂)
num-bindings (Var x) = Zero
\end{code}
