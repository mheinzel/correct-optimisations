module Lang where

open import Data.Nat
  using (_+_ ; _≡ᵇ_) renaming (ℕ to Nat ; zero to Zero ; suc to Succ)
open import Data.Bool using (Bool)
open import Data.List using (List ; _∷_ ; [])
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

-- Types
data U : Set where
  BOOL NAT : U

⟦_⟧ : U → Set
⟦ BOOL ⟧  = Bool
⟦ NAT ⟧   = Nat

Ctx = List U

variable
  n : Nat
  b : Bool
  Γ : Ctx
  σ τ : U

-- Syntax
data Ref (σ : U) : Ctx → Set where
  Top  : Ref σ (σ ∷ Γ)
  Pop  : Ref σ Γ → Ref σ (τ ∷ Γ)
 
data Expr (Γ : Ctx) : (σ : U) → Set where
  Val : ⟦ σ ⟧ → Expr Γ σ
  Plus : Expr Γ NAT → Expr Γ NAT → Expr Γ NAT
  Eq : Expr Γ NAT → Expr Γ NAT → Expr Γ BOOL
  Let : (decl : Expr Γ σ) → (body : Expr (σ ∷ Γ) τ) → Expr Γ τ
  Var : Ref σ Γ → Expr Γ σ

-- Semantics
data Env : Ctx → Set where
  Nil   : Env []
  Cons  : ⟦ σ ⟧ → Env Γ → Env (σ ∷ Γ)

lookup : Ref σ Γ → Env Γ → ⟦ σ ⟧
lookup Top        (Cons x env)   = x
lookup (Pop ref)  (Cons x env)   = lookup ref env

eval : Expr Γ σ → Env Γ → ⟦ σ ⟧
eval (Val x) env = x
eval (Eq n m) env = (eval n env) ≡ᵇ (eval m env)
eval (Plus e₁ e₂) env = eval e₁ env + eval e₂ env
eval (Let e body) env = eval body (Cons (eval e env) env)
eval (Var x) env = lookup x env 

-- Examples

-- let x = 1 in let y = x in 2
ex-unused : Expr Γ NAT
ex-unused = Let (Val 1) (Let (Var Top) (Val 2))

-- λ a → let x = a in let y = 1 in let z = x + 5 in y + a
ex-unused-2 : Expr (NAT ∷ Γ) NAT
ex-unused-2 =
  Let (Var Top)
    (Let (Val 1)
      (Let (Var (Pop Top))
        (Plus (Var (Pop Top)) (Var (Pop (Pop (Pop Top)))))))

test-ex-unused : (env : Env Γ) → eval ex-unused env ≡ 2
test-ex-unused env = refl

test-ex-unused-2 : (env : Env Γ) (n : Nat) → eval ex-unused-2 (Cons n env) ≡ Succ n
test-ex-unused-2 env n = refl
