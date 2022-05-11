\begin{code}[hide]
module Subset where

open import Data.Nat using (_+_ ; _≡ᵇ_) renaming (ℕ to Nat)
open import Data.List using (List ; _∷_ ; [])
open import Data.Unit
open import Data.Product
open import Data.Empty
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; cong₂)

open import Lang
\end{code}

\newcommand{\CodeSubsetSubset}{%
\begin{code}
-- Subsets of our context and operations on them 
data Subset : Ctx → Set where
  Empty  : Subset []
  Drop   : Subset Γ → Subset (τ ∷ Γ)
  Keep   : Subset Γ → Subset (τ ∷ Γ)
\end{code}}

\begin{code}[hide]
variable
  Δ Δ' Δ₁ Δ₂ : Subset Γ

∅ : {Γ : Ctx} → Subset Γ
∅ {[]} = Empty
∅ {x ∷ Γ} = Drop ∅

all : (Γ : Ctx) → Subset Γ
all [] = Empty
all (x ∷ Γ) = Keep (all Γ)

_∪_ : Subset Γ → Subset Γ → Subset Γ
Empty ∪ Empty = Empty
Drop Δ₁ ∪ Drop Δ₂ = Drop (Δ₁ ∪ Δ₂)
Drop Δ₁ ∪ Keep Δ₂ = Keep (Δ₁ ∪ Δ₂)
Keep Δ₁ ∪ Drop Δ₂ = Keep (Δ₁ ∪ Δ₂)
Keep Δ₁ ∪ Keep Δ₂ = Keep (Δ₁ ∪ Δ₂)

⌊_⌋ : Subset Γ → Ctx
⌊ Empty ⌋              = []
⌊ Drop Δ ⌋             = ⌊ Δ ⌋
⌊ Keep {τ = τ} Δ ⌋     = τ ∷ ⌊ Δ ⌋

_[_] : (Δ : Subset Γ) → Ref τ ⌊ Δ ⌋ → Subset Γ
(Drop Δ) [ i ] = Drop (Δ [ i ])
(Keep Δ) [ Top ]  = Keep ∅
(Keep Δ) [ Pop i ] = Drop (Δ [ i ])

pop : Subset (σ ∷ Γ) → Subset Γ
pop (Drop Δ) = Δ
pop (Keep Δ) = Δ
\end{code}

-- Relating subsets and environments
\newcommand{\CodeSubsetOpSubseteq}{%
\begin{code}
_⊆_ : Subset Γ → Subset Γ → Set
Δ₁ ⊆ Keep Δ₂ = pop Δ₁ ⊆ Δ₂
Empty ⊆ Empty = ⊤
Drop Δ₁ ⊆ Drop Δ₂ = Δ₁ ⊆ Δ₂
Keep Δ₁ ⊆ Drop Δ₂ = ⊥
\end{code}}

\begin{code}[hide]
∅⊆ : (Γ : Ctx) → (Δ : Subset Γ) → ∅ ⊆ Δ
∅⊆ [] Empty = tt
∅⊆ (x ∷ Γ) (Drop Δ) = ∅⊆ Γ Δ
∅⊆ (x ∷ Γ) (Keep Δ) = ∅⊆ Γ Δ

⊆all : (Γ : Ctx) → (Δ : Subset Γ) → Δ ⊆ all Γ
⊆all Γ Empty = tt
⊆all (x ∷ Γ) (Drop Δ) = ⊆all Γ Δ
⊆all (x ∷ Γ) (Keep Δ) = ⊆all Γ Δ

∪⊆ : (Γ : Ctx) → (Δ₁ Δ₂ Δ : Subset Γ) → .(H₁ : Δ₁ ⊆ Δ) → .(H₂ : Δ₂ ⊆ Δ) →
  (Δ₁ ∪ Δ₂) ⊆ Δ
∪⊆ [] Empty Empty Empty H₁ H₂ = tt
∪⊆ (_ ∷ Γ) (Drop Δ₁) (Drop Δ₂) (Drop Δ) H₁ H₂ = ∪⊆ Γ Δ₁ Δ₂ Δ H₁ H₂
∪⊆ (_ ∷ Γ) (Drop Δ₁) (Drop Δ₂) (Keep Δ) H₁ H₂ = ∪⊆ Γ Δ₁ Δ₂ Δ H₁ H₂
∪⊆ (_ ∷ Γ) (Drop Δ₁) (Keep Δ₂) (Keep Δ) H₁ H₂ = ∪⊆ Γ Δ₁ Δ₂ Δ H₁ H₂
∪⊆ (_ ∷ Γ) (Keep Δ₁) (Drop Δ₂) (Keep Δ) H₁ H₂ = ∪⊆ Γ Δ₁ Δ₂ Δ H₁ H₂
∪⊆ (_ ∷ Γ) (Keep Δ₁) (Keep Δ₂) (Keep Δ) H₁ H₂ = ∪⊆ Γ Δ₁ Δ₂ Δ H₁ H₂

⊆∪₁ : (Δ₁ Δ₂ : Subset Γ) → Δ₁ ⊆ (Δ₁ ∪ Δ₂)
⊆∪₁ Empty Empty = tt
⊆∪₁ (Drop Δ₁) (Drop Δ₂) = ⊆∪₁ Δ₁ Δ₂
⊆∪₁ (Drop Δ₁) (Keep Δ₂) = ⊆∪₁ Δ₁ Δ₂
⊆∪₁ (Keep Δ₁) (Drop Δ₂) = ⊆∪₁ Δ₁ Δ₂
⊆∪₁ (Keep Δ₁) (Keep Δ₂) = ⊆∪₁ Δ₁ Δ₂

⊆∪₂ : (Δ₁ Δ₂ : Subset Γ) → Δ₂ ⊆ (Δ₁ ∪ Δ₂)  
⊆∪₂ Empty Empty = tt
⊆∪₂ (Drop Δ₁) (Drop Δ₂) = ⊆∪₂ Δ₁ Δ₂
⊆∪₂ (Drop Δ₁) (Keep Δ₂) = ⊆∪₂ Δ₁ Δ₂
⊆∪₂ (Keep Δ₁) (Drop Δ₂) = ⊆∪₂ Δ₁ Δ₂
⊆∪₂ (Keep Δ₁) (Keep Δ₂) = ⊆∪₂ Δ₁ Δ₂

[i]⊆ : (Γ : Ctx) (Δ : Subset Γ) (i : Ref σ ⌊ Δ ⌋) → (Δ [ i ]) ⊆ Δ
[i]⊆ [] Empty ()
[i]⊆ (τ ∷ Γ) (Drop Δ) i = [i]⊆ Γ Δ i
[i]⊆ (τ ∷ Γ) (Keep Δ) Top = ∅⊆ Γ Δ
[i]⊆ (τ ∷ Γ) (Keep Δ) (Pop i) = [i]⊆ Γ Δ i

⊆-refl : (Δ : Subset Γ) → Δ ⊆ Δ
⊆-refl Empty = tt
⊆-refl (Drop Δ) = ⊆-refl Δ
⊆-refl (Keep Δ) = ⊆-refl Δ

⊆-trans : (Δ₁ Δ₂ Δ₃ : Subset Γ) → (Δ₁ ⊆ Δ₂) → (Δ₂ ⊆ Δ₃) → Δ₁ ⊆ Δ₃
⊆-trans Empty Empty Empty Δ₁⊆Δ₂ Δ₂⊆Δ₃ = tt
⊆-trans (Drop Δ₁) (Drop Δ₂) (Drop Δ₃) Δ₁⊆Δ₂ Δ₂⊆Δ₃ = ⊆-trans Δ₁ Δ₂ Δ₃ Δ₁⊆Δ₂ Δ₂⊆Δ₃
⊆-trans (Drop Δ₁) (Drop Δ₂) (Keep Δ₃) Δ₁⊆Δ₂ Δ₂⊆Δ₃ = ⊆-trans Δ₁ Δ₂ Δ₃ Δ₁⊆Δ₂ Δ₂⊆Δ₃
⊆-trans (Drop Δ₁) (Keep Δ₂) (Keep Δ₃) Δ₁⊆Δ₂ Δ₂⊆Δ₃ = ⊆-trans Δ₁ Δ₂ Δ₃ Δ₁⊆Δ₂ Δ₂⊆Δ₃
⊆-trans (Keep Δ₁) (Keep Δ₂) (Keep Δ₃) Δ₁⊆Δ₂ Δ₂⊆Δ₃ = ⊆-trans Δ₁ Δ₂ Δ₃ Δ₁⊆Δ₂ Δ₂⊆Δ₃

-- Renamings / weakenings
renameVar : (Δ₁ Δ₂ : Subset Γ) → .(Δ₁ ⊆ Δ₂) → Ref σ ⌊ Δ₁ ⌋ → Ref σ ⌊ Δ₂ ⌋
renameVar (Drop Δ₁) (Drop Δ₂) H i = renameVar Δ₁ Δ₂ H i
renameVar (Drop Δ₁) (Keep Δ₂) H i = Pop (renameVar Δ₁ Δ₂ H i)
renameVar (Keep Δ₁) (Keep Δ₂) H Top = Top
renameVar (Keep Δ₁) (Keep Δ₂) H (Pop i) = Pop (renameVar Δ₁ Δ₂ H i)

renameExpr : (Δ₁ Δ₂ : Subset Γ) → .(Δ₁ ⊆ Δ₂) → Expr ⌊ Δ₁ ⌋ σ → Expr ⌊ Δ₂ ⌋ σ
renameExpr Δ₁ Δ₂ H (Val x) = Val x
renameExpr Δ₁ Δ₂ H (Plus e₁ e₂) = Plus (renameExpr Δ₁ Δ₂ H e₁) (renameExpr Δ₁ Δ₂ H e₂)
renameExpr Δ₁ Δ₂ H (Let e₁ e₂) = Let (renameExpr Δ₁ Δ₂ H e₁) (renameExpr (Keep Δ₁) (Keep Δ₂) H e₂)
renameExpr Δ₁ Δ₂ H (Var x) = Var (renameVar Δ₁ Δ₂ H x)

injExpr₁ : (Δ₁ Δ₂ : Subset Γ) → Expr ⌊ Δ₁ ⌋ σ → Expr ⌊ Δ₁ ∪ Δ₂ ⌋ σ
injExpr₁ Δ₁ Δ₂ = renameExpr Δ₁ (Δ₁ ∪ Δ₂) (⊆∪₁ Δ₁ Δ₂)

injExpr₂ : (Δ₁ Δ₂ : Subset Γ) → Expr ⌊ Δ₂ ⌋ σ → Expr ⌊ Δ₁ ∪ Δ₂ ⌋ σ
injExpr₂ Δ₁ Δ₂ = renameExpr Δ₂ (Δ₁ ∪ Δ₂) (⊆∪₂ Δ₁ Δ₂)

-- Restricting an environment to some subset of (required) values
prjEnv : (Δ₁ Δ₂ : Subset Γ) → .(Δ₁ ⊆ Δ₂) → Env ⌊ Δ₂ ⌋ → Env ⌊ Δ₁ ⌋
prjEnv Empty Empty prf env = env
prjEnv (Drop Δ₁) (Drop Δ₂) prf env = prjEnv Δ₁ Δ₂ prf env
prjEnv (Drop Δ₁) (Keep Δ₂) prf (Cons x env) = prjEnv Δ₁ Δ₂ prf env
prjEnv (Keep Δ₁) (Keep Δ₂) prf (Cons x env) = Cons x (prjEnv Δ₁ Δ₂ prf env)

prjEnv₁ : (Δ₁ Δ₂ : Subset Γ) → Env ⌊ Δ₁ ∪ Δ₂ ⌋ → Env ⌊ Δ₁ ⌋
prjEnv₁ Δ₁ Δ₂ = prjEnv Δ₁ (Δ₁ ∪ Δ₂) (⊆∪₁ Δ₁ Δ₂)

prjEnv₂ : (Δ₁ Δ₂ : Subset Γ) → Env ⌊ Δ₁ ∪ Δ₂ ⌋ → Env ⌊ Δ₂ ⌋
prjEnv₂ Δ₁ Δ₂ = prjEnv Δ₂ (Δ₁ ∪ Δ₂) (⊆∪₂ Δ₁ Δ₂)

prjEnv-trans : (Δ₁ Δ₂ Δ₃ : Subset Γ) → .(H₁₂ : Δ₁ ⊆ Δ₂) → .(H₂₃ : Δ₂ ⊆ Δ₃) → (env : Env ⌊ Δ₃ ⌋) →
  prjEnv Δ₁ Δ₂ H₁₂ (prjEnv Δ₂ Δ₃ H₂₃ env) ≡ prjEnv Δ₁ Δ₃ (⊆-trans Δ₁ Δ₂ Δ₃ H₁₂ H₂₃) env
prjEnv-trans Empty Empty Empty H₁₂ H₂₃ env = refl
prjEnv-trans (Drop Δ₁) (Drop Δ₂) (Drop Δ₃) H₁₂ H₂₃ env = prjEnv-trans Δ₁ Δ₂ Δ₃ H₁₂ H₂₃ env
prjEnv-trans (Drop Δ₁) (Drop Δ₂) (Keep Δ₃) H₁₂ H₂₃ (Cons x env) = prjEnv-trans Δ₁ Δ₂ Δ₃ H₁₂ H₂₃ env
prjEnv-trans (Drop Δ₁) (Keep Δ₂) (Keep Δ₃) H₁₂ H₂₃ (Cons x env) = prjEnv-trans Δ₁ Δ₂ Δ₃ H₁₂ H₂₃ env
prjEnv-trans (Keep Δ₁) (Keep Δ₂) (Keep Δ₃) H₁₂ H₂₃ (Cons x env) = cong (Cons x) (prjEnv-trans Δ₁ Δ₂ Δ₃ H₁₂ H₂₃ env)

-- Properties of renamings
renameVar-id : (Δ : Subset Γ) (i : Ref σ ⌊ Δ ⌋) → renameVar Δ Δ (⊆-refl Δ) i ≡ i
renameVar-id (Drop Δ) i = renameVar-id Δ i
renameVar-id (Keep Δ) Top = refl
renameVar-id (Keep Δ) (Pop i) = cong Pop (renameVar-id Δ i)

renameExpr-id : (Δ : Subset Γ) (e : Expr ⌊ Δ ⌋ σ) → renameExpr Δ Δ (⊆-refl Δ) e ≡ e
renameExpr-id Δ (Val x) = refl
renameExpr-id Δ (Plus e₁ e₂) = cong₂ Plus (renameExpr-id Δ e₁) (renameExpr-id Δ e₂)
renameExpr-id Δ (Let e₁ e₂) = cong₂ Let (renameExpr-id Δ e₁) (renameExpr-id (Keep Δ) e₂)
renameExpr-id Δ (Var x) = cong Var (renameVar-id Δ x)

renameVar-trans : (Δ₁ Δ₂ Δ₃ : Subset Γ) → .(H₁₂ : Δ₁ ⊆ Δ₂) → .(H₂₃ : Δ₂ ⊆ Δ₃) → (i : Ref σ ⌊ Δ₁ ⌋) →
  renameVar Δ₂ Δ₃ H₂₃ (renameVar Δ₁ Δ₂ H₁₂ i) ≡ renameVar Δ₁ Δ₃ (⊆-trans Δ₁ Δ₂ Δ₃ H₁₂ H₂₃) i
renameVar-trans (Drop Δ₁) (Drop Δ₂) (Drop Δ₃) H₁₂ H₂₃ i = renameVar-trans Δ₁ Δ₂ Δ₃ H₁₂ H₂₃ i
renameVar-trans (Drop Δ₁) (Drop Δ₂) (Keep Δ₃) H₁₂ H₂₃ i = cong Pop (renameVar-trans Δ₁ Δ₂ Δ₃ H₁₂ H₂₃ i)
renameVar-trans (Drop Δ₁) (Keep Δ₂) (Keep Δ₃) H₁₂ H₂₃ i = cong Pop (renameVar-trans Δ₁ Δ₂ Δ₃ H₁₂ H₂₃ i)
renameVar-trans (Keep Δ₁) (Keep Δ₂) (Keep Δ₃) H₁₂ H₂₃ Top = refl
renameVar-trans (Keep Δ₁) (Keep Δ₂) (Keep Δ₃) H₁₂ H₂₃ (Pop i) = cong Pop (renameVar-trans Δ₁ Δ₂ Δ₃ H₁₂ H₂₃ i)

renameExpr-trans : (Δ₁ Δ₂ Δ₃ : Subset Γ) → .(H₁₂ : Δ₁ ⊆ Δ₂) → .(H₂₃ : Δ₂ ⊆ Δ₃) → (e : Expr ⌊ Δ₁ ⌋ σ) →
  renameExpr Δ₂ Δ₃ H₂₃ (renameExpr Δ₁ Δ₂ H₁₂ e) ≡ renameExpr Δ₁ Δ₃ (⊆-trans Δ₁ Δ₂ Δ₃ H₁₂ H₂₃) e
renameExpr-trans Δ₁ Δ₂ Δ₃ H₁₂ H₂₃ (Val x) =
  refl
renameExpr-trans Δ₁ Δ₂ Δ₃ H₁₂ H₂₃ (Plus e₁ e₂) =
  cong₂ Plus (renameExpr-trans Δ₁ Δ₂ Δ₃ H₁₂ H₂₃ e₁) (renameExpr-trans Δ₁ Δ₂ Δ₃ H₁₂ H₂₃ e₂)
renameExpr-trans Δ₁ Δ₂ Δ₃ H₁₂ H₂₃ (Let e₁ e₂) =
  cong₂ Let (renameExpr-trans Δ₁ Δ₂ Δ₃ H₁₂ H₂₃ e₁) (renameExpr-trans (Keep Δ₁) (Keep Δ₂) (Keep Δ₃) H₁₂ H₂₃ e₂)
renameExpr-trans Δ₁ Δ₂ Δ₃ H₁₂ H₂₃ (Var x) =
  cong Var (renameVar-trans Δ₁ Δ₂ Δ₃ H₁₂ H₂₃ x)

renameVar-preserves : (Δ₁ Δ₂ : Subset Γ) → .(H : Δ₁ ⊆ Δ₂) → (i : Ref σ ⌊ Δ₁ ⌋) (env : Env ⌊ Δ₂ ⌋) →
  lookup (renameVar Δ₁ Δ₂ H i) env ≡ lookup i (prjEnv Δ₁ Δ₂ H env)
renameVar-preserves (Drop Δ₁) (Drop Δ₂) H i env = renameVar-preserves Δ₁ Δ₂ H i env
renameVar-preserves (Drop Δ₁) (Keep Δ₂) H i (Cons x env) = renameVar-preserves Δ₁ Δ₂ H i env
renameVar-preserves (Keep Δ₁) (Keep Δ₂) H Top (Cons x env) = refl
renameVar-preserves (Keep Δ₁) (Keep Δ₂) H (Pop i) (Cons x env) = renameVar-preserves Δ₁ Δ₂ H i env

renameExpr-preserves : (Δ₁ Δ₂ : Subset Γ) → .(H : Δ₁ ⊆ Δ₂) → (e : Expr ⌊ Δ₁ ⌋ σ) (env : Env ⌊ Δ₂ ⌋) →
  eval (renameExpr Δ₁ Δ₂ H e) env ≡ eval e (prjEnv Δ₁ Δ₂ H env)
renameExpr-preserves Δ₁ Δ₂ H (Val x) env = refl
renameExpr-preserves Δ₁ Δ₂ H (Plus e₁ e₂) env =
  cong₂ _+_ (renameExpr-preserves Δ₁ Δ₂ H e₁ env) (renameExpr-preserves Δ₁ Δ₂ H e₂ env)
renameExpr-preserves Δ₁ Δ₂ H (Let e₁ e₂) env =
    eval (renameExpr (Keep Δ₁) (Keep Δ₂) _ e₂) (Cons (eval (renameExpr Δ₁ Δ₂ _ e₁) env) env)
  ≡⟨ renameExpr-preserves (Keep Δ₁) (Keep Δ₂ ) _ e₂ (Cons (eval (renameExpr Δ₁ Δ₂ H e₁) env) env) ⟩
    eval e₂ (prjEnv (Keep Δ₁) (Keep Δ₂) _ (Cons (eval (renameExpr Δ₁ Δ₂ _ e₁) env) env))
  ≡⟨ cong (λ x → eval e₂ (Cons x (prjEnv Δ₁ Δ₂ _ env))) (renameExpr-preserves Δ₁ Δ₂ H e₁ env) ⟩
    eval e₂ (Cons (eval e₁ (prjEnv Δ₁ Δ₂ _ env)) (prjEnv Δ₁ Δ₂ _ env))
  ∎
  where
    open Relation.Binary.PropositionalEquality.≡-Reasoning
renameExpr-preserves Δ₁ Δ₂ H (Var x) env = renameVar-preserves Δ₁ Δ₂ H x env
\end{code}
