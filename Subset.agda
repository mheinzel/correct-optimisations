module Subset where

open import Data.Nat using (_+_ ; _≡ᵇ_)
open import Data.List using (List ; _∷_ ; [])
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; cong₂)

open import Lang

-- Subsets of our context and operations on them 
data Subset : Ctx → Set where
  Empty  : Subset []
  Drop   : Subset Γ → Subset (τ ∷ Γ)
  Keep   : Subset Γ → Subset (τ ∷ Γ)

variable
  Δ Δ₁ Δ₂ : Subset Γ

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

[_] : Ref τ Γ → Subset Γ
[ Top ]    = Keep ∅
[ Pop p ]  = Drop [ p ]

pop : Subset (σ ∷ Γ) → Subset Γ
pop (Drop Δ) = Δ
pop (Keep Δ) = Δ

⌊_⌋ : Subset Γ → Ctx
⌊ Empty ⌋              = []
⌊ Drop Δ ⌋             = ⌊ Δ ⌋
⌊ Keep {τ = τ} Δ ⌋     = τ ∷ ⌊ Δ ⌋

restrictedRef : (i : Ref σ Γ) → Ref σ ⌊ [ i ] ⌋
restrictedRef Top = Top
restrictedRef (Pop i) = restrictedRef i

⊆-of-all : (Γ : Ctx) → ⌊ all Γ ⌋ ≡ Γ
⊆-of-all [] = refl
⊆-of-all (x ∷ Γ) = cong (λ Γ' → x ∷ Γ') (⊆-of-all Γ)

env-of-all : Env Γ → Env ⌊ all Γ ⌋
env-of-all Nil = Nil
env-of-all (Cons x env) = Cons x (env-of-all env)

-- Relating subsets and environments
_⊆_ : Subset Γ → Subset Γ → Set
Δ₁ ⊆ Keep Δ₂ = pop Δ₁ ⊆ Δ₂
Empty ⊆ Empty = ⊤
Drop Δ₁ ⊆ Drop Δ₂ = Δ₁ ⊆ Δ₂
Keep Δ₁ ⊆ Drop Δ₂ = ⊥

subset-⊆ : (Γ : Ctx) → (Δ : Subset Γ) → Δ ⊆ all Γ
subset-⊆ Γ Empty = tt
subset-⊆ (x ∷ Γ) (Drop Δ) = subset-⊆ Γ Δ
subset-⊆ (x ∷ Γ) (Keep Δ) = subset-⊆ Γ Δ

⊆unique : (Δ₁ Δ₂ : Subset Γ) (H₁ H₂ : Δ₁ ⊆ Δ₂) → H₁ ≡ H₂
⊆unique Empty Empty H₁ H₂ = refl
⊆unique (Drop Δ₁) (Drop Δ₂) H₁ H₂ = ⊆unique Δ₁ Δ₂ H₁ H₂
⊆unique (Drop Δ₁) (Keep Δ₂) H₁ H₂ = ⊆unique Δ₁ Δ₂ H₁ H₂
⊆unique (Keep Δ₁) (Keep Δ₂) H₁ H₂ = ⊆unique Δ₁ Δ₂ H₁ H₂

⊆refl : (Δ : Subset Γ) → Δ ⊆ Δ
⊆refl Empty = tt
⊆refl (Drop Δ) = ⊆refl Δ
⊆refl (Keep Δ) = ⊆refl Δ

⊆trans : (Δ₁ Δ₂ Δ₃ : Subset Γ) → (Δ₁ ⊆ Δ₂) → (Δ₂ ⊆ Δ₃) → Δ₁ ⊆ Δ₃
⊆trans Empty Empty Empty Δ₁⊆Δ₂ Δ₂⊆Δ₃ = tt
⊆trans (Drop Δ₁) (Drop Δ₂) (Drop Δ₃) Δ₁⊆Δ₂ Δ₂⊆Δ₃ = ⊆trans Δ₁ Δ₂ Δ₃ Δ₁⊆Δ₂ Δ₂⊆Δ₃
⊆trans (Drop Δ₁) (Drop Δ₂) (Keep Δ₃) Δ₁⊆Δ₂ Δ₂⊆Δ₃ = ⊆trans Δ₁ Δ₂ Δ₃ Δ₁⊆Δ₂ Δ₂⊆Δ₃
⊆trans (Drop Δ₁) (Keep Δ₂) (Keep Δ₃) Δ₁⊆Δ₂ Δ₂⊆Δ₃ = ⊆trans Δ₁ Δ₂ Δ₃ Δ₁⊆Δ₂ Δ₂⊆Δ₃
⊆trans (Keep Δ₁) (Keep Δ₂) (Keep Δ₃) Δ₁⊆Δ₂ Δ₂⊆Δ₃ = ⊆trans Δ₁ Δ₂ Δ₃ Δ₁⊆Δ₂ Δ₂⊆Δ₃

∪sym : (Δ₁ Δ₂ : Subset Γ) → (Δ₁ ∪ Δ₂) ≡ (Δ₂ ∪ Δ₁)
∪sym Empty Empty = refl
∪sym (Drop x) (Drop y) = cong Drop (∪sym x y)
∪sym (Drop x) (Keep y) = cong Keep (∪sym x y)
∪sym (Keep x) (Drop y) = cong Keep (∪sym x y)
∪sym (Keep x) (Keep y) = cong Keep (∪sym x y)

∪sub₁ : (Δ₁ Δ₂ : Subset Γ) → Δ₁ ⊆ (Δ₁ ∪ Δ₂)
∪sub₁ Empty Empty = tt
∪sub₁ (Drop Δ₁) (Drop Δ₂) = ∪sub₁ Δ₁ Δ₂
∪sub₁ (Drop Δ₁) (Keep Δ₂) = ∪sub₁ Δ₁ Δ₂
∪sub₁ (Keep Δ₁) (Drop Δ₂) = ∪sub₁ Δ₁ Δ₂
∪sub₁ (Keep Δ₁) (Keep Δ₂) = ∪sub₁ Δ₁ Δ₂

∪sub₂ : (Δ₁ Δ₂ : Subset Γ) → Δ₂ ⊆ (Δ₁ ∪ Δ₂)  
∪sub₂ Empty Empty = tt
∪sub₂ (Drop Δ₁) (Drop Δ₂) = ∪sub₂ Δ₁ Δ₂
∪sub₂ (Drop Δ₁) (Keep Δ₂) = ∪sub₂ Δ₁ Δ₂
∪sub₂ (Keep Δ₁) (Drop Δ₂) = ∪sub₂ Δ₁ Δ₂
∪sub₂ (Keep Δ₁) (Keep Δ₂) = ∪sub₂ Δ₁ Δ₂

-- Renamings / weakenings
renameVar : (Δ₁ Δ₂ : Subset Γ) → .(Δ₁ ⊆ Δ₂) → Ref σ ⌊ Δ₁ ⌋ → Ref σ ⌊ Δ₂ ⌋
renameVar (Drop Δ₁) (Drop Δ₂) H i = renameVar Δ₁ Δ₂ H i
renameVar (Drop Δ₁) (Keep Δ₂) H i = Pop (renameVar Δ₁ Δ₂ H i)
renameVar (Keep Δ₁) (Keep Δ₂) H Top = Top
renameVar (Keep Δ₁) (Keep Δ₂) H (Pop i) = Pop (renameVar Δ₁ Δ₂ H i)

renameVar-trans : (Δ₁ Δ₂ Δ₃ : Subset Γ) → .(H₁₂ : Δ₁ ⊆ Δ₂) → .(H₂₃ : Δ₂ ⊆ Δ₃) → (i : Ref σ ⌊ Δ₁ ⌋) →
  renameVar Δ₂ Δ₃ H₂₃ (renameVar Δ₁ Δ₂ H₁₂ i) ≡ renameVar Δ₁ Δ₃ (⊆trans Δ₁ Δ₂ Δ₃ H₁₂ H₂₃) i
renameVar-trans (Drop Δ₁) (Drop Δ₂) (Drop Δ₃) H₁₂ H₂₃ i = renameVar-trans Δ₁ Δ₂ Δ₃ H₁₂ H₂₃ i
renameVar-trans (Drop Δ₁) (Drop Δ₂) (Keep Δ₃) H₁₂ H₂₃ i = cong Pop (renameVar-trans Δ₁ Δ₂ Δ₃ H₁₂ H₂₃ i)
renameVar-trans (Drop Δ₁) (Keep Δ₂) (Keep Δ₃) H₁₂ H₂₃ i = cong Pop (renameVar-trans Δ₁ Δ₂ Δ₃ H₁₂ H₂₃ i)
renameVar-trans (Keep Δ₁) (Keep Δ₂) (Keep Δ₃) H₁₂ H₂₃ Top = refl
renameVar-trans (Keep Δ₁) (Keep Δ₂) (Keep Δ₃) H₁₂ H₂₃ (Pop i) = cong Pop (renameVar-trans Δ₁ Δ₂ Δ₃ H₁₂ H₂₃ i)

-- TODO: Δ₁ Δ₂ implicit?
renameExpr : (Δ₁ Δ₂ : Subset Γ) → .(Δ₁ ⊆ Δ₂) → Expr ⌊ Δ₁ ⌋ σ → Expr ⌊ Δ₂ ⌋ σ
renameExpr Δ₁ Δ₂ H (Val x) = Val x
renameExpr Δ₁ Δ₂ H (Plus e₁ e₂) = Plus (renameExpr Δ₁ Δ₂ H e₁) (renameExpr Δ₁ Δ₂ H e₂)
renameExpr Δ₁ Δ₂ H (Eq e₁ e₂) = Eq (renameExpr Δ₁ Δ₂ H e₁) (renameExpr Δ₁ Δ₂ H e₂)
renameExpr Δ₁ Δ₂ H (Let e₁ e₂) = Let (renameExpr Δ₁ Δ₂ H e₁) (renameExpr (Keep Δ₁) (Keep Δ₂) H e₂)
renameExpr Δ₁ Δ₂ H (Var x) = Var (renameVar Δ₁ Δ₂ H x)

renameExpr-trans : (Δ₁ Δ₂ Δ₃ : Subset Γ) → .(H₁₂ : Δ₁ ⊆ Δ₂) → .(H₂₃ : Δ₂ ⊆ Δ₃) → (e : Expr ⌊ Δ₁ ⌋ σ) →
  renameExpr Δ₂ Δ₃ H₂₃ (renameExpr Δ₁ Δ₂ H₁₂ e) ≡ renameExpr Δ₁ Δ₃ (⊆trans Δ₁ Δ₂ Δ₃ H₁₂ H₂₃) e
renameExpr-trans Δ₁ Δ₂ Δ₃ H₁₂ H₂₃ (Val x) =
  refl
renameExpr-trans Δ₁ Δ₂ Δ₃ H₁₂ H₂₃ (Plus e₁ e₂) =
  cong₂ Plus (renameExpr-trans Δ₁ Δ₂ Δ₃ H₁₂ H₂₃ e₁) (renameExpr-trans Δ₁ Δ₂ Δ₃ H₁₂ H₂₃ e₂)
renameExpr-trans Δ₁ Δ₂ Δ₃ H₁₂ H₂₃ (Eq e₁ e₂) =
  cong₂ Eq (renameExpr-trans Δ₁ Δ₂ Δ₃ H₁₂ H₂₃ e₁) (renameExpr-trans Δ₁ Δ₂ Δ₃ H₁₂ H₂₃ e₂)
renameExpr-trans Δ₁ Δ₂ Δ₃ H₁₂ H₂₃ (Let e₁ e₂) =
  cong₂ Let (renameExpr-trans Δ₁ Δ₂ Δ₃ H₁₂ H₂₃ e₁) (renameExpr-trans (Keep Δ₁) (Keep Δ₂) (Keep Δ₃) H₁₂ H₂₃ e₂)
renameExpr-trans Δ₁ Δ₂ Δ₃ H₁₂ H₂₃ (Var x) =
  cong Var (renameVar-trans Δ₁ Δ₂ Δ₃ H₁₂ H₂₃ x)

inj₁ : (Δ₁ Δ₂ : Subset Γ) → Expr ⌊ Δ₁ ⌋ σ → Expr ⌊ Δ₁ ∪ Δ₂ ⌋ σ
inj₁ Δ₁ Δ₂ = renameExpr Δ₁ (Δ₁ ∪ Δ₂) (∪sub₁ Δ₁ Δ₂)

inj₂ : (Δ₁ Δ₂ : Subset Γ) → Expr ⌊ Δ₂ ⌋ σ → Expr ⌊ Δ₁ ∪ Δ₂ ⌋ σ
inj₂ Δ₁ Δ₂ = renameExpr Δ₂ (Δ₁ ∪ Δ₂) (∪sub₂ Δ₁ Δ₂)

-- Restricting an environment to some subset of (required) values
prjEnv : (Δ : Subset Γ) → Env Γ → Env ⌊ Δ ⌋
prjEnv Empty Nil = Nil
prjEnv (Drop Δ) (Cons x env) = prjEnv Δ env
prjEnv (Keep Δ) (Cons x env) = Cons x (prjEnv Δ env)

-- More general version
prjEnv' : (Δ₁ Δ₂ : Subset Γ) → .(Δ₁ ⊆ Δ₂) → Env ⌊ Δ₂ ⌋ → Env ⌊ Δ₁ ⌋
prjEnv' Empty Empty prf env = env
prjEnv' (Drop Δ₁) (Drop Δ₂) prf env = prjEnv' Δ₁ Δ₂ prf env
prjEnv' (Drop Δ₁) (Keep Δ₂) prf (Cons x env) = prjEnv' Δ₁ Δ₂ prf env
prjEnv' (Keep Δ₁) (Keep Δ₂) prf (Cons x env) = Cons x (prjEnv' Δ₁ Δ₂ prf env)

prjEnv≡prjEnv' : (Δ : Subset Γ) (env : Env Γ) →
  prjEnv Δ env ≡ prjEnv' Δ (all Γ) (subset-⊆ Γ Δ) (prjEnv (all Γ) env)
prjEnv≡prjEnv' {[]} Empty Nil = refl
prjEnv≡prjEnv' {τ ∷ Γ} (Drop Δ) (Cons x env) = prjEnv≡prjEnv' Δ env
prjEnv≡prjEnv' {τ ∷ Γ} (Keep Δ) (Cons x env) = cong (Cons x) (prjEnv≡prjEnv' Δ env)

-- TODO what is the expected behaviour and use of this?
sub₁ : (Δ₁ Δ₂ : Subset Γ) → Subset ⌊ Δ₁ ∪ Δ₂ ⌋
sub₁ Empty Empty = Empty
sub₁ (Drop Δ₁) (Drop Δ₂) = sub₁ Δ₁ Δ₂
sub₁ (Drop Δ₁) (Keep Δ₂) = Drop (sub₁ Δ₁ Δ₂) -- why not: Drop (sub₁ Δ₁ Δ₂)
sub₁ (Keep Δ₁) (Drop Δ₂) = Keep (sub₁ Δ₁ Δ₂) -- not sure why this is not symmetric
sub₁ (Keep Δ₁) (Keep Δ₂) = Keep (sub₁ Δ₁ Δ₂)

-- TODO finish these? Or use alternative def using ⊆?
prj₁ : ∀ (Δ₁ Δ₂ : Subset Γ) → Env ⌊ Δ₁ ∪ Δ₂ ⌋ → Env ⌊ Δ₁ ⌋
prj₁ Δ₁ Δ₂ = prjEnv' Δ₁ (Δ₁ ∪ Δ₂) (∪sub₁ Δ₁ Δ₂)

prj₂ : (Δ₁ Δ₂ : Subset Γ) → Env ⌊ Δ₁ ∪ Δ₂ ⌋ → Env ⌊ Δ₂ ⌋
prj₂ Δ₁ Δ₂ = prjEnv' Δ₂ (Δ₁ ∪ Δ₂) (∪sub₂ Δ₁ Δ₂)

renameVar-preserves : (Δ₁ Δ₂ : Subset Γ) → .(H : Δ₁ ⊆ Δ₂) → (i : Ref σ ⌊ Δ₁ ⌋) (env : Env ⌊ Δ₂ ⌋) →
  lookup (renameVar Δ₁ Δ₂ H i) env ≡ lookup i (prjEnv' Δ₁ Δ₂ H env)
renameVar-preserves (Drop Δ₁) (Drop Δ₂) H i env = renameVar-preserves Δ₁ Δ₂ H i env
renameVar-preserves (Drop Δ₁) (Keep Δ₂) H i (Cons x env) = renameVar-preserves Δ₁ Δ₂ H i env
renameVar-preserves (Keep Δ₁) (Keep Δ₂) H Top (Cons x env) = refl
renameVar-preserves (Keep Δ₁) (Keep Δ₂) H (Pop i) (Cons x env) = renameVar-preserves Δ₁ Δ₂ H i env

renameExpr-preserves : (Δ₁ Δ₂ : Subset Γ) → .(H : Δ₁ ⊆ Δ₂) → (e : Expr ⌊ Δ₁ ⌋ σ) (env : Env ⌊ Δ₂ ⌋) →
  eval (renameExpr Δ₁ Δ₂ H e) env ≡ eval e (prjEnv' Δ₁ Δ₂ H env)
renameExpr-preserves Δ₁ Δ₂ H (Val x) env = refl
renameExpr-preserves Δ₁ Δ₂ H (Plus e₁ e₂) env =
  cong₂ _+_ (renameExpr-preserves Δ₁ Δ₂ H e₁ env) (renameExpr-preserves Δ₁ Δ₂ H e₂ env)
renameExpr-preserves Δ₁ Δ₂ H (Eq e₁ e₂) env =
  cong₂ _≡ᵇ_ (renameExpr-preserves Δ₁ Δ₂ H e₁ env) (renameExpr-preserves Δ₁ Δ₂ H e₂ env)
renameExpr-preserves Δ₁ Δ₂ H (Let e₁ e₂) env =
  eval (renameExpr (Keep Δ₁) (Keep Δ₂) _ e₂) (Cons (eval (renameExpr Δ₁ Δ₂ _ e₁) env) env)
  ≡⟨ renameExpr-preserves (Keep Δ₁) (Keep Δ₂ ) _ e₂ (Cons (eval (renameExpr Δ₁ Δ₂ H e₁) env) env) ⟩
  eval e₂ (prjEnv' (Keep Δ₁) (Keep Δ₂) _ (Cons (eval (renameExpr Δ₁ Δ₂ _ e₁) env) env))
  ≡⟨ cong (λ x → eval e₂ (Cons x (prjEnv' Δ₁ Δ₂ _ env))) (renameExpr-preserves Δ₁ Δ₂ H e₁ env) ⟩
  eval e₂ (Cons (eval e₁ (prjEnv' Δ₁ Δ₂ _ env)) (prjEnv' Δ₁ Δ₂ _ env))
  ∎
  where
    open Relation.Binary.PropositionalEquality.≡-Reasoning
renameExpr-preserves Δ₁ Δ₂ H (Var x) env = renameVar-preserves Δ₁ Δ₂ H x env
