module Subset where

open import Data.List using (List ; _∷_ ; [])
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong)

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

-- Renamings / weakenings
renameVar : (Δ₁ Δ₂ : Subset Γ) → Δ₁ ⊆ Δ₂ → Ref σ ⌊ Δ₁ ⌋ → Ref σ ⌊ Δ₂ ⌋
renameVar (Drop Δ₁) (Drop Δ₂) H i = renameVar Δ₁ Δ₂ H i
renameVar (Drop Δ₁) (Keep Δ₂) H i = Pop (renameVar Δ₁ Δ₂ H i)
renameVar (Keep Δ₁) (Keep Δ₂) H Top = Top
renameVar (Keep Δ₁) (Keep Δ₂) H (Pop i) = Pop (renameVar Δ₁ Δ₂ H i)

renameExpr : (Δ₁ Δ₂ : Subset Γ) → Δ₁ ⊆ Δ₂ → Expr ⌊ Δ₁ ⌋ σ → Expr ⌊ Δ₂ ⌋ σ
renameExpr Δ₁ Δ₂ H (Val x) = Val x
renameExpr Δ₁ Δ₂ H (Plus e₁ e₂) = Plus (renameExpr Δ₁ Δ₂ H e₁) (renameExpr Δ₁ Δ₂ H e₂)
renameExpr Δ₁ Δ₂ H (Eq e₁ e₂) = Eq (renameExpr Δ₁ Δ₂ H e₁) (renameExpr Δ₁ Δ₂ H e₂)
renameExpr Δ₁ Δ₂ H (Let e₁ e₂) = Let (renameExpr Δ₁ Δ₂ H e₁) (renameExpr (Keep Δ₁) (Keep Δ₂) H e₂)
renameExpr Δ₁ Δ₂ H (Var x) = Var (renameVar Δ₁ Δ₂ H x)

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
prjEnv' : (Δ₁ Δ₂ : Subset Γ) → Δ₁ ⊆ Δ₂ → Env ⌊ Δ₂ ⌋ → Env ⌊ Δ₁ ⌋
prjEnv' Empty Empty prf env = env
prjEnv' (Drop Δ₁) (Drop Δ₂) prf env = prjEnv' Δ₁ Δ₂ prf env
prjEnv' (Drop Δ₁) (Keep Δ₂) prf (Cons x env) = prjEnv' Δ₁ Δ₂ prf env
prjEnv' (Keep Δ₁) (Keep Δ₂) prf (Cons x env) = Cons x (prjEnv' Δ₁ Δ₂ prf env)


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
