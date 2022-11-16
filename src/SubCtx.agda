module SubCtx where

open import Data.Nat using (_+_) renaming (ℕ to Nat)
open import Data.List using (List ; _∷_ ; [])
open import Data.Unit
open import Data.Product
open import Data.Empty
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; cong₂)

open import Lang

-- This is needed because our notion of semantical equivalence is "same evaluation result",
-- and values include Agda functions.
-- We might want something different?
postulate
  -- extensionality : {A B : Set} → (f g : A → B) (H : (x : A) → f x ≡ g x) → f ≡ g
  extensionality :
    {S : Set} {T : S -> Set} (f g : (x : S) -> T x) ->
    ((x : S) -> f x ≡ g x) ->
    f ≡ g


-- SubCtxs of our context and operations on them 
data SubCtx : Ctx → Set where
  Empty  : SubCtx []
  Drop   : SubCtx Γ → SubCtx (τ ∷ Γ)
  Keep   : SubCtx Γ → SubCtx (τ ∷ Γ)

variable
  Δ Δ' Δ₁ Δ₂ : SubCtx Γ

⌊_⌋ : SubCtx Γ → Ctx
⌊ Empty ⌋              = []
⌊ Drop Δ ⌋             = ⌊ Δ ⌋
⌊ Keep {Γ} {τ} Δ ⌋     = τ ∷ ⌊ Δ ⌋

∅ : {Γ : Ctx} → SubCtx Γ
∅ {[]} = Empty
∅ {x ∷ Γ} = Drop ∅

all : (Γ : Ctx) → SubCtx Γ
all [] = Empty
all (x ∷ Γ) = Keep (all Γ)

_∪_ : SubCtx Γ → SubCtx Γ → SubCtx Γ
Empty ∪ Empty = Empty
Drop Δ₁ ∪ Drop Δ₂ = Drop (Δ₁ ∪ Δ₂)
Drop Δ₁ ∪ Keep Δ₂ = Keep (Δ₁ ∪ Δ₂)
Keep Δ₁ ∪ Drop Δ₂ = Keep (Δ₁ ∪ Δ₂)
Keep Δ₁ ∪ Keep Δ₂ = Keep (Δ₁ ∪ Δ₂)

sing : (Δ : SubCtx Γ) → Ref τ ⌊ Δ ⌋ → SubCtx Γ
sing (Drop Δ) x       = Drop (sing Δ x)
sing (Keep Δ) Top     = Keep ∅
sing (Keep Δ) (Pop x) = Drop (sing Δ x)

pop : SubCtx (σ ∷ Γ) → SubCtx Γ
pop (Drop Δ) = Δ
pop (Keep Δ) = Δ

-- Relating subsets and environments

_⊆_ : SubCtx Γ → SubCtx Γ → Set
Δ₁ ⊆ Keep Δ₂ = pop Δ₁ ⊆ Δ₂
Empty ⊆ Empty = ⊤
Drop Δ₁ ⊆ Drop Δ₂ = Δ₁ ⊆ Δ₂
Keep Δ₁ ⊆ Drop Δ₂ = ⊥

⊆-refl : (Δ : SubCtx Γ) → Δ ⊆ Δ
⊆-refl Empty = tt
⊆-refl (Drop Δ) = ⊆-refl Δ
⊆-refl (Keep Δ) = ⊆-refl Δ

⊆-trans : (Δ₁ Δ₂ Δ₃ : SubCtx Γ) → (Δ₁ ⊆ Δ₂) → (Δ₂ ⊆ Δ₃) → Δ₁ ⊆ Δ₃
⊆-trans Empty Empty Empty Δ₁⊆Δ₂ Δ₂⊆Δ₃ = tt
⊆-trans (Drop Δ₁) (Drop Δ₂) (Drop Δ₃) Δ₁⊆Δ₂ Δ₂⊆Δ₃ = ⊆-trans Δ₁ Δ₂ Δ₃ Δ₁⊆Δ₂ Δ₂⊆Δ₃
⊆-trans (Drop Δ₁) (Drop Δ₂) (Keep Δ₃) Δ₁⊆Δ₂ Δ₂⊆Δ₃ = ⊆-trans Δ₁ Δ₂ Δ₃ Δ₁⊆Δ₂ Δ₂⊆Δ₃
⊆-trans (Drop Δ₁) (Keep Δ₂) (Keep Δ₃) Δ₁⊆Δ₂ Δ₂⊆Δ₃ = ⊆-trans Δ₁ Δ₂ Δ₃ Δ₁⊆Δ₂ Δ₂⊆Δ₃
⊆-trans (Keep Δ₁) (Keep Δ₂) (Keep Δ₃) Δ₁⊆Δ₂ Δ₂⊆Δ₃ = ⊆-trans Δ₁ Δ₂ Δ₃ Δ₁⊆Δ₂ Δ₂⊆Δ₃

∅⊆ : (Γ : Ctx) → (Δ : SubCtx Γ) → ∅ ⊆ Δ
∅⊆ [] Empty = tt
∅⊆ (x ∷ Γ) (Drop Δ) = ∅⊆ Γ Δ
∅⊆ (x ∷ Γ) (Keep Δ) = ∅⊆ Γ Δ

⊆all : (Γ : Ctx) → (Δ : SubCtx Γ) → Δ ⊆ all Γ
⊆all Γ Empty = tt
⊆all (x ∷ Γ) (Drop Δ) = ⊆all Γ Δ
⊆all (x ∷ Γ) (Keep Δ) = ⊆all Γ Δ

sing⊆ : (Γ : Ctx) (Δ : SubCtx Γ) (x : Ref σ ⌊ Δ ⌋) → sing Δ x ⊆ Δ
sing⊆ [] Empty ()
sing⊆ (τ ∷ Γ) (Drop Δ) x = sing⊆ Γ Δ x
sing⊆ (τ ∷ Γ) (Keep Δ) Top = ∅⊆ Γ Δ
sing⊆ (τ ∷ Γ) (Keep Δ) (Pop x) = sing⊆ Γ Δ x

∪⊆ : (Γ : Ctx) → (Δ₁ Δ₂ Δ : SubCtx Γ) → .(H₁ : Δ₁ ⊆ Δ) → .(H₂ : Δ₂ ⊆ Δ) →
  (Δ₁ ∪ Δ₂) ⊆ Δ
∪⊆ [] Empty Empty Empty H₁ H₂ = tt
∪⊆ (_ ∷ Γ) (Drop Δ₁) (Drop Δ₂) (Drop Δ) H₁ H₂ = ∪⊆ Γ Δ₁ Δ₂ Δ H₁ H₂
∪⊆ (_ ∷ Γ) (Drop Δ₁) (Drop Δ₂) (Keep Δ) H₁ H₂ = ∪⊆ Γ Δ₁ Δ₂ Δ H₁ H₂
∪⊆ (_ ∷ Γ) (Drop Δ₁) (Keep Δ₂) (Keep Δ) H₁ H₂ = ∪⊆ Γ Δ₁ Δ₂ Δ H₁ H₂
∪⊆ (_ ∷ Γ) (Keep Δ₁) (Drop Δ₂) (Keep Δ) H₁ H₂ = ∪⊆ Γ Δ₁ Δ₂ Δ H₁ H₂
∪⊆ (_ ∷ Γ) (Keep Δ₁) (Keep Δ₂) (Keep Δ) H₁ H₂ = ∪⊆ Γ Δ₁ Δ₂ Δ H₁ H₂

⊆∪₁ : (Δ₁ Δ₂ : SubCtx Γ) → Δ₁ ⊆ (Δ₁ ∪ Δ₂)
⊆∪₁ Empty Empty = tt
⊆∪₁ (Drop Δ₁) (Drop Δ₂) = ⊆∪₁ Δ₁ Δ₂
⊆∪₁ (Drop Δ₁) (Keep Δ₂) = ⊆∪₁ Δ₁ Δ₂
⊆∪₁ (Keep Δ₁) (Drop Δ₂) = ⊆∪₁ Δ₁ Δ₂
⊆∪₁ (Keep Δ₁) (Keep Δ₂) = ⊆∪₁ Δ₁ Δ₂

⊆∪₂ : (Δ₁ Δ₂ : SubCtx Γ) → Δ₂ ⊆ (Δ₁ ∪ Δ₂)  
⊆∪₂ Empty Empty = tt
⊆∪₂ (Drop Δ₁) (Drop Δ₂) = ⊆∪₂ Δ₁ Δ₂
⊆∪₂ (Drop Δ₁) (Keep Δ₂) = ⊆∪₂ Δ₁ Δ₂
⊆∪₂ (Keep Δ₁) (Drop Δ₂) = ⊆∪₂ Δ₁ Δ₂
⊆∪₂ (Keep Δ₁) (Keep Δ₂) = ⊆∪₂ Δ₁ Δ₂

-- helper for common case
⊆∪₁-trans : (Δ₁ Δ₂ Δᵤ : SubCtx Γ) → (Δ₁ ∪ Δ₂) ⊆ Δᵤ → Δ₁ ⊆ Δᵤ
⊆∪₁-trans Δ₁ Δ₂ Δᵤ H = ⊆-trans Δ₁ (Δ₁ ∪ Δ₂) Δᵤ (⊆∪₁ Δ₁ Δ₂) H

⊆∪₂-trans : (Δ₁ Δ₂ Δᵤ : SubCtx Γ) → (Δ₁ ∪ Δ₂) ⊆ Δᵤ → Δ₂ ⊆ Δᵤ
⊆∪₂-trans Δ₁ Δ₂ Δᵤ H = ⊆-trans Δ₂ (Δ₁ ∪ Δ₂) Δᵤ (⊆∪₂ Δ₁ Δ₂) H

-- Renamings / weakenings
renameVar : (Δ₁ Δ₂ : SubCtx Γ) → .(Δ₁ ⊆ Δ₂) → Ref σ ⌊ Δ₁ ⌋ → Ref σ ⌊ Δ₂ ⌋
renameVar (Drop Δ₁) (Drop Δ₂) H x = renameVar Δ₁ Δ₂ H x
renameVar (Drop Δ₁) (Keep Δ₂) H x = Pop (renameVar Δ₁ Δ₂ H x)
renameVar (Keep Δ₁) (Keep Δ₂) H Top = Top
renameVar (Keep Δ₁) (Keep Δ₂) H (Pop x) = Pop (renameVar Δ₁ Δ₂ H x)

renameExpr : (Δ₁ Δ₂ : SubCtx Γ) → .(Δ₁ ⊆ Δ₂) → Expr ⌊ Δ₁ ⌋ σ → Expr ⌊ Δ₂ ⌋ σ
renameExpr Δ₁ Δ₂ H (Var x) = Var (renameVar Δ₁ Δ₂ H x)
renameExpr Δ₁ Δ₂ H (App e₁ e₂) = App (renameExpr Δ₁ Δ₂ H e₁) (renameExpr Δ₁ Δ₂ H e₂)
renameExpr Δ₁ Δ₂ H (Lam e) = Lam (renameExpr (Keep Δ₁) (Keep Δ₂) H e)
renameExpr Δ₁ Δ₂ H (Let e₁ e₂) = Let (renameExpr Δ₁ Δ₂ H e₁) (renameExpr (Keep Δ₁) (Keep Δ₂) H e₂)
renameExpr Δ₁ Δ₂ H (Val v) = Val v
renameExpr Δ₁ Δ₂ H (Plus e₁ e₂) = Plus (renameExpr Δ₁ Δ₂ H e₁) (renameExpr Δ₁ Δ₂ H e₂)

injExpr₁ : (Δ₁ Δ₂ : SubCtx Γ) → Expr ⌊ Δ₁ ⌋ σ → Expr ⌊ Δ₁ ∪ Δ₂ ⌋ σ
injExpr₁ Δ₁ Δ₂ = renameExpr Δ₁ (Δ₁ ∪ Δ₂) (⊆∪₁ Δ₁ Δ₂)

injExpr₂ : (Δ₁ Δ₂ : SubCtx Γ) → Expr ⌊ Δ₂ ⌋ σ → Expr ⌊ Δ₁ ∪ Δ₂ ⌋ σ
injExpr₂ Δ₁ Δ₂ = renameExpr Δ₂ (Δ₁ ∪ Δ₂) (⊆∪₂ Δ₁ Δ₂)

-- Restricting an environment to some subset of (required) values
prjEnv : (Δ₁ Δ₂ : SubCtx Γ) → .(Δ₁ ⊆ Δ₂) → Env ⌊ Δ₂ ⌋ → Env ⌊ Δ₁ ⌋
prjEnv Empty Empty prf env = env
prjEnv (Drop Δ₁) (Drop Δ₂) prf env = prjEnv Δ₁ Δ₂ prf env
prjEnv (Drop Δ₁) (Keep Δ₂) prf (Cons v env) = prjEnv Δ₁ Δ₂ prf env
prjEnv (Keep Δ₁) (Keep Δ₂) prf (Cons v env) = Cons v (prjEnv Δ₁ Δ₂ prf env)

prjEnv₁ : (Δ₁ Δ₂ : SubCtx Γ) → Env ⌊ Δ₁ ∪ Δ₂ ⌋ → Env ⌊ Δ₁ ⌋
prjEnv₁ Δ₁ Δ₂ = prjEnv Δ₁ (Δ₁ ∪ Δ₂) (⊆∪₁ Δ₁ Δ₂)

prjEnv₂ : (Δ₁ Δ₂ : SubCtx Γ) → Env ⌊ Δ₁ ∪ Δ₂ ⌋ → Env ⌊ Δ₂ ⌋
prjEnv₂ Δ₁ Δ₂ = prjEnv Δ₂ (Δ₁ ∪ Δ₂) (⊆∪₂ Δ₁ Δ₂)

prjEnv-trans : (Δ₁ Δ₂ Δ₃ : SubCtx Γ) → .(H₁₂ : Δ₁ ⊆ Δ₂) → .(H₂₃ : Δ₂ ⊆ Δ₃) → (env : Env ⌊ Δ₃ ⌋) →
  prjEnv Δ₁ Δ₂ H₁₂ (prjEnv Δ₂ Δ₃ H₂₃ env) ≡ prjEnv Δ₁ Δ₃ (⊆-trans Δ₁ Δ₂ Δ₃ H₁₂ H₂₃) env
prjEnv-trans Empty Empty Empty H₁₂ H₂₃ env = refl
prjEnv-trans (Drop Δ₁) (Drop Δ₂) (Drop Δ₃) H₁₂ H₂₃ env = prjEnv-trans Δ₁ Δ₂ Δ₃ H₁₂ H₂₃ env
prjEnv-trans (Drop Δ₁) (Drop Δ₂) (Keep Δ₃) H₁₂ H₂₃ (Cons v env) = prjEnv-trans Δ₁ Δ₂ Δ₃ H₁₂ H₂₃ env
prjEnv-trans (Drop Δ₁) (Keep Δ₂) (Keep Δ₃) H₁₂ H₂₃ (Cons v env) = prjEnv-trans Δ₁ Δ₂ Δ₃ H₁₂ H₂₃ env
prjEnv-trans (Keep Δ₁) (Keep Δ₂) (Keep Δ₃) H₁₂ H₂₃ (Cons v env) = cong (Cons v) (prjEnv-trans Δ₁ Δ₂ Δ₃ H₁₂ H₂₃ env)

-- Properties of renamings
renameVar-id : (Δ : SubCtx Γ) (x : Ref σ ⌊ Δ ⌋) → renameVar Δ Δ (⊆-refl Δ) x ≡ x
renameVar-id (Drop Δ) x = renameVar-id Δ x
renameVar-id (Keep Δ) Top = refl
renameVar-id (Keep Δ) (Pop x) = cong Pop (renameVar-id Δ x)

renameExpr-id : (Δ : SubCtx Γ) (e : Expr ⌊ Δ ⌋ σ) → renameExpr Δ Δ (⊆-refl Δ) e ≡ e
renameExpr-id Δ (Var x) = cong Var (renameVar-id Δ x)
renameExpr-id Δ (Lam e) = cong Lam (renameExpr-id (Keep Δ) e)
renameExpr-id Δ (App e₁ e₂) = cong₂ App (renameExpr-id Δ e₁) (renameExpr-id Δ e₂)
renameExpr-id Δ (Let e₁ e₂) = cong₂ Let (renameExpr-id Δ e₁) (renameExpr-id (Keep Δ) e₂)
renameExpr-id Δ (Val v) = refl
renameExpr-id Δ (Plus e₁ e₂) = cong₂ Plus (renameExpr-id Δ e₁) (renameExpr-id Δ e₂)

renameVar-trans : (Δ₁ Δ₂ Δ₃ : SubCtx Γ) → .(H₁₂ : Δ₁ ⊆ Δ₂) → .(H₂₃ : Δ₂ ⊆ Δ₃) → (x : Ref σ ⌊ Δ₁ ⌋) →
  renameVar Δ₂ Δ₃ H₂₃ (renameVar Δ₁ Δ₂ H₁₂ x) ≡ renameVar Δ₁ Δ₃ (⊆-trans Δ₁ Δ₂ Δ₃ H₁₂ H₂₃) x
renameVar-trans (Drop Δ₁) (Drop Δ₂) (Drop Δ₃) H₁₂ H₂₃ x = renameVar-trans Δ₁ Δ₂ Δ₃ H₁₂ H₂₃ x
renameVar-trans (Drop Δ₁) (Drop Δ₂) (Keep Δ₃) H₁₂ H₂₃ x = cong Pop (renameVar-trans Δ₁ Δ₂ Δ₃ H₁₂ H₂₃ x)
renameVar-trans (Drop Δ₁) (Keep Δ₂) (Keep Δ₃) H₁₂ H₂₃ x = cong Pop (renameVar-trans Δ₁ Δ₂ Δ₃ H₁₂ H₂₃ x)
renameVar-trans (Keep Δ₁) (Keep Δ₂) (Keep Δ₃) H₁₂ H₂₃ Top = refl
renameVar-trans (Keep Δ₁) (Keep Δ₂) (Keep Δ₃) H₁₂ H₂₃ (Pop x) = cong Pop (renameVar-trans Δ₁ Δ₂ Δ₃ H₁₂ H₂₃ x)

renameExpr-trans : (Δ₁ Δ₂ Δ₃ : SubCtx Γ) → .(H₁₂ : Δ₁ ⊆ Δ₂) → .(H₂₃ : Δ₂ ⊆ Δ₃) → (e : Expr ⌊ Δ₁ ⌋ σ) →
  renameExpr Δ₂ Δ₃ H₂₃ (renameExpr Δ₁ Δ₂ H₁₂ e) ≡ renameExpr Δ₁ Δ₃ (⊆-trans Δ₁ Δ₂ Δ₃ H₁₂ H₂₃) e
renameExpr-trans Δ₁ Δ₂ Δ₃ H₁₂ H₂₃ (Var x) =
  cong Var (renameVar-trans Δ₁ Δ₂ Δ₃ H₁₂ H₂₃ x)
renameExpr-trans Δ₁ Δ₂ Δ₃ H₁₂ H₂₃ (App e₁ e₂) =
  cong₂ App (renameExpr-trans Δ₁ Δ₂ Δ₃ H₁₂ H₂₃ e₁) (renameExpr-trans Δ₁ Δ₂ Δ₃ H₁₂ H₂₃ e₂)
renameExpr-trans Δ₁ Δ₂ Δ₃ H₁₂ H₂₃ (Lam e) =
  cong Lam (renameExpr-trans (Keep Δ₁) (Keep Δ₂) (Keep Δ₃) H₁₂ H₂₃ e)
renameExpr-trans Δ₁ Δ₂ Δ₃ H₁₂ H₂₃ (Let e₁ e₂) =
  cong₂ Let (renameExpr-trans Δ₁ Δ₂ Δ₃ H₁₂ H₂₃ e₁) (renameExpr-trans (Keep Δ₁) (Keep Δ₂) (Keep Δ₃) H₁₂ H₂₃ e₂)
renameExpr-trans Δ₁ Δ₂ Δ₃ H₁₂ H₂₃ (Val v) =
  refl
renameExpr-trans Δ₁ Δ₂ Δ₃ H₁₂ H₂₃ (Plus e₁ e₂) =
  cong₂ Plus (renameExpr-trans Δ₁ Δ₂ Δ₃ H₁₂ H₂₃ e₁) (renameExpr-trans Δ₁ Δ₂ Δ₃ H₁₂ H₂₃ e₂)

renameVar-preserves : (Δ₁ Δ₂ : SubCtx Γ) → .(H : Δ₁ ⊆ Δ₂) → (x : Ref σ ⌊ Δ₁ ⌋) (env : Env ⌊ Δ₂ ⌋) →
  lookup (renameVar Δ₁ Δ₂ H x) env ≡ lookup x (prjEnv Δ₁ Δ₂ H env)
renameVar-preserves (Drop Δ₁) (Drop Δ₂) H x env = renameVar-preserves Δ₁ Δ₂ H x env
renameVar-preserves (Drop Δ₁) (Keep Δ₂) H x (Cons v env) = renameVar-preserves Δ₁ Δ₂ H x env
renameVar-preserves (Keep Δ₁) (Keep Δ₂) H Top (Cons v env) = refl
renameVar-preserves (Keep Δ₁) (Keep Δ₂) H (Pop x) (Cons v env) = renameVar-preserves Δ₁ Δ₂ H x env

renameExpr-preserves : (Δ₁ Δ₂ : SubCtx Γ) → .(H : Δ₁ ⊆ Δ₂) → (e : Expr ⌊ Δ₁ ⌋ σ) (env : Env ⌊ Δ₂ ⌋) →
  eval (renameExpr Δ₁ Δ₂ H e) env ≡ eval e (prjEnv Δ₁ Δ₂ H env)
renameExpr-preserves Δ₁ Δ₂ H (Var x) env = renameVar-preserves Δ₁ Δ₂ H x env
renameExpr-preserves Δ₁ Δ₂ H (App e₁ e₂) env =
  cong₂ (λ f x → f x) (renameExpr-preserves Δ₁ Δ₂ H e₁ env) (renameExpr-preserves Δ₁ Δ₂ H e₂ env)
renameExpr-preserves Δ₁ Δ₂ H (Lam e) env =
  extensionality
    (λ x → eval (renameExpr (Keep Δ₁) (Keep Δ₂) H e) (Cons x env))
    (λ x → eval e (Cons x (prjEnv Δ₁ Δ₂ H env)))
    λ x →
      renameExpr-preserves (Keep Δ₁) (Keep Δ₂) H e (Cons x env)
renameExpr-preserves Δ₁ Δ₂ H (Let e₁ e₂) env =
    eval (renameExpr (Keep Δ₁) (Keep Δ₂) _ e₂) (Cons (eval (renameExpr Δ₁ Δ₂ _ e₁) env) env)
  ≡⟨ renameExpr-preserves (Keep Δ₁) (Keep Δ₂ ) _ e₂ (Cons (eval (renameExpr Δ₁ Δ₂ H e₁) env) env) ⟩
    eval e₂ (prjEnv (Keep Δ₁) (Keep Δ₂) _ (Cons (eval (renameExpr Δ₁ Δ₂ _ e₁) env) env))
  ≡⟨ cong (λ v → eval e₂ (Cons v (prjEnv Δ₁ Δ₂ _ env))) (renameExpr-preserves Δ₁ Δ₂ H e₁ env) ⟩
    eval e₂ (Cons (eval e₁ (prjEnv Δ₁ Δ₂ _ env)) (prjEnv Δ₁ Δ₂ _ env))
  ∎
  where
    open Relation.Binary.PropositionalEquality.≡-Reasoning
renameExpr-preserves Δ₁ Δ₂ H (Val v) env = refl
renameExpr-preserves Δ₁ Δ₂ H (Plus e₁ e₂) env =
  cong₂ _+_ (renameExpr-preserves Δ₁ Δ₂ H e₁ env) (renameExpr-preserves Δ₁ Δ₂ H e₂ env)
