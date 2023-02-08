{-# OPTIONS --sized-types #-}

module Generic.Lang where

open import Data.Product
open import Data.Nat using (_+_)
open import Data.List using (List ; _∷_ ; [])
open import Function using (_$_; _∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Size using (∞)

open import Generic.Syntax
open import Generic.Semantics
open import Data.Environment
open import Data.Var

open import Core
import DeBruijn.Lang as DeBruijn

data `Lang : Set where
  `App  : U → U → `Lang
  `Lam  : U → U → `Lang
  `Let  : U → U → `Lang
  `Val  : U → `Lang
  `Plus : `Lang

Lang : Desc U
Lang = `σ `Lang $ λ where
  (`App σ τ) → `X [] (σ ⇒ τ) (`X [] σ (`∎ τ))
  (`Lam σ τ) → `X (σ ∷ []) τ (`∎ (σ ⇒ τ))
  (`Let σ τ) → `X [] σ (`X (σ ∷ []) τ (`∎ τ))
  (`Val τ)   → `σ Core.⟦ τ ⟧ λ _ → `∎ τ
  `Plus      → `X [] NAT (`X [] NAT (`∎ NAT))

pattern App  e₁ e₂  = `App _ _ , e₁ , e₂ , refl
pattern Lam  e      = `Lam _ _ , e  , refl
pattern Let  e₁ e₂  = `Let _ _ , e₁ , e₂ , refl
pattern Val  v      = `Val _   , v  , refl
pattern Plus e₁ e₂  = `Plus    , e₁ , e₂ , refl

Expr : U ─Scoped
Expr = Tm Lang ∞

into-Var : ∀ {Γ τ} → Ref τ Γ → Var τ Γ
into-Var Top = z
into-Var (Pop x) = s (into-Var x)

-- Just to check that this is the same as our original language.
into : ∀ {Γ τ} → DeBruijn.Expr Γ τ → Expr τ Γ
into (DeBruijn.Var x)      = `var (into-Var x)
into (DeBruijn.App e₁ e₂)  = `con (App (into e₁) (into e₂))
into (DeBruijn.Lam e)      = `con (Lam (into e))
into (DeBruijn.Let e₁ e₂)  = `con (Let (into e₁) (into e₂))
into (DeBruijn.Val v)      = `con (Val v)
into (DeBruijn.Plus e₁ e₂) = `con (Plus (into e₁) (into e₂))


Value : U ─Scoped
Value τ Γ = Core.⟦ τ ⟧

th^Value : ∀ {τ} → Thinnable (Value τ)
th^Value v = λ _ → v

Eval : Semantics Lang Value Value
Semantics.th^𝓥 Eval = th^Value
Semantics.var Eval = λ v → v
Semantics.alg Eval = λ where
  (App v₁ v₂)  → v₁ v₂
  (Lam e)      → λ v → e identity (ε ∙ v)
  (Let v e)  → e identity (ε ∙ v)
  (Val v)      → v
  (Plus v₁ v₂) → v₁ + v₂

eval : ∀ {Γ Γ' σ s} → (Γ ─Env) Value Γ' → Tm Lang s σ Γ → Value σ Γ'
eval env t = Semantics.semantics Eval env t

DeBruijnExpr : U ─Scoped
DeBruijnExpr τ Γ = DeBruijn.Expr Γ τ  -- grrr

Ref-Var : ∀ {σ Γ} → Var σ Γ → Ref σ Γ
Ref-Var z = Top
Ref-Var (s x) = Pop (Ref-Var x)

-- Could also use Ref instead of Var, but then we'd need th^Ref
From : Semantics Lang Var DeBruijnExpr
Semantics.th^𝓥 From = th^Var
Semantics.var From = DeBruijn.Var ∘ Ref-Var
Semantics.alg From = λ where
  (App e₁ e₂)  → DeBruijn.App e₁ e₂
  (Lam e)      → DeBruijn.Lam (e (pack s) (ε ∙ z))
  (Let e₁ e₂)  → DeBruijn.Let e₁ (e₂ (pack s) (ε ∙ z))
  (Val v)      → DeBruijn.Val v
  (Plus e₁ e₂) → DeBruijn.Plus e₁ e₂

from : ∀ {Γ Γ' σ s} → (Γ ─Env) Var Γ' → Tm Lang s σ Γ → DeBruijn.Expr Γ' σ
from env t = Semantics.semantics From env t
