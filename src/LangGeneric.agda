{-# OPTIONS --sized-types #-}

module LangGeneric where

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
open import Lang using (U; _⇒_; NAT; ⟦_⟧; Ctx)
import Lang

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
  (`Val τ)   → `σ Lang.⟦ τ ⟧ λ _ → `∎ τ
  `Plus      → `X [] NAT (`X [] NAT (`∎ NAT))

pattern App  e₁ e₂  = `App _ _ , e₁ , e₂ , refl
pattern Lam  e      = `Lam _ _ , e  , refl
pattern Let  e₁ e₂  = `Let _ _ , e₁ , e₂ , refl
pattern Val  v      = `Val _   , v  , refl
pattern Plus e₁ e₂  = `Plus    , e₁ , e₂ , refl

Expr : U ─Scoped
Expr = Tm Lang ∞

into-Var : ∀ {Γ τ} → Lang.Ref τ Γ → Var τ Γ
into-Var Lang.Top = z
into-Var (Lang.Pop x) = s (into-Var x)

-- Just to check that this is the same as our original language.
into : ∀ {Γ τ} → Lang.Expr Γ τ → Expr τ Γ
into (Lang.Var x)      = `var (into-Var x)
into (Lang.App e₁ e₂)  = `con (App (into e₁) (into e₂))
into (Lang.Lam e)      = `con (Lam (into e))
into (Lang.Let e₁ e₂)  = `con (Let (into e₁) (into e₂))
into (Lang.Val v)      = `con (Val v)
into (Lang.Plus e₁ e₂) = `con (Plus (into e₁) (into e₂))


Value : U ─Scoped
Value τ Γ = Lang.⟦ τ ⟧

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

LangExpr : U ─Scoped
LangExpr τ Γ = Lang.Expr Γ τ  -- grrr

Ref-Var : ∀ {σ Γ} → Var σ Γ → Lang.Ref σ Γ
Ref-Var z = Lang.Top
Ref-Var (s x) = Lang.Pop (Ref-Var x)

-- Could also use Ref instead of Var, but then we'd need th^Ref
From : Semantics Lang Var LangExpr
Semantics.th^𝓥 From = th^Var
Semantics.var From = Lang.Var ∘ Ref-Var
Semantics.alg From = λ where
  (App e₁ e₂)  → Lang.App e₁ e₂
  (Lam e)      → Lang.Lam (e (pack s) (ε ∙ z))
  (Let e₁ e₂)  → Lang.Let e₁ (e₂ (pack s) (ε ∙ z))
  (Val v)      → Lang.Val v
  (Plus e₁ e₂) → Lang.Plus e₁ e₂

from : ∀ {Γ Γ' σ s} → (Γ ─Env) Var Γ' → Tm Lang s σ Γ → Lang.Expr Γ' σ
from env t = Semantics.semantics From env t
