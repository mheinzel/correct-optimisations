module Language.Generic where

open import Data.List using (_∷_ ; [] ; [_])
open import Function using (const)

open import Generic.Syntax hiding (`Let)
open import Data.Environment using (Thinnable)
open import Data.Var using (_─Scoped)

open import Language.Core as Core hiding (⟦_⟧)

data Tag : Set where
  `App  : U → U → Tag
  `Lam  : U → U → Tag
  `Let  : U → U → Tag
  `Val  : U → Tag
  `Plus : Tag

Lang : Desc U
Lang = `σ Tag λ where
  (`App σ τ) → `X [] (σ ⇒ τ) (`X [] σ (`∎ τ))
  (`Lam σ τ) → `X [ σ ] τ (`∎ (σ ⇒ τ))
  (`Let σ τ) → `X [] σ (`X [ σ ] τ (`∎ τ))
  (`Val τ)   → `σ Core.⟦ τ ⟧ λ _ → `∎ τ
  `Plus      → `X [] NAT (`X [] NAT (`∎ NAT))

Value : U ─Scoped
Value τ Γ = Core.⟦ τ ⟧

th^Value : ∀ {τ} → Thinnable (Value τ)
th^Value v = const v
