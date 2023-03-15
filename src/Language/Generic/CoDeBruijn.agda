module Language.Generic.CoDeBruijn where

open import Data.List using (List ; _∷_ ; []; _++_)
open import Data.Product as Prod using (_×_; Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality
open import Function using (const; _$_; _∘_)
open import Data.Unit using (⊤; tt)

open import Stdlib using (∀[_]; _⇒_)
open import Data.Var using (_─Scoped)
open import Data.OPE using (oz; oi; oe; _ₒ_; _↑_)
open import Data.Relevant as Relevant using (_×ᴿ_; pairᴿ; _⊢_; _\\_)
open import Generic.Syntax
open import Generic.CoDeBruijn.Syntax

open import Language.Core hiding (⟦_⟧)
open import Language.Generic
import Language.CoDeBruijn as CoDeBruijn

Expr : U ─Scoped
Expr = Tm Lang

into : ∀ {Γ τ} → CoDeBruijn.Expr τ Γ → Expr τ Γ
into CoDeBruijn.Var =
  `var
into (CoDeBruijn.App (pairᴿ (e₁ ↑ θ₁) (e₂ ↑ θ₂) cover)) =
  `con (`App _ _ , pairᴿ (into e₁ ↑ θ₁) (×ᴿ-trivial (into e₂) ↑ θ₂) cover)
into (CoDeBruijn.Lam (ψ \\ e)) =
  `con (`Lam _ _ , ×ᴿ-trivial (ψ \\ into e))
into (CoDeBruijn.Let (pairᴿ (e₁ ↑ θ₁) ((ψ \\ e₂) ↑ θ₂) cover)) =
  `con (`Let _ _ , pairᴿ (into e₁ ↑ θ₁) ((×ᴿ-trivial (ψ \\ into e₂)) ↑ θ₂) cover)
into (CoDeBruijn.Val v) =
  `con (`Val _ , v , refl , refl)
into (CoDeBruijn.Plus (pairᴿ (e₁ ↑ θ₁) (e₂ ↑ θ₂) cover)) =
  `con (`Plus , pairᴿ (into e₁ ↑ θ₁) (×ᴿ-trivial (into e₂) ↑ θ₂) cover)

-- This is a bit annoying to match on.
-- We have two θ₂ and covers, and have to reveal the fact that one of them is trivial (e.g. oi).
from : ∀ {Γ τ} → Expr τ Γ → CoDeBruijn.Expr τ Γ
from `var =
  CoDeBruijn.Var
from (`con (`App σ τ , pairᴿ (e₁ ↑ θ₁) (pairᴿ (e₂ ↑ θ₂') ((refl , refl) ↑ θ₂'') c ↑ θ₂) cover))
  with refl ← Relevant.cover-oi-oe⁻¹ c =
    CoDeBruijn.App (pairᴿ (from e₁ ↑ θ₁) (from e₂ ↑ θ₂) cover)
from (`con (`Lam σ τ , pairᴿ ((ψ \\ e) ↑ θ₁) ((refl , refl) ↑ θ₂) cover))
  with refl ← Relevant.cover-oi-oe⁻¹ cover =
    CoDeBruijn.Lam (ψ \\ (from e))
from (`con (`Let σ τ , pairᴿ (e₁ ↑ θ₁) (pairᴿ ((ψ \\ e₂) ↑ θ₂') ((refl , refl) ↑ θ₂'') c ↑ θ₂) cover))
  with refl ← Relevant.cover-oi-oe⁻¹ c =
    CoDeBruijn.Let (pairᴿ (from e₁ ↑ θ₁) ((ψ \\ from e₂) ↑ θ₂) cover)
from (`con (`Val τ , v , refl , refl)) =
  CoDeBruijn.Val v
from (`con (`Plus , pairᴿ (e₁ ↑ θ₁) (pairᴿ (e₂ ↑ θ₂') ((refl , refl) ↑ θ₂'') c ↑ θ₂) cover))
  with refl ← Relevant.cover-oi-oe⁻¹ c =
    CoDeBruijn.Plus (pairᴿ (from e₁ ↑ θ₁) (from e₂ ↑ θ₂) cover)
