module Language.Generic.CoDeBruijn where

open import Data.List using (List ; _∷_ ; []; _++_)
open import Data.Product as Prod using (_×_; Σ-syntax; _,_)
open import Data.Nat using (_+_)
open import Relation.Binary.PropositionalEquality
open import Function using (const; _$_; _∘_)
open import Data.Unit using (⊤; tt)

open import Stdlib using (∀[_]; _⇒_)
open import Data.Var using (_─Scoped)
open import Data.Thinning using (_⊑_; oz; oi; oe; _ₒ_; _++⊑_; _↑_)
open import Data.Relevant as Relevant using (_×ᴿ_; pairᴿ; _⊢_; _\\_)
open import Generic.Syntax hiding (`Let)
open import Generic.CoDeBruijn.Syntax

open import Language.Core as Core hiding (⟦_⟧)
open Core.Env {U} {Core.⟦_⟧}
open import Language.Generic
import Language.CoDeBruijn as CoDeBruijn

private
  variable
    σ τ : U
    Γ Γ' : Ctx

Expr : U ─Scoped
Expr = Tm Lang

-- Evaluation

eval : Expr τ Γ' → Env Γ → Γ' ⊑ Γ → Core.⟦ τ ⟧
eval `var env θ = Core.Ref.lookup (Core.Ref.ref-o θ) env
eval (`con (`App _ _ , pairᴿ (e₁ ↑ θ₁) (pairᴿ (e₂ ↑ θ₂') ((refl , _) ↑ _) _ ↑ θ₂) cover)) env θ =
  eval e₁ env (θ₁ ₒ θ) (eval e₂ env (θ₂' ₒ θ₂ ₒ θ))
eval (`con (`Lam _ _ , pairᴿ ((ψ \\ e₁) ↑ θ₁) ((refl , _) ↑ _) c)) env θ =
  λ v → eval e₁ (Cons v env) (ψ ++⊑  θ₁ ₒ θ )
eval (`con (`Let _ _ , pairᴿ (e₁ ↑ θ₁) (pairᴿ ((ψ \\ e₂) ↑ θ₂') ((refl , _) ↑ _) _ ↑ θ₂) cover)) env θ =
  eval e₂ (Cons (eval e₁ env (θ₁ ₒ θ)) env) (ψ ++⊑ θ₂' ₒ θ₂ ₒ θ)
eval (`con (`Val _ , v , refl , _)) env θ =
  v
eval (`con (`Plus , pairᴿ (e₁ ↑ θ₁) (pairᴿ (e₂ ↑ θ₂') ((refl , _) ↑ _) _ ↑ θ₂) cover)) env θ =
  eval e₁ env (θ₁ ₒ θ) + eval e₂ env (θ₂' ₒ θ₂ ₒ θ)

-- Conversion
-- Just to check that this is the same as our original language.
module _ where
  import Language.CoDeBruijn as CoDeBruijn

  into : CoDeBruijn.Expr τ Γ → Expr τ Γ
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
