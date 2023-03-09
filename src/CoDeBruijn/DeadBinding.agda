-- Dead binding elimination,
-- Using co-de-Bruijn representation.
module CoDeBruijn.DeadBinding where

-- TODO: make compile
open import Data.Nat using (_+_)
open import Data.List using (List ; _∷_ ; [])
open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; cong₂ ; sym)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Function using (_∘_)

open import Core
open import CoDeBruijn.Core {U}
open import CoDeBruijn.Lang
open import OPE {U}

private
  variable
    τ : U
    Γ : Ctx

-- Only remove directly dead bindings.
dbe : Expr τ Γ → Expr τ ⇑ Γ
dbe {τ} .{τ ∷ []} Var =
  Var ↑ oz os
dbe (App (pairᴿ (e₁ ↑ ϕ₁) (e₂ ↑ ϕ₂) c)) =
  map⇑ App (thin⇑ ϕ₁ (dbe e₁) ,ᴿ thin⇑ ϕ₂ (dbe e₂))
dbe (Lam {σ} (_\\_ {Γ'} ψ e)) =
  map⇑ (Lam ∘ map⊢ ψ) (Γ' \\R dbe e)
-- NOTE: We check liveness given based on the the variable usage in the input Expr.
-- But dbe e₂ might reveal the variable to be dead even if previously marked live!
dbe (Let (pairᴿ (e₁ ↑ ϕ₁) ((oz o' \\ e₂) ↑ ϕ₂) c)) =
  thin⇑ ϕ₂ (dbe e₂)
dbe (Let (pairᴿ (e₁ ↑ ϕ₁) ((oz os \\ e₂) ↑ ϕ₂) c)) =
  map⇑ Let (thin⇑ ϕ₁ (dbe e₁) ,ᴿ thin⇑ ϕ₂ ((_ ∷ []) \\R dbe e₂))
dbe (Val v) =
  Val v ↑ oz
dbe (Plus (pairᴿ (e₁ ↑ ϕ₁) (e₂ ↑ ϕ₂) c)) =
  map⇑ Plus (thin⇑ ϕ₁ (dbe e₁) ,ᴿ thin⇑ ϕ₂ (dbe e₂))

-- TODO: iterate!
-- TODO: prove semantics-preserving
