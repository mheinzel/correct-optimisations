-- Dead binding elimination,
-- done generically using co-de-Bruijn representation.
module Transformations.Generic.CoDeBruijn.DeadBinding where

-- TODO: trim down imports
open import Data.Bool using (true; false)
open import Data.Nat using (_+_)
open import Data.List using (List ; _∷_ ; [])
open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; cong₂ ; sym; trans)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Function using (_∘_; _$_)

open import Data.OPE
open import Data.Relevant

open import Language.Core hiding (⟦_⟧)
open Language.Core.Env
open Language.Core.Ref
open import Generic.Syntax
open import Generic.CoDeBruijn.Syntax

private
  variable
    I : Set
    σ τ : I
    Γ Δ : List I

-- Only remove directly dead bindings.
dbe : (d : Desc I) → Tm (d `+ Let) τ Γ → Tm (d `+ Let) τ ⇑ Γ
dbe-⟦∙⟧ : (d d' : Desc I) → ⟦ d ⟧ (Scope (Tm (d' `+ Let))) τ Γ → ⟦ d ⟧ (Scope (Tm (d' `+ Let))) τ ⇑ Γ
dbe-Scope : (Δ : List I) (d : Desc I) → Scope (Tm (d `+ Let)) Δ τ Γ → Scope (Tm (d `+ Let)) Δ τ ⇑ Γ
dbe-Let : (d : Desc I) → ⟦ Let ⟧ (Scope (Tm (d `+ Let))) τ Γ → Tm (d `+ Let) τ ⇑ Γ
-- dbe-Let : (d : Desc I) → ⟦ Let ⟧ (Scope (Tm (d `+ Let))) τ Γ → ⟦ Let ⟧ (Scope (Tm (d `+ Let))) τ ⇑ Γ

dbe d `var = `var ↑ oi
dbe d (`con (injˡ t)) = map⇑ (`con ∘ injˡ) (dbe-⟦∙⟧ d d t)
dbe d (`con (injʳ t)) = dbe-Let d t
-- dbe d (`con (injʳ t)) = map⇑ (`con ∘ injʳ) (dbe-Let d t)

dbe-⟦∙⟧ (`σ A d) d' (a , t) =
  map⇑ (a ,_) (dbe-⟦∙⟧ (d a) d' t)
dbe-⟦∙⟧ (`X Δ j d) d' (pairᴿ (t₁ ↑ θ₁) (t₂ ↑ θ₂) c) =
  thin⇑ θ₁ (dbe-Scope Δ d' t₁) ,ᴿ thin⇑ θ₂ (dbe-⟦∙⟧ d d' t₂)
dbe-⟦∙⟧ (`∎ i) d' t =
  t ↑ oi

dbe-Scope [] d t = dbe d t
dbe-Scope Δ@(_ ∷ _) d (_\\_ {Γ'} ψ t) = map⇑ (map⊢ ψ) (Γ' \\ᴿ dbe d t)

dbe-Let d ((σ , τ) , pairᴿ (t₁ ↑ θ₁) (pairᴿ ((oz o' \\ t₂) ↑ θ₂') ((refl , refl) ↑ θ₂'') c ↑ θ₂) cover)
  with refl ← cover-oi-oe⁻¹ c =
    thin⇑ θ₂ (dbe d t₂)
dbe-Let d ((σ , τ) , pairᴿ (t₁ ↑ θ₁) (pairᴿ ((oz os \\ t₂) ↑ θ₂') ((refl , refl) ↑ θ₂'') c ↑ θ₂) cover)
  with refl ← cover-oi-oe⁻¹ c =
    let t'  ↑ θ'    = thin⇑ θ₁ (dbe d t₁) ,ᴿ map⇑ (×ᴿ-trivial {T = (σ ∷ []) ⊢ Tm (d `+ Let) τ}) (thin⇑ θ₂ ((_ ∷ []) \\ᴿ (dbe d t₂))) 
    in
    -- map⇑ (`con ∘ injʳ ∘ ((σ , τ) ,_)) (thin⇑ θ₁ (dbe d t₁) ,ᴿ thin⇑ θ₂ ((_ ∷ []) \\ᴿ dbe d t₂ ))
    `con (false , ((σ , τ) , t')) ↑ θ'
    -- map⇑ (`con ∘ (true ,_)) (thin⇑ θ₁ (dbe d t₁) ,ᴿ thin⇑ θ₂ ((_ ∷ []) \\ᴿ dbe d t₂))

{-
dbe {τ} .{τ ∷ []} Var =
  Var ↑ oz os
dbe (App (pairᴿ (e₁ ↑ ϕ₁) (e₂ ↑ ϕ₂) c)) =
  map⇑ App (thin⇑ ϕ₁ (dbe e₁) ,ᴿ thin⇑ ϕ₂ (dbe e₂))
dbe (Lam {σ} (_\\_ {Γ'} ψ e)) =
  map⇑ (Lam ∘ map⊢ ψ) (Γ' \\ᴿ dbe e)
-- NOTE: We check liveness given based on the the variable usage in the input Expr.
-- But dbe e₂ might reveal the variable to be dead even if previously marked live!
dbe (Let (pairᴿ (e₁ ↑ ϕ₁) ((oz o' \\ e₂) ↑ ϕ₂) c)) =
  thin⇑ ϕ₂ (dbe e₂)
dbe (Let (pairᴿ (e₁ ↑ ϕ₁) ((oz os \\ e₂) ↑ ϕ₂) c)) =
  map⇑ Let (thin⇑ ϕ₁ (dbe e₁) ,ᴿ thin⇑ ϕ₂ ((_ ∷ []) \\ᴿ dbe e₂))
dbe (Val v) =
  Val v ↑ oz
dbe (Plus (pairᴿ (e₁ ↑ ϕ₁) (e₂ ↑ ϕ₂) c)) =
  map⇑ Plus (thin⇑ ϕ₁ (dbe e₁) ,ᴿ thin⇑ ϕ₂ (dbe e₂))
-}
