-- Strong dead binding elimination,
-- done generically using co-de-Bruijn representation.
module Transformations.Generic.CoDeBruijn.DeadBindingStrong where

open import Data.List using (List ; _∷_ ; [])
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Function using (_$_; _∘_)

open import Data.OPE
open import Data.Relevant

open import Generic.Syntax
open import Generic.CoDeBruijn.Syntax

private
  variable
    I : Set
    σ τ : I
    Γ Δ : List I

let-? : (d : Desc I) → (Tm (d `+ Let) σ ⇑ Γ) → ((σ ∷ []) ⊢ Tm (d `+ Let) τ) ⇑ Γ → Tm (d `+ Let) τ ⇑ Γ
let-? d (t₁ ↑ θ₁) (((oz o') \\ t₂) ↑ θ₂) = t₂ ↑ θ₂  -- Binding dead, just keep body.
let-? d (t₁ ↑ θ₁) (((oz os) \\ t₂) ↑ θ₂) =
  let t' ↑ θ' = (t₁ ↑ θ₁) ,ᴿ (×ᴿ-trivial (oz os \\ t₂) ↑ θ₂)
  in `con (injʳ (_ , t')) ↑ θ'

dbe : (d : Desc I) → Tm (d `+ Let) τ Γ → Tm (d `+ Let) τ ⇑ Γ
dbe-⟦∙⟧ : (d d' : Desc I) → ⟦ d ⟧ (Scope (Tm (d' `+ Let))) τ Γ → ⟦ d ⟧ (Scope (Tm (d' `+ Let))) τ ⇑ Γ
dbe-Scope : (Δ : List I) (d : Desc I) → Scope (Tm (d `+ Let)) Δ τ Γ → Scope (Tm (d `+ Let)) Δ τ ⇑ Γ

dbe d `var = `var ↑ oi
dbe d (`con (injˡ t)) = map⇑ (`con ∘ injˡ) (dbe-⟦∙⟧ d d t)
dbe d (`con (injʳ (a , pairᴿ (t₁ ↑ θ₁) (t₀@(pairᴿ ((ψ \\ t₂) ↑ _) ((refl , refl) ↑ _) c) ↑ θ₂) _)))
  with refl ← cover-oi-oe⁻¹ c =
    -- It would be more efficient to first only run DBE on the body,
    -- and only run DBE on the declaration if it turned out to be needed.
    -- Should be possible, but requires some restructuring to appease the termination checker.
    let-? d (thin⇑ θ₁ (dbe d t₁)) (thin⇑ θ₂ (map⇑ (map⊢ ψ) (_ \\ᴿ dbe d t₂)))

dbe-⟦∙⟧ (`σ A d) d' (a , t) =
  map⇑ (a ,_) (dbe-⟦∙⟧ (d a) d' t)
dbe-⟦∙⟧ (`X Δ j d) d' (pairᴿ (t₁ ↑ θ₁) (t₂ ↑ θ₂) c) =
  thin⇑ θ₁ (dbe-Scope Δ d' t₁) ,ᴿ thin⇑ θ₂ (dbe-⟦∙⟧ d d' t₂)
dbe-⟦∙⟧ (`∎ i) d' t =
  t ↑ oi

dbe-Scope [] d t = dbe d t
dbe-Scope (_ ∷ _) d (ψ \\ t) = map⇑ (map⊢ ψ) (_ \\ᴿ dbe d t)
