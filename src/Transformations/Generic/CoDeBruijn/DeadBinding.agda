-- Dead binding elimination,
-- done generically using co-de-Bruijn representation.
module Transformations.Generic.CoDeBruijn.DeadBinding where

open import Data.List using (List ; _∷_ ; [])
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Function using (_∘_)

open import Data.OPE
open import Data.Relevant

open import Generic.Syntax
open import Generic.CoDeBruijn.Syntax

private
  variable
    I : Set
    σ τ : I
    Γ Δ : List I
    d d' : Desc I

-- Only remove directly dead bindings.
dbe : Tm (d `+ `Let) τ Γ → Tm (d `+ `Let) τ ⇑ Γ
dbe-⟦∙⟧ : ⟦ d ⟧ (Scope (Tm (d' `+ `Let))) τ Γ → ⟦ d ⟧ (Scope (Tm (d' `+ `Let))) τ ⇑ Γ
dbe-Scope : (Δ : List I) → Scope (Tm (d `+ `Let)) Δ τ Γ → Scope (Tm (d `+ `Let)) Δ τ ⇑ Γ

dbe `var = `var ↑ oi
dbe (`con (injˡ t)) = map⇑ (`con ∘ injˡ) (dbe-⟦∙⟧ t)
dbe (`con (injʳ t@(a , pairᴿ (t₁ ↑ θ₁) (pairᴿ ((ψ \\ t₂) ↑ _) ((refl , refl) ↑ _) c ↑ θ₂) _)))
  with cover-oi-oe⁻¹ c | ψ
...  | refl | oz o' =
    thin⇑ θ₂ (dbe t₂)
...  | refl | oz os =
    let t' ↑ θ' = thin⇑ θ₁ (dbe t₁) ,ᴿ map⇑ ×ᴿ-trivial (thin⇑ θ₂ ((_ ∷ []) \\ᴿ (dbe t₂))) 
    in `con (injʳ (a , t')) ↑ θ'
    -- This implementation is simpler, but gets rejected by the termination checker:
    -- map⇑ (`con ∘ injʳ) (dbe-⟦∙⟧ {d = `Let} t)
    -- We are forced to basically inline dbe-⟦∙⟧ here.
    -- Otherwise, another option would be to re-use let-?:
    -- mult⇑ (map⇑ dbe (let-?' t))

dbe-⟦∙⟧ {d = `σ A d} (a , t) =
  map⇑ (a ,_) (dbe-⟦∙⟧ t)
dbe-⟦∙⟧ {d = `X Δ j d} (pairᴿ (t₁ ↑ θ₁) (t₂ ↑ θ₂) _) =
  thin⇑ θ₁ (dbe-Scope Δ t₁) ,ᴿ thin⇑ θ₂ (dbe-⟦∙⟧ t₂)
dbe-⟦∙⟧ {d = `∎ i} t =
  t ↑ oi

dbe-Scope [] t = dbe t
dbe-Scope (_ ∷ _) (ψ \\ t) = map⇑ (map⊢ ψ) (_ \\ᴿ dbe t)
