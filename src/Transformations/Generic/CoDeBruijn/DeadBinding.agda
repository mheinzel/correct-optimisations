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

-- Only remove directly dead bindings.
dbe : (d : Desc I) → Tm (d `+ Let) τ Γ → Tm (d `+ Let) τ ⇑ Γ
dbe-⟦∙⟧ : (d d' : Desc I) → ⟦ d ⟧ (Scope (Tm (d' `+ Let))) τ Γ → ⟦ d ⟧ (Scope (Tm (d' `+ Let))) τ ⇑ Γ
dbe-Scope : (Δ : List I) (d : Desc I) → Scope (Tm (d `+ Let)) Δ τ Γ → Scope (Tm (d `+ Let)) Δ τ ⇑ Γ

dbe d `var = `var ↑ oi
dbe d (`con (injˡ t)) = map⇑ (`con ∘ injˡ) (dbe-⟦∙⟧ d d t)
dbe d (`con (injʳ (a , pairᴿ (t₁ ↑ θ₁) (pairᴿ ((ψ \\ t₂) ↑ _) ((refl , refl) ↑ _) c ↑ θ₂) _)))
  with cover-oi-oe⁻¹ c | ψ
...  | refl | oz o' =
    thin⇑ θ₂ (dbe d t₂)
...  | refl | oz os =
    let t' ↑ θ' = thin⇑ θ₁ (dbe d t₁)
                ,ᴿ map⇑ ×ᴿ-trivial (thin⇑ θ₂ ((_ ∷ []) \\ᴿ (dbe d t₂))) 
    in
    `con (injʳ (a , t')) ↑ θ'

dbe-⟦∙⟧ (`σ A d) d' (a , t) =
  map⇑ (a ,_) (dbe-⟦∙⟧ (d a) d' t)
dbe-⟦∙⟧ (`X Δ j d) d' (pairᴿ (t₁ ↑ θ₁) (t₂ ↑ θ₂) c) =
  thin⇑ θ₁ (dbe-Scope Δ d' t₁) ,ᴿ thin⇑ θ₂ (dbe-⟦∙⟧ d d' t₂)
dbe-⟦∙⟧ (`∎ i) d' t =
  t ↑ oi

dbe-Scope [] d t = dbe d t
dbe-Scope (_ ∷ _) d (ψ \\ t) = map⇑ (map⊢ ψ) (_ \\ᴿ dbe d t)
