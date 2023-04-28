-- Strong dead binding elimination,
-- done generically using co-de-Bruijn representation.
module Transformations.Generic.CoDeBruijn.DeadBindingStrong where

open import Data.List using (List ; _∷_ ; [])
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Function using (_$_; _∘_)

open import Data.Thinning
open import Data.Relevant

open import Generic.Syntax
open import Generic.CoDeBruijn.Syntax

private
  variable
    I : Set
    σ τ : I
    Γ Δ : List I
    d d' : Desc I

let-? : Tm (d `+ `Let) σ ⇑ Γ → ((σ ∷ []) ⊢ Tm (d `+ `Let) τ) ⇑ Γ → Tm (d `+ `Let) τ ⇑ Γ
let-? (t₁ ↑ θ₁) ((o' oz \\ t₂) ↑ θ₂) = t₂ ↑ θ₂  -- Binding dead, just keep body.
let-? (t₁ ↑ θ₁) ((os oz \\ t₂) ↑ θ₂) =          -- Assemble constructor.
  let t' ↑ θ' = (t₁ ↑ θ₁) ,ᴿ (×ᴿ-trivial (os oz \\ t₂) ↑ θ₂)
  in `con (injʳ (_ , t')) ↑ θ'

{-
let-?' : ⟦ `Let ⟧ (Scope (Tm (d `+ `Let))) τ Γ → Tm (d `+ `Let) τ ⇑ Γ
let-?' t@(a , pairᴿ (t₁ ↑ θ₁) (pairᴿ ((ψ \\ t₂) ↑ _) ((refl , refl) ↑ _) c ↑ θ₂) _)
  with cover-oi-oe⁻¹ c | ψ
...  | refl | o' oz =
  t₂ ↑ θ₂
...  | refl | os oz =
  `con (injʳ t) ↑ oi
-}

dbe : Tm (d `+ `Let) τ Γ → Tm (d `+ `Let) τ ⇑ Γ
dbe-⟦∙⟧ : ⟦ d ⟧ (Scope (Tm (d' `+ `Let))) τ Γ → ⟦ d ⟧ (Scope (Tm (d' `+ `Let))) τ ⇑ Γ
dbe-Scope : (Δ : List I) → Scope (Tm (d `+ `Let)) Δ τ Γ → Scope (Tm (d `+ `Let)) Δ τ ⇑ Γ

dbe `var = `var ↑ oi
dbe (`con (injˡ t)) = map⇑ (`con ∘ injˡ) (dbe-⟦∙⟧ t)
dbe (`con (injʳ t@(a , pairᴿ (t₁ ↑ θ₁) (pairᴿ ((ψ \\ t₂) ↑ _) ((refl , refl) ↑ _) c ↑ θ₂) _)))
  with refl ← cover-oi-oe⁻¹ c =
    let-? (thin⇑ θ₁ (dbe t₁)) (thin⇑ θ₂ (map⇑ (map⊢ ψ) (_ \\ᴿ dbe t₂)))
    -- This implementation is simpler, but gets rejected by the termination checker:
    -- mult⇑ (map⇑ let-?' (dbe-⟦∙⟧ {d = `Let} t))
    --
    -- Also, it would be more efficient to first only run DBE on the body,
    -- and only run DBE on the declaration if it turned out to be needed.
    -- This however requires some restructuring to appease the termination checker.

dbe-⟦∙⟧ {d = `σ A d} (a , t) =
  map⇑ (a ,_) (dbe-⟦∙⟧ t)
dbe-⟦∙⟧ {d = `X Δ j d} (pairᴿ (t₁ ↑ θ₁) (t₂ ↑ θ₂) c) =
  thin⇑ θ₁ (dbe-Scope Δ t₁) ,ᴿ thin⇑ θ₂ (dbe-⟦∙⟧ t₂)
dbe-⟦∙⟧ {d = `∎ i} t =
  t ↑ oi

dbe-Scope [] t = dbe t
dbe-Scope (_ ∷ _) (ψ \\ t) = map⇑ (map⊢ ψ) (_ \\ᴿ dbe t)
