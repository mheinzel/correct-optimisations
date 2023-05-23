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

Let? : ⟦ `Let ⟧ (Scope (Tm (d `+ `Let))) τ Γ → Tm (d `+ `Let) τ ⇑ Γ
Let? t@(a , pairᴿ (t₁ ↑ θ₁) (p ↑ θ₂) _)
  with ×ᴿ-trivial⁻¹ p
... | (o' oz \\ t₂) , refl = t₂ ↑ θ₂
... | (os oz \\ t₂) , refl = `con (inr t) ↑ oi

dbe : Tm (d `+ `Let) τ Γ → Tm (d `+ `Let) τ ⇑ Γ
dbe-⟦∙⟧ : ⟦ d ⟧ (Scope (Tm (d' `+ `Let))) τ Γ → ⟦ d ⟧ (Scope (Tm (d' `+ `Let))) τ ⇑ Γ
dbe-Scope : (Δ : List I) → Scope (Tm (d `+ `Let)) Δ τ Γ → Scope (Tm (d `+ `Let)) Δ τ ⇑ Γ

dbe `var = `var ↑ oi
dbe (`con (inl t)) = map⇑ (`con ∘ inl) (dbe-⟦∙⟧ t)
dbe (`con (inr t)) = bind⇑ Let? (dbe-⟦∙⟧ {d = `Let} t)

-- It would be more efficient to first only run DBE on the body,
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
