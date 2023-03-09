module GenericCoDeBruijn.Lang where

open import Data.List using (List ; _∷_ ; []; _++_)
open import Data.Product as Prod using (_×_; Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality

open import Data.Var using (_─Scoped)
open import Generic.Syntax hiding (⟦_⟧; Tm)  -- TODO: `hiding` clause should not be needed later
open import Stdlib using (∀[_])

open import CoDeBruijn.Core using (_×ᴿ_)

module _ {I : Set} where
  private
    variable
      i σ : I
      Γ₁ Γ₂ : List I
      X Y : List I → I ─Scoped
  -- ⟦_⟧ : Desc I → (List I → I ─Scoped) → I ─Scoped
  -- ⟦ `σ A d    ⟧ X i Γ = Σ[ a ∈ A ] (⟦ d a ⟧ X i Γ)
  -- ⟦ `X Δ j d  ⟧ X i Γ = X Δ j Γ × ⟦ d ⟧ X i Γ
  -- ⟦ `∎ j      ⟧ X i Γ = i ≡ j
  --
  -- data Tm (d : Desc I) : I ─Scoped where
  --   `var  : ∀[ Var i                   ⇒ Tm d i ]
  --   `con  : ∀[ ⟦ d ⟧ (Scope (Tm d)) i  ⇒ Tm d i ]

  -- Does this look right?
  ⟦_⟧ : Desc I → (List I → I ─Scoped) → I ─Scoped
  ⟦ `σ A d    ⟧ X i Γ = Σ[ a ∈ A ] (⟦ d a ⟧ X i Γ)
  ⟦ `X Δ j d  ⟧ X i = X Δ j ×ᴿ ⟦ d ⟧ X i
  ⟦ `∎ j      ⟧ X i Γ = i ≡ j

  -- TODO!
  -- Maybe work it out with an example?
  data Tm (d : Desc I) : I ─Scoped where
    -- `var  : ∀[ Var i                   ⇒ Tm d i ]
    -- `con  : ∀[ ⟦ d ⟧ (Scope (Tm d)) i  ⇒ Tm d i ]

open import Function using (_$_)
open import Core

data `Lang : Set where
  `App  : U → U → `Lang
  `Lam  : U → U → `Lang
  `Let  : U → U → `Lang
  `Val  : U → `Lang
  `Plus : `Lang

Lang : Desc U
Lang = `σ `Lang $ λ where
  (`App σ τ) → `X [] (σ ⇒ τ) (`X [] σ (`∎ τ))
  (`Lam σ τ) → `X (σ ∷ []) τ (`∎ (σ ⇒ τ))
  (`Let σ τ) → `X [] σ (`X (σ ∷ []) τ (`∎ τ))
  (`Val τ)   → `σ Core.⟦ τ ⟧ λ _ → `∎ τ
  `Plus      → `X [] NAT (`X [] NAT (`∎ NAT))
