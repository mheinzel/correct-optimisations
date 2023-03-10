{-# OPTIONS --allow-unsolved-metas #-}

module GenericCoDeBruijn.Lang where

open import Data.List using (List ; _∷_ ; []; _++_)
open import Data.Product as Prod using (_×_; Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality
open import Function using (const; _$_; _∘_)

open import Data.Var using (_─Scoped)
open import Generic.Syntax
open import Stdlib using (∀[_]; _⇒_)

open import OPE using (_↑_; oz; oi)
open import CoDeBruijn.Core using (_×ᴿ_; pairᴿ; _⊢_; _\\_; cover-oi)

module _ {I : Set} where
  private
    variable
      i σ : I
      Γ Γ₁ Γ₂ : List I
      X Y : List I → I ─Scoped
  -- ⟦_⟧ : Desc I → (List I → I ─Scoped) → I ─Scoped
  -- ⟦ `σ A d    ⟧ X i Γ = Σ[ a ∈ A ] (⟦ d a ⟧ X i Γ)
  -- ⟦ `X Δ j d  ⟧ X i Γ = X Δ j Γ × ⟦ d ⟧ X i Γ
  -- ⟦ `∎ j      ⟧ X i Γ = i ≡ j
  --
  -- data Tm (d : Desc I) : I ─Scoped where
  --   `var  : ∀[ Var i                   ⇒ Tm d i ]
  --   `con  : ∀[ ⟦ d ⟧ (Scope (Tm d)) i  ⇒ Tm d i ]

  Scope : I ─Scoped → List I → I ─Scoped
  Scope T Δ i = Δ ⊢ T i

  -- Does this look right?
  ⟦_⟧ : Desc I → (List I → I ─Scoped) → I ─Scoped
  ⟦ `σ A d    ⟧ X i Γ = Σ[ a ∈ A ] (⟦ d a ⟧ X i Γ)
  ⟦ `X Δ j d  ⟧ X i = X Δ j ×ᴿ ⟦ d ⟧ X i
  ⟦ `∎ j      ⟧ X i Γ = i ≡ j

  -- TODO!
  -- Maybe work it out with an example?
  data Tm (d : Desc I) : I ─Scoped where
    `var  : Tm d i (i ∷ [])
    `con  : ∀[ ⟦ d ⟧ (Scope (Tm d)) i ⇒ Tm d i ]

  xᴿ-trivial : {x : I} {T : List I → Set} → T Γ → (T ×ᴿ const (x ≡ x)) Γ
  xᴿ-trivial t = pairᴿ (t ↑ oi) (refl ↑ oi) cover-oi

  ⊢-trivial : {T : List I → Set} → T Γ → ([] ⊢ T) Γ
  ⊢-trivial t = oz \\ t

open import Core hiding (⟦_⟧)
import CoDeBruijn.Lang as CoDeBruijn

data `Lang : Set where
  `App  : U → U → `Lang
  `Lam  : U → U → `Lang
  -- `Let  : U → U → `Lang
  -- `Val  : U → `Lang
  -- `Plus : `Lang

Lang : Desc U
Lang = `σ `Lang $ λ where
  (`App σ τ) → `X [] (σ Core.⇒ τ) (`X [] σ (`∎ τ))
  (`Lam σ τ) → `X (σ ∷ []) τ (`∎ (σ Core.⇒ τ))

pattern App e₁ θ₁ e₂ θ₂' θ₂ c' c  =
  `App _ _ , pairᴿ ((oz \\ e₁) ↑ θ₁) (pairᴿ ((oz \\ e₂) ↑ θ₂') (refl ↑ _) c' ↑ θ₂) c

Expr : U ─Scoped
Expr = Tm Lang

into : ∀ {Γ τ} → CoDeBruijn.Expr τ Γ → Expr τ Γ
into CoDeBruijn.Var =
  `var
into (CoDeBruijn.App {σ} {τ} (pairᴿ (e₁ ↑ θ₁) (e₂ ↑ θ₂) cover)) =
  `con ((`App σ τ) , (pairᴿ (⊢-trivial (into e₁) ↑ θ₁) (xᴿ-trivial (⊢-trivial (into e₂)) ↑ θ₂) cover))
into (CoDeBruijn.Lam {σ} {τ} (ψ \\ e)) =
  `con (`Lam σ τ , xᴿ-trivial (ψ \\ into e))

into (CoDeBruijn.Let x) = {!!}
into (CoDeBruijn.Val v) = {!!}
into (CoDeBruijn.Plus x) = {!!}

from : ∀ {Γ τ} → Expr τ Γ → CoDeBruijn.Expr τ Γ
from `var =
  CoDeBruijn.Var
-- TODO: this is annoying to match on
-- and we have two θ₂ and covers, which need to be composed? can we force one to oi?
from (`con (`App σ τ , pairᴿ ((oz \\ e₁) ↑ θ₁) (pairᴿ ((oz \\ e₂) ↑ θ₂') (refl ↑ _) c ↑ θ₂) cover)) =
  CoDeBruijn.App {σ} {τ} (pairᴿ {!!} {!!} {!!})
from (`con (`Lam σ τ , snd)) =
  {!!}
{-
HelpE : (List I → I ─Scoped) → I ─Scoped
HelpE X σ Γ =
  `σ `Lang (
  App :
    ∀ {σ τ Γ} →
    (TmE (σ ⇒ τ) ×ᴿ TmE σ) Γ →
    TmE τ Γ
  Lam :
    ∀ {σ τ Γ} →
    ((σ ∷ []) ⊢ TmE τ) Γ →
    TmE (σ ⇒ τ) Γ

data TmE : (σ : U) (Γ : Ctx) → Set where
  Var : ∀ {σ} →
    TmE σ (σ ∷ [])
  Con : ∀ {σ} →
    HelpE ? σ Γ →
    TmE σ Γ
-}
