module Generic.Conversion where

open import Data.Product using (_,_)
open import Data.List using (List; []; _∷_)
open import Function using (_$_; _∘_)
open import Relation.Binary.PropositionalEquality

open import Data.Relevant as Relevant using (pairᴿ; _,ᴿ_; _\\_; _\\R_)
open import Data.OPE
open import Data.Var using (_─Scoped; Var; z; s)
open import Generic.Syntax
open import Generic.DeBruijn.Syntax as DeBruijn
open import Generic.CoDeBruijn.Syntax as CoDeBruijn

private
  variable
    I : Set
    σ τ : I
    Γ Γ' Δ : List I
    T : I ─Scoped

Var-from-⊑ : (τ ∷ []) ⊑ Γ → Var τ Γ
Var-from-⊑ (θ o') = s (Var-from-⊑ θ)
Var-from-⊑ (θ os) = z

⊑-from-Var : Var τ Γ → (τ ∷ []) ⊑ Γ
⊑-from-Var z = oe os
⊑-from-Var (s k) = (⊑-from-Var k) o'

module Relax where
  relax :
    (d : Desc I) → Γ' ⊑ Γ →
    CoDeBruijn.Tm d τ Γ' →
    DeBruijn.Tm d τ Γ

  relax-Scope :
    (Δ : List I) (d : Desc I) → Γ' ⊑ Γ →
    CoDeBruijn.Scope (CoDeBruijn.Tm d) Δ τ Γ' →
    DeBruijn.Scope (DeBruijn.Tm d) Δ τ Γ

  relax-⟦∙⟧ :
    (d d' : Desc I) → Γ' ⊑ Γ →
    CoDeBruijn.⟦ d ⟧ (CoDeBruijn.Scope (CoDeBruijn.Tm d')) τ Γ' →
    DeBruijn.⟦ d ⟧ (DeBruijn.Scope (DeBruijn.Tm d')) τ Γ

  relax d θ `var = `var (Var-from-⊑ θ)
  relax d θ (`con t) = `con (relax-⟦∙⟧ d d θ t)

  relax-Scope [] d θ t = relax d θ t
  relax-Scope Δ@(_ ∷ _) d θ (ψ \\ t) = relax d (ψ ++⊑ θ) t

  relax-⟦∙⟧ (`σ A k) d' θ (a , t) =
    a , relax-⟦∙⟧ (k a) d' θ t
  relax-⟦∙⟧ (`X Δ j d) d' θ (pairᴿ (t₁ ↑ θ₁) (t₂ ↑ θ₂) cover) =
    relax-Scope Δ d' (θ₁ ₒ θ) t₁ , relax-⟦∙⟧ d d' (θ₂ ₒ θ) t₂
  relax-⟦∙⟧ (`∎ j) d' θ (refl , refl) =
    refl

module Tighten where
  tighten :
    (d : Desc I) →
    DeBruijn.Tm d τ Γ →
    CoDeBruijn.Tm d τ ⇑ Γ

  tighten-Scope :
    (Δ : List I) (d : Desc I) →
    DeBruijn.Scope (DeBruijn.Tm d) Δ τ Γ →
    CoDeBruijn.Scope (CoDeBruijn.Tm d) Δ τ ⇑ Γ

  tighten-⟦∙⟧ :
    (d d' : Desc I) →
    DeBruijn.⟦ d ⟧ (DeBruijn.Scope (DeBruijn.Tm d')) τ Γ →
    CoDeBruijn.⟦ d ⟧ (CoDeBruijn.Scope (CoDeBruijn.Tm d')) τ ⇑ Γ

  tighten d (`var k) = `var ↑ ⊑-from-Var k
  tighten d (`con t) = map⇑ `con (tighten-⟦∙⟧ d d t)

  tighten-Scope [] d t = tighten d t
  tighten-Scope Δ@(_ ∷ _) d t = Δ \\R tighten d t

  tighten-⟦∙⟧ (`σ A k) d' (a , t) = map⇑ (a ,_) (tighten-⟦∙⟧ (k a) d' t)
  tighten-⟦∙⟧ (`X Δ j d) d' (t₁ , t₂) = tighten-Scope Δ d' t₁ ,ᴿ tighten-⟦∙⟧ d d' t₂
  tighten-⟦∙⟧ (`∎ j) d' refl = (refl , refl) ↑ oe
