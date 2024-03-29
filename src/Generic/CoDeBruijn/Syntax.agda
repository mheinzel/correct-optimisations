module Generic.CoDeBruijn.Syntax where

open import Data.Bool using (true; false)
open import Data.List using (List ; _∷_ ; [])
open import Data.Product as Prod using (_×_; Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality
open import Function using (_∋_)

open import Data.Var using (_─Scoped)
open import Data.Thinning using (oi; oe; _↑_)
open import Data.Relevant as Relevant using (_×ᴿ_; pairᴿ; _⊢_; _\\_)
open import Generic.Syntax

private
  variable
    I : Set
    i σ τ τ' : I
    Γ Γ₁ Γ₂ Δ : List I

-- Interpretation of Descriptions

⟦_⟧ : Desc I → (List I → I ─Scoped) → I ─Scoped
⟦ `σ A d    ⟧ X i Γ = Σ[ a ∈ A ] (⟦ d a ⟧ X i Γ)
⟦ `X Δ j d  ⟧ X i = X Δ j ×ᴿ ⟦ d ⟧ X i
⟦ `∎ j      ⟧ X i Γ = i ≡ j × Γ ≡ []

-- Syntaxes

-- Not sure if worth it. Avoids unnecessary wrappers (some kind of ⊢-trivial),
-- but might introduce more cases in generic stuff?
Scope : I ─Scoped → List I → I ─Scoped
Scope T []        i = T i
Scope T Δ@(_ ∷ _) i = Δ ⊢ T i

data Tm (d : Desc I) : I ─Scoped where
  `var  : Tm d i (i ∷ [])
  `con  : ⟦ d ⟧ (Scope (Tm d)) i Γ → Tm d i Γ

-- Convenience function for the construction of ⟦ `X Δ σ (`∎ τ) ⟧ ,
-- which as a product requires a (trivial) Cover.
×ᴿ-trivial : {T : List I → Set} → T Γ → (T ×ᴿ λ Γ' → τ ≡ τ × Γ' ≡ []) Γ
×ᴿ-trivial t = pairᴿ (t ↑ oi) ((refl , refl) ↑ oe) Relevant.cover-oi-oe

-- Just to show it really matches that type.
×ᴿ-trivial' : {X : List I → I ─Scoped} → X Δ σ Γ → ⟦ `X Δ σ (`∎ τ) ⟧ X τ Γ
×ᴿ-trivial' t = ×ᴿ-trivial t


×ᴿ-trivial⁻¹ : {T : List I → Set} → (T ×ᴿ λ Γ' → τ ≡ τ' × Γ' ≡ []) Γ → T Γ × τ ≡ τ'
×ᴿ-trivial⁻¹ (pairᴿ (t ↑ θ₁) ((refl , refl) ↑ θ₂) cover)
  with refl ← Relevant.cover-oi-oe⁻¹ cover =
    t , refl

-- Just to show it really matches that type.
×ᴿ-trivial⁻¹' : {X : List I → I ─Scoped} → ⟦ `X Δ σ (`∎ τ') ⟧ X τ Γ → X Δ σ Γ × τ ≡ τ'
×ᴿ-trivial⁻¹' p = ×ᴿ-trivial⁻¹ p


module _ {I i Γ} {d : Desc I} where

  `con-inj : ∀ {t u} → (Tm d i Γ ∋ `con t) ≡ `con u → t ≡ u
  `con-inj refl = refl

-- Closed terms
module _ {I : Set} where

  TM : Desc I → I → Set
  TM d i = Tm d i []


-- Descriptions are closed under sums

module _ {I : Set} {d e : Desc I} {X : List I → I ─Scoped}
         {A : Set} {i : I} {Γ : List I} where

 pattern inl t = true , t
 pattern inr t = false , t
 
 case : (⟦ d ⟧ X i Γ → A) → (⟦ e ⟧ X i Γ → A) → (⟦ d `+ e  ⟧ X i Γ → A)
 case l r (inl t) = l t
 case l r (inr t) = r t
