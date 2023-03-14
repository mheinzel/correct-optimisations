module GenericCoDeBruijn.Lang where

open import Data.List using (List ; _∷_ ; []; _++_)
open import Data.Product as Prod using (_×_; Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality
open import Function using (const; _$_; _∘_)
open import Data.Unit using (⊤; tt)

open import Data.Var using (_─Scoped)
open import Generic.Syntax
open import Stdlib using (∀[_]; _⇒_)

open import OPE using (oz; oi; oe; _ₒ_; _↑_)
open import CoDeBruijn.Core as CoDeBruijn using (_×ᴿ_; pairᴿ; _⊢_; _\\_)

module _ where
  record Kind (I : Set) : Set where
    inductive
    constructor _⇒ᴷ_
    field
      scope : List (Kind I)
      sort : I

  data Desc' (I : Set) : Set₁ where
    Recᴰ : Kind I → Desc' I
    Σᴰ   : (A : Set) → (A → Desc' I) → Desc' I
    Oneᴰ : Desc' I
    _×ᴰ_ : Desc' I → Desc' I → Desc' I
 
  -- TODO: We're using _⊑_ here (as part of ×ᴿ), but the de Bruijn interpretation uses Thinning
  -- Unify?
  ⟦_⟧' : {I : Set} → Desc' I → (I → List (Kind I) → Set) → List (Kind I) → Set
  ⟦ Recᴰ k ⟧' R = Kind.scope k ⊢ R (Kind.sort k) 
  ⟦ Σᴰ S T ⟧' R Γ = Σ[ s ∈ S ] ⟦ T s ⟧' R Γ
  ⟦ Oneᴰ   ⟧' R Γ = Γ ≡ []
  ⟦ S ×ᴰ T ⟧' R = ⟦ S ⟧' R ×ᴿ ⟦ T ⟧' R
  

module _ {I : Set} where
  private
    variable
      i σ : I
      Γ Γ₁ Γ₂ : List I

  -- Not sure if worth it. Avoids unnecessary wrappers (some kind of ⊢-trivial),
  -- but might introduce more cases in generic stuff?
  Scope : I ─Scoped → List I → I ─Scoped
  Scope T []        i = T i
  Scope T Δ@(_ ∷ _) i = Δ ⊢ T i

  ⟦_⟧ : Desc I → (List I → I ─Scoped) → I ─Scoped
  ⟦ `σ A d    ⟧ X i Γ = Σ[ a ∈ A ] (⟦ d a ⟧ X i Γ)
  ⟦ `X Δ j d  ⟧ X i = X Δ j ×ᴿ ⟦ d ⟧ X i
  ⟦ `∎ j      ⟧ X i Γ = i ≡ j × Γ ≡ []

  data Tm (d : Desc I) : I ─Scoped where
    `var  : Tm d i (i ∷ [])
    `con  : ∀[ ⟦ d ⟧ (Scope (Tm d)) i ⇒ Tm d i ]

  ×ᴿ-trivial : {τ : I} {T : List I → Set} → T Γ → (T ×ᴿ λ Γ' → τ ≡ τ × Γ' ≡ []) Γ
  ×ᴿ-trivial t = pairᴿ (t ↑ oi) ((refl , refl) ↑ oe) CoDeBruijn.cover-oi-oe

  ×ᴿ-trivial⁻¹ : {τ τ' : I} {T : List I → Set} → (T ×ᴿ λ Γ' → τ ≡ τ' × Γ' ≡ []) Γ → T Γ × τ ≡ τ'
  ×ᴿ-trivial⁻¹ (pairᴿ (t ↑ θ₁) ((refl , refl) ↑ θ₂) cover)
    with refl ← CoDeBruijn.cover-oi-oe⁻¹ cover =
      t , refl

open import Core hiding (⟦_⟧)
import CoDeBruijn.Lang as CoDeBruijn

data `Lang : Set where
  `App  : U → U → `Lang
  `Lam  : U → U → `Lang
  `Let  : U → U → `Lang
  `Val  : U → `Lang
  `Plus : `Lang

Lang' : Desc' U
Lang' = Σᴰ `Lang λ where
  (`App σ τ) → Recᴰ ([] ⇒ᴷ (σ Core.⇒ τ)) ×ᴰ Recᴰ ([] ⇒ᴷ σ)
  (`Lam σ τ) → Recᴰ ((([] ⇒ᴷ σ) ∷ []) ⇒ᴷ τ)
  (`Let σ τ) → Recᴰ ([] ⇒ᴷ σ) ×ᴰ Recᴰ ((([] ⇒ᴷ σ) ∷ []) ⇒ᴷ τ)
  (`Val τ)   → Σᴰ Core.⟦ τ ⟧ λ x → Oneᴰ
  `Plus      → Recᴰ ([] ⇒ᴷ NAT) ×ᴰ Recᴰ ([] ⇒ᴷ NAT)

Lang : Desc U
Lang = `σ `Lang $ λ where
  (`App σ τ) → `X [] (σ Core.⇒ τ) (`X [] σ (`∎ τ))
  (`Lam σ τ) → `X (σ ∷ []) τ (`∎ (σ Core.⇒ τ))
  (`Let σ τ) → `X [] σ (`X (σ ∷ []) τ (`∎ τ))
  (`Val τ)   → `σ Core.⟦ τ ⟧ λ _ → `∎ τ
  `Plus      → `X [] NAT (`X [] NAT (`∎ NAT))

pattern App e₁ θ₁ e₂ θ₂' θ₂ c' c  =
  `App _ _ , pairᴿ ((oz \\ e₁) ↑ θ₁) (pairᴿ ((oz \\ e₂) ↑ θ₂') (refl ↑ _) c' ↑ θ₂) c

Expr : U ─Scoped
Expr = Tm Lang

into : ∀ {Γ τ} → CoDeBruijn.Expr τ Γ → Expr τ Γ
into CoDeBruijn.Var =
  `var
into (CoDeBruijn.App (pairᴿ (e₁ ↑ θ₁) (e₂ ↑ θ₂) cover)) =
  `con (`App _ _ , pairᴿ (into e₁ ↑ θ₁) (×ᴿ-trivial (into e₂) ↑ θ₂) cover)
into (CoDeBruijn.Lam (ψ \\ e)) =
  `con (`Lam _ _ , ×ᴿ-trivial (ψ \\ into e))
into (CoDeBruijn.Let (pairᴿ (e₁ ↑ θ₁) ((ψ \\ e₂) ↑ θ₂) cover)) =
  `con (`Let _ _ , pairᴿ (into e₁ ↑ θ₁) ((×ᴿ-trivial (ψ \\ into e₂)) ↑ θ₂) cover)
into (CoDeBruijn.Val v) =
  `con (`Val _ , v , refl , refl)
into (CoDeBruijn.Plus (pairᴿ (e₁ ↑ θ₁) (e₂ ↑ θ₂) cover)) =
  `con (`Plus , pairᴿ (into e₁ ↑ θ₁) (×ᴿ-trivial (into e₂) ↑ θ₂) cover)

-- This is a bit annoying to match on.
-- We have two θ₂ and covers, and have to reveal the fact that one of them is trivial (e.g. oi).
from : ∀ {Γ τ} → Expr τ Γ → CoDeBruijn.Expr τ Γ
from `var =
  CoDeBruijn.Var
from (`con (`App σ τ , pairᴿ (e₁ ↑ θ₁) (pairᴿ (e₂ ↑ θ₂') ((refl , refl) ↑ θ₂'') c ↑ θ₂) cover))
  with refl ← CoDeBruijn.cover-oi-oe⁻¹ c =
    CoDeBruijn.App (pairᴿ (from e₁ ↑ θ₁) (from e₂ ↑ θ₂) cover)
from (`con (`Lam σ τ , pairᴿ ((ψ \\ e) ↑ θ₁) ((refl , refl) ↑ θ₂) cover))
  with refl ← CoDeBruijn.cover-oi-oe⁻¹ cover =
    CoDeBruijn.Lam (ψ \\ (from e))
from (`con (`Let σ τ , pairᴿ (e₁ ↑ θ₁) (pairᴿ ((ψ \\ e₂) ↑ θ₂') ((refl , refl) ↑ θ₂'') c ↑ θ₂) cover))
  with refl ← CoDeBruijn.cover-oi-oe⁻¹ c =
    CoDeBruijn.Let (pairᴿ (from e₁ ↑ θ₁) ((ψ \\ from e₂) ↑ θ₂) cover)
from (`con (`Val τ , v , refl , refl)) =
  CoDeBruijn.Val v
from (`con (`Plus , pairᴿ (e₁ ↑ θ₁) (pairᴿ (e₂ ↑ θ₂') ((refl , refl) ↑ θ₂'') c ↑ θ₂) cover))
  with refl ← CoDeBruijn.cover-oi-oe⁻¹ c =
    CoDeBruijn.Plus (pairᴿ (from e₁ ↑ θ₁) (from e₂ ↑ θ₂) cover)
