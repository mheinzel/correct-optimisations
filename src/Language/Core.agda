module Language.Core where

open import Data.Nat using (_+_) renaming (ℕ to Nat ; zero to Zero ; suc to Succ)
open import Data.Bool using (Bool)
open import Data.List using (List ; _∷_ ; [] ; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong)

data U : Set where
  _⇒_   : U → U → U
  BOOL  : U
  NAT   : U

⟦_⟧ : U → Set
⟦ σ ⇒ τ ⟧ = ⟦ σ ⟧ → ⟦ τ ⟧
⟦ BOOL ⟧  = Bool
⟦ NAT ⟧   = Nat

Ctx = List U

-- TODO: move to Data.Env, as an alternative to their Environment?
module Env {I : Set} {⟦_⟧ : I → Set} where
  open import Data.Thinning

  private
    variable
      Γ Γ₁ Γ₂ Δ : List I
      σ τ : I

  data Env : List I → Set where
    Nil   : Env []
    Cons  : ⟦ σ ⟧ → Env Γ → Env (σ ∷ Γ)

  project-Env : Δ ⊑ Γ → Env Γ → Env Δ
  project-Env oz     env          = env
  project-Env (os θ) (Cons v env) = Cons v (project-Env θ env)
  project-Env (o' θ) (Cons v env) = project-Env θ env

  law-project-Env-ₒ :
    ∀ {Γ₁ Γ₂ Γ₃} (θ : Γ₁ ⊑ Γ₂) (ϕ : Γ₂ ⊑ Γ₃) (env : Env Γ₃) →
    project-Env (θ ₒ ϕ) env ≡ project-Env θ (project-Env ϕ env)
  law-project-Env-ₒ      θ (o' ϕ) (Cons v env) = law-project-Env-ₒ θ ϕ env
  law-project-Env-ₒ (o' θ) (os ϕ) (Cons v env) = law-project-Env-ₒ θ ϕ env
  law-project-Env-ₒ (os θ) (os ϕ) (Cons v env) = cong (Cons v) (law-project-Env-ₒ θ ϕ env)
  law-project-Env-ₒ oz oz env = refl

  law-project-Env-oi : (env : Env Γ) → project-Env oi env ≡ env
  law-project-Env-oi Nil = refl
  law-project-Env-oi (Cons v env) = cong (Cons v) (law-project-Env-oi env)

  infixr 19 _++ᴱ_

  _++ᴱ_ : Env Γ₁ → Env Γ₂ → Env (Γ₁ ++ Γ₂)
  Nil ++ᴱ env₂ = env₂
  Cons v env₁ ++ᴱ env₂ = Cons v (env₁ ++ᴱ env₂)

-- TODO: replace with Data.Var?
module Ref {I : Set} {⟦_⟧ : I → Set} where
  open import Data.Thinning

  open Env {I} {⟦_⟧}
  private
    variable
      Γ Γ₁ Γ₂ Γ₃ Δ : List I
      σ τ : I

  data Ref (σ : I) : List I → Set where
    Top  : Ref σ (σ ∷ Γ)
    Pop  : Ref σ Γ → Ref σ (τ ∷ Γ)

  lookup : Ref σ Γ → Env Γ → ⟦ σ ⟧
  lookup Top      (Cons v env)   = v
  lookup (Pop i)  (Cons v env)   = lookup i env

  rename-Ref : Δ ⊑ Γ → Ref σ Δ → Ref σ Γ
  rename-Ref (o' θ) x = Pop (rename-Ref θ x)
  rename-Ref (os θ) (Pop x) = Pop (rename-Ref θ x)
  rename-Ref (os θ) Top = Top

  law-rename-Ref-ₒ :
    (e : Ref σ Γ₁) (θ : Γ₁ ⊑ Γ₂) (ϕ : Γ₂ ⊑ Γ₃) →
    rename-Ref (θ ₒ ϕ) e ≡  rename-Ref ϕ (rename-Ref θ e)
  law-rename-Ref-ₒ x       θ      (o' ϕ) = cong Pop (law-rename-Ref-ₒ x θ ϕ)
  law-rename-Ref-ₒ x       (o' θ) (os ϕ) = cong Pop (law-rename-Ref-ₒ x θ ϕ)
  law-rename-Ref-ₒ (Pop x) (os θ) (os ϕ) = cong Pop (law-rename-Ref-ₒ x θ ϕ)
  law-rename-Ref-ₒ Top     (os θ) (os ϕ) = refl
  law-rename-Ref-ₒ ()      oz     oz

  law-lookup-rename-Ref :
    (x : Ref σ Δ) (θ : Δ ⊑ Γ) (env : Env Γ) →
    lookup (rename-Ref θ x) env ≡ lookup x (project-Env θ env)
  law-lookup-rename-Ref x       (o' θ) (Cons v env) = law-lookup-rename-Ref x θ env
  law-lookup-rename-Ref Top     (os θ) (Cons v env) = refl
  law-lookup-rename-Ref (Pop x) (os θ) (Cons v env) = law-lookup-rename-Ref x θ env

  -- Thinnings from a singleton context are isomorphic to Ref.
  o-Ref : Ref τ Γ → (τ ∷ []) ⊑ Γ
  o-Ref Top     = os oe
  o-Ref (Pop x) = o' (o-Ref x)

  law-rename-Ref-o-Ref : (x : Ref τ Γ) → rename-Ref (o-Ref x) Top ≡ x
  law-rename-Ref-o-Ref Top = refl
  law-rename-Ref-o-Ref (Pop x) = cong Pop (law-rename-Ref-o-Ref x)

  ref-o : (τ ∷ []) ⊑ Γ → Ref τ Γ
  ref-o (o' θ) = Pop (ref-o θ)
  ref-o (os θ) = Top

  law-ref-o-Ref : (x : Ref σ Γ) → ref-o (o-Ref x) ≡ x
  law-ref-o-Ref Top = refl
  law-ref-o-Ref (Pop x) = cong Pop (law-ref-o-Ref x)
