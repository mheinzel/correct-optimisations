module Language.Core where

open import Data.Nat using (_+_) renaming (ℕ to Nat ; zero to Zero ; suc to Succ)
open import Data.Bool using (Bool)
open import Data.List using (List ; _∷_ ; [] ; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

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
  open import Data.OPE

  private
    variable
      Γ Γ₁ Γ₂ : List I
      σ τ : I

  data Env : List I → Set where
    Nil   : Env []
    Cons  : ⟦ σ ⟧ → Env Γ → Env (σ ∷ Γ)

  project-Env : ∀ {Γ₁ Γ₂} → Γ₁ ⊑ Γ₂ → Env Γ₂ → Env Γ₁
  project-Env oz     env          = env
  project-Env (θ os) (Cons v env) = Cons v (project-Env θ env)
  project-Env (θ o') (Cons v env) = project-Env θ env

  law-project-Env-ₒ :
    ∀ {Γ₁ Γ₂ Γ₃} (θ : Γ₁ ⊑ Γ₂) (ϕ : Γ₂ ⊑ Γ₃) (env : Env Γ₃) →
    project-Env (θ ₒ ϕ) env ≡ project-Env θ (project-Env ϕ env)
  law-project-Env-ₒ θ (ϕ o') (Cons v env) = law-project-Env-ₒ θ ϕ env
  law-project-Env-ₒ (θ o') (ϕ os) (Cons v env) = law-project-Env-ₒ θ ϕ env
  law-project-Env-ₒ (θ os) (ϕ os) (Cons v env) = cong (Cons v) (law-project-Env-ₒ θ ϕ env)
  law-project-Env-ₒ oz oz env = refl

  law-project-Env-oi : (env : Env Γ) → project-Env oi env ≡ env
  law-project-Env-oi Nil = refl
  law-project-Env-oi (Cons x env) = cong (Cons x) (law-project-Env-oi env)

  infixr 19 _++ᴱ_

  _++ᴱ_ : Env Γ₁ → Env Γ₂ → Env (Γ₁ ++ Γ₂)
  Nil ++ᴱ env₂ = env₂
  Cons v env₁ ++ᴱ env₂ = Cons v (env₁ ++ᴱ env₂)

-- TODO: replace with Data.Var?
module Ref {I : Set} {⟦_⟧ : I → Set} where
  open import Data.OPE

  open Env {I} {⟦_⟧}
  private
    variable
      Γ Γ₁ Γ₂ : List I
      σ τ : I

  data Ref (σ : I) : List I → Set where
    Top  : Ref σ (σ ∷ Γ)
    Pop  : Ref σ Γ → Ref σ (τ ∷ Γ)

  lookup : Ref σ Γ → Env Γ → ⟦ σ ⟧
  lookup Top      (Cons v env)   = v
  lookup (Pop i)  (Cons v env)   = lookup i env

  -- OPEs from a singleton context are isomorphic to Ref.
  o-Ref : Ref τ Γ → (τ ∷ []) ⊑ Γ
  o-Ref Top     = oe os
  o-Ref (Pop x) = (o-Ref x) o'

  ref-o : (τ ∷ []) ⊑ Γ → Ref τ Γ
  ref-o (θ o') = Pop (ref-o θ)
  ref-o (θ os) = Top

  ref-o-Ref≡id : (x : Ref σ Γ) → ref-o (o-Ref x) ≡ x
  ref-o-Ref≡id Top = refl
  ref-o-Ref≡id (Pop x) = cong Pop (ref-o-Ref≡id x)
