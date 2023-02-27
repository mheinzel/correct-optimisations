module Core where

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

variable
  Γ : Ctx
  σ τ : U

data Env : Ctx → Set where
  Nil   : Env []
  Cons  : ⟦ σ ⟧ → Env Γ → Env (σ ∷ Γ)

infixr 19 _++ᴱ_

_++ᴱ_ : ∀ {Γ₁ Γ₂} → Env Γ₁ → Env Γ₂ → Env (Γ₁ ++ Γ₂)
Nil ++ᴱ env₂ = env₂
Cons v env₁ ++ᴱ env₂ = Cons v (env₁ ++ᴱ env₂)

data Ref (σ : U) : Ctx → Set where
  Top  : Ref σ (σ ∷ Γ)
  Pop  : Ref σ Γ → Ref σ (τ ∷ Γ)

lookup : Ref σ Γ → Env Γ → ⟦ σ ⟧
lookup Top      (Cons v env)   = v
lookup (Pop i)  (Cons v env)   = lookup i env
