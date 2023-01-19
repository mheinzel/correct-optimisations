-- Let Floating (inwards)
module LetInward where

open import Data.Nat using (_+_)
open import Data.List using (List ; _∷_ ; [])
open import Data.Unit
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; cong₂ ; sym)
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import Lang
open import SubCtx
open import Live
-- open import LiveFlex

-- Push the let-binding inwards as far as possible without
-- - duplicating it
-- - pushing it into a lambda

{- Trying it based on LiveExpr
-- TODO: Can we assume that the binding must be live? (issues with Var case)
-- TODO: This would be easier with a less restrictive version of LiveExpr
-- IDEA: annotations are updated with each transformation, changes bubble up
-- IDEA/HACK: Also push binding into branches where they're not used, but don't recurse.
--            Then they can be removed again in a separate pass.
push-let : LiveExpr Δ Δ₁ σ → LiveExpr {σ ∷ Γ} (Keep Δ) Δ₂ τ → LiveExpr Δ (Δ₁ ∪ pop Δ₂) τ
push-let e₁ (Var x) = Let e₁ (Var x)
push-let e₁ (App e₂ e₃) = {!!}
push-let e₁ (Lam e₂) = Let e₁ (Lam e₂)
push-let e₁ (Let e₂ e₃) = {!!}
push-let e₁ (Val v) = Let e₁ (Val v)
push-let e₁ (Plus {Γ} {Δ₂} {Δ₃} e₂ e₃) with Δ₂ | Δ₃
... | Drop Δ₂ | Drop Δ₃ = {!!}
... | Drop Δ₂ | Keep Δ₃ = let e₃' = push-let e₁ e₃
                              e₂' = Live.Let e₁ e₂  -- hack, we want to strengthen
                          in {! !}
... | Keep Δ₂ | Drop Δ₃ = {!!}
... | Keep Δ₂ | Keep Δ₃ = Let e₁ (Plus e₂ e₃)  -- don't duplicate
-}

push-let : (Δ : SubCtx Γ) → Expr ⌊ Δ ⌋ σ → Expr ⌊ Keep {Γ} {σ} Δ ⌋ τ → Expr ⌊ Δ ⌋ τ
push-let {Γ} {σ} Δ decl (Var x) = Let decl (Var x)  -- the Let might be unnecessary here, if x doesn't refer to the declaration
push-let {Γ} {σ} Δ decl (App e₁ e₂) with strengthen (Drop Δ) (Keep Δ) (⊆-refl Δ) e₁ | strengthen (Drop Δ) (Keep Δ) (⊆-refl Δ) e₂
... | inj₁ tt  | inj₁ tt  = Let decl (App e₁ e₂)
... | inj₁ tt  | inj₂ e₂' = App (push-let Δ decl e₁) e₂'
... | inj₂ e₁' | inj₁ tt  = App e₁' (push-let Δ decl e₂)
... | inj₂ e₁' | inj₂ e₂' = App e₁' e₂'
push-let {Γ} {σ} Δ decl (Lam e) = Let decl (Lam e)  -- don't push into lambda
push-let {Γ} {σ} Δ decl (Let e₁ e₂) with strengthen (Drop Δ) (Keep Δ) (⊆-refl Δ) e₁ | strengthen (Keep (Drop Δ)) (Keep (Keep Δ)) (⊆-refl Δ) e₂
... | inj₁ tt  | inj₁ tt  = Let decl (Let e₁ e₂)
... | inj₁ tt  | inj₂ e₂' = Let (push-let Δ decl e₁) e₂'
... | inj₂ e₁' | inj₁ tt  = Let e₁' {!!}  -- TODO: need to go under the binder here :/
... | inj₂ e₁' | inj₂ e₂' = Let e₁' e₂'
push-let {Γ} {σ} Δ decl (Val v) = Val v
push-let {Γ} {σ} Δ decl (Plus e₁ e₂) with strengthen (Drop Δ) (Keep Δ) (⊆-refl Δ) e₁ | strengthen (Drop Δ) (Keep Δ) (⊆-refl Δ) e₂
... | inj₁ tt  | inj₁ tt  = Let decl (Plus e₁ e₂)
... | inj₁ tt  | inj₂ e₂' = Plus (push-let Δ decl e₁) e₂'
... | inj₂ e₁' | inj₁ tt  = Plus e₁' (push-let Δ decl e₂)
... | inj₂ e₁' | inj₂ e₂' = Plus e₁' e₂'

-- TODO: can this simplify the code?
potentially-push-let : (Δ : SubCtx (σ ∷ Γ)) → Expr ⌊ pop Δ ⌋ σ → Expr ⌊ Δ ⌋ τ → Expr ⌊ pop Δ ⌋ τ
potentially-push-let (Drop Δ) decl e = e
potentially-push-let (Keep Δ) decl e = push-let Δ decl e
