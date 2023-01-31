-- Let Floating (inwards)
module LetInward where

open import Data.Nat using (_+_)
open import Data.List using (List ; _∷_ ; [])
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; cong₂ ; sym)
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import Lang
open import SubCtx
open import Live

-- Push the let-binding inwards as far as possible without
-- - duplicating it
-- - pushing it into a lambda
--
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

-- query on demand?
-- potentially-push ?
