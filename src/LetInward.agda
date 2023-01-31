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

data OPE : Ctx → Ctx → Set where
  Empty : OPE [] []
  Keep : {Γ' Γ : Ctx} (τ : U) → OPE Γ' Γ → OPE (τ ∷ Γ') (τ ∷ Γ)
  Drop : {Γ' Γ : Ctx} (τ : U) → OPE Γ' Γ → OPE Γ' (τ ∷ Γ)

ope-id : (Γ : Ctx) → OPE Γ Γ
ope-id [] = Empty
ope-id (x ∷ Γ) = Keep x (ope-id Γ)

weaken-Ref : {Γ' Γ : Ctx} (ope : OPE Γ' Γ) → Ref σ Γ' → Ref σ Γ
weaken-Ref (Keep τ ope) Top = Top
weaken-Ref (Keep τ ope) (Pop x) = Pop (weaken-Ref ope x)
weaken-Ref (Drop τ ope) x = Pop (weaken-Ref ope x)

weaken : {Γ' Γ : Ctx} (ope : OPE Γ' Γ) → Expr Γ' τ → Expr Γ τ
weaken ope (Var x) = Var (weaken-Ref ope x)
weaken ope (App e₁ e₂) = App (weaken ope e₁) (weaken ope e₂)
weaken ope (Lam e) = Lam (weaken (Keep _ ope) e)
weaken ope (Let e₁ e₂) = Let (weaken ope e₁) (weaken (Keep _ ope) e₂)
weaken ope (Val x) = Val x
weaken ope (Plus e₁ e₂) = Plus (weaken ope e₁) (weaken ope e₂)
  
strengthen-Ref : {Γ' Γ : Ctx} (ope : OPE Γ' Γ) → Ref σ Γ → ⊤ ⊎ Ref σ Γ'
strengthen-Ref (Keep τ ope) Top = inj₂ Top
strengthen-Ref (Keep τ ope) (Pop x) with strengthen-Ref ope x
... | inj₁ tt = inj₁ tt
... | inj₂ x' = inj₂ (Pop x')
strengthen-Ref (Drop τ ope) Top = inj₁ tt -- ref became invalid by strengthening
strengthen-Ref (Drop τ ope) (Pop x) = strengthen-Ref ope x

strengthen : {Γ' Γ : Ctx} (ope : OPE Γ' Γ) → Expr Γ τ → ⊤ ⊎ Expr Γ' τ
strengthen ope (Var x) with strengthen-Ref ope x
... | inj₁ tt = inj₁ tt
... | inj₂ x' = inj₂ (Var x') 
strengthen ope (App e₁ e₂) with strengthen ope e₁ | strengthen ope e₂
... | inj₂ e₁' | inj₂ e₂' = inj₂ (App e₁' e₂')
... | _        | _        = inj₁ tt
strengthen ope (Lam {σ = σ} e) with strengthen (Keep σ ope) e
... | inj₂ e' = inj₂ (Lam e')
... | inj₁ tt = inj₁ tt
strengthen ope (Let {σ = σ} e₁ e₂) with strengthen ope e₁ | strengthen (Keep σ ope) e₂
... | inj₂ e₁' | inj₂ e₂' = inj₂ (Let e₁' e₂')
... | _        | _        = inj₁ tt
strengthen ope (Val x) = inj₂ (Val x)
strengthen ope (Plus e₁ e₂) with strengthen ope e₁ | strengthen ope e₂
... | inj₂ e₁' | inj₂ e₂' = inj₂ (Plus e₁' e₂')
... | _        | _        = inj₁ tt

push-let : Expr Γ σ → Expr (σ ∷ Γ) τ → Expr Γ τ
push-let decl (Var x) with strengthen-Ref (Drop _ (ope-id _)) x
... | inj₁ tt = Let decl (Var x)
... | inj₂ x' = Var x'
push-let decl (App e₁ e₂) with strengthen (Drop _ (ope-id _)) e₁ | strengthen (Drop _ (ope-id _)) e₂
... | inj₁ tt  | inj₁ tt  = Let decl (App e₁ e₂)
... | inj₁ tt  | inj₂ e₂' = App (push-let decl e₁) e₂'
... | inj₂ e₁' | inj₁ tt  = App e₁' (push-let decl e₂)
... | inj₂ e₁' | inj₂ e₂' = App e₁' e₂'
push-let decl (Lam e) = Let decl (Lam e)  -- don't push into lambda
push-let decl (Let {σ = σ} e₁ e₂) with strengthen (Drop _ (ope-id _)) e₁ | strengthen (Keep _ (Drop _ (ope-id _))) e₂
... | inj₁ tt  | inj₁ tt  = Let decl (Let e₁ e₂)
... | inj₁ tt  | inj₂ e₂' = Let (push-let decl e₁) e₂'
... | inj₂ e₁' | inj₁ tt  =
  let decl' = weaken (Drop σ (ope-id _)) decl
  in Let e₁' {!!}  -- TODO: need to go under the binder here :/
... | inj₂ e₁' | inj₂ e₂' = Let e₁' e₂'
push-let decl (Val v) = Val v
push-let decl (Plus e₁ e₂) with strengthen (Drop _ (ope-id _)) e₁ | strengthen (Drop _ (ope-id _)) e₂
... | inj₁ tt  | inj₁ tt  = Let decl (Plus e₁ e₂)
... | inj₁ tt  | inj₂ e₂' = Plus (push-let decl e₁) e₂'
... | inj₂ e₁' | inj₁ tt  = Plus e₁' (push-let decl e₂)
... | inj₂ e₁' | inj₂ e₂' = Plus e₁' e₂'

{-
data PartialEnv : (Γ : Ctx) (Δ Δ' : SubCtx Γ) → Set where
  Empty   : PartialEnv [] Empty Empty
  Leave   : PartialEnv Γ Δ Δ' → PartialEnv (τ ∷ Γ) (Keep Δ) (Keep Δ')
  Provide : Expr Γ τ → PartialEnv Γ Δ Δ' → PartialEnv (τ ∷ Γ) (Keep Δ) (Drop Δ')

push-let' : (Γ : Ctx) (Δ Δ' : SubCtx Γ) → PartialEnv Γ Δ Δ' → Expr ⌊ Δ ⌋ τ → Expr ⌊ Δ' ⌋ τ
-- push-let' : (Δ : SubCtx Γ) → Expr ⌊ Δ ⌋ σ → Expr ⌊ Keep {Γ} {σ} Δ ⌋ τ → Expr ⌊ Δ ⌋ τ
push-let' Γ Δ Δ' env (Var x) = {!!}
push-let' Γ Δ Δ' env (App e e₁) = {!!}
push-let' Γ Δ Δ' env (Lam e) = {!!}
push-let' Γ Δ Δ' env (Let e e₁) = {!!}
push-let' Γ Δ Δ' env (Val x) = {!!}
push-let' Γ Δ Δ' env (Plus e e₁) = {!!}

-- TODO: can this simplify the code?
potentially-push-let : (Δ : SubCtx (σ ∷ Γ)) → Expr ⌊ pop Δ ⌋ σ → Expr ⌊ Δ ⌋ τ → Expr ⌊ pop Δ ⌋ τ
potentially-push-let (Drop Δ) decl e = e
potentially-push-let (Keep Δ) decl e = push-let Δ decl e
-}
