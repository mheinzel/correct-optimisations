-- Let Floating (inwards)
module DeBruijn.LetInward where

open import Data.Nat using (_+_)
open import Data.List using (List ; _∷_ ; [] ; _++_)
open import Data.Unit
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; cong₂ ; sym)
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import Core
open import OPE
open import DeBruijn.Lang
open import DeBruijn.Live

-- Push the let-binding inwards as far as possible without
-- - duplicating it
-- - pushing it into a lambda

-- Working with plain OPEs here instead of SubCtx.
-- Let's keep it separate for now and later look for ways to unify.

weaken-Ref : {Γ' Γ : Ctx} → Γ' ⊑ Γ → Ref σ Γ' → Ref σ Γ
weaken-Ref (θ os) Top = Top
weaken-Ref (θ os) (Pop x) = Pop (weaken-Ref θ x)
weaken-Ref (θ o') x = Pop (weaken-Ref θ x)

weaken : {Γ' Γ : Ctx} → Γ' ⊑ Γ → Expr Γ' τ → Expr Γ τ
weaken θ (Var x) = Var (weaken-Ref θ x)
weaken θ (App e₁ e₂) = App (weaken θ e₁) (weaken θ e₂)
weaken θ (Lam e) = Lam (weaken (θ os) e)
weaken θ (Let e₁ e₂) = Let (weaken θ e₁) (weaken (θ os) e₂)
weaken θ (Val x) = Val x
weaken θ (Plus e₁ e₂) = Plus (weaken θ e₁) (weaken θ e₂)
  
strengthen-Ref : {Γ' Γ : Ctx} → Γ' ⊑ Γ → Ref σ Γ → ⊤ ⊎ Ref σ Γ'
strengthen-Ref (θ os) Top = inj₂ Top
strengthen-Ref (θ os) (Pop x) with strengthen-Ref θ x
... | inj₁ tt = inj₁ tt
... | inj₂ x' = inj₂ (Pop x')
strengthen-Ref (θ o') Top = inj₁ tt -- ref became invalid by strengthening
strengthen-Ref (θ o') (Pop x) = strengthen-Ref θ x

strengthen : {Γ' Γ : Ctx} → Γ' ⊑ Γ → Expr Γ τ → ⊤ ⊎ Expr Γ' τ
strengthen θ (Var x) with strengthen-Ref θ x
... | inj₁ tt = inj₁ tt
... | inj₂ x' = inj₂ (Var x') 
strengthen θ (App e₁ e₂) with strengthen θ e₁ | strengthen θ e₂
... | inj₂ e₁' | inj₂ e₂' = inj₂ (App e₁' e₂')
... | _        | _        = inj₁ tt
strengthen θ (Lam {σ = σ} e) with strengthen (θ os) e
... | inj₂ e' = inj₂ (Lam e')
... | inj₁ tt = inj₁ tt
strengthen θ (Let {σ = σ} e₁ e₂) with strengthen θ e₁ | strengthen (θ os) e₂
... | inj₂ e₁' | inj₂ e₂' = inj₂ (Let e₁' e₂')
... | _        | _        = inj₁ tt
strengthen θ (Val x) = inj₂ (Val x)
strengthen θ (Plus e₁ e₂) with strengthen θ e₁ | strengthen θ e₂
... | inj₂ e₁' | inj₂ e₂' = inj₂ (Plus e₁' e₂')
... | _        | _        = inj₁ tt

pop-at : (Γ : Ctx) → Ref τ Γ → Ctx
pop-at (σ ∷ Γ) Top = Γ
pop-at (σ ∷ Γ) (Pop i) = σ ∷ pop-at Γ i

o-pop-at : (i : Ref τ Γ) → pop-at Γ i ⊑ Γ
o-pop-at Top = oi o'
o-pop-at (Pop i) = (o-pop-at i) os

strengthen-pop-at : (i : Ref σ Γ) → Expr Γ τ → ⊤ ⊎ Expr (pop-at Γ i) τ
strengthen-pop-at i = strengthen (o-pop-at i)

strengthen-keep-pop-at : {σ' : U} (i : Ref σ Γ) → Expr (σ' ∷ Γ) τ → ⊤ ⊎ Expr (σ' ∷ pop-at Γ i) τ
strengthen-keep-pop-at i = strengthen ((o-pop-at i) os)

-- NOTE: The following code feels like it requires more different operations than it should.
-- But it's kind of expected: We are dealing with ordering preserving embeddings, but reordering the bindings.

lift-Ref : {Γ₁ Γ₂ : Ctx} (f : Ref τ Γ₁ → Ref τ Γ₂) → Ref τ (σ ∷ Γ₁) → Ref τ (σ ∷ Γ₂)
lift-Ref f Top = Top
lift-Ref f (Pop x) = Pop (f x)

flip-Ref : {σ₁ σ₂ : U} → Ref τ (σ₁ ∷ σ₂ ∷ Γ) → Ref τ (σ₂ ∷ σ₁ ∷ Γ)
flip-Ref Top = Pop Top
flip-Ref (Pop Top) = Top
flip-Ref (Pop (Pop x)) = Pop (Pop x)

rename-top-Ref : (Γ' : Ctx) (i : Ref σ Γ) → Ref τ (Γ' ++ Γ) → Ref τ (Γ' ++ (σ ∷ pop-at Γ i))
rename-top-Ref (σ' ∷ Γ') i Top = Top
rename-top-Ref (σ' ∷ Γ') i (Pop x) = Pop (rename-top-Ref Γ' i x)  -- just work through Γ' first
rename-top-Ref [] Top x = x
rename-top-Ref [] (Pop i) x = flip-Ref (lift-Ref (rename-top-Ref [] i) x)

rename-top : (Γ' : Ctx) (i : Ref σ Γ) → Expr (Γ' ++ Γ) τ → Expr (Γ' ++ (σ ∷ pop-at Γ i)) τ
rename-top Γ' i (Var x) = Var (rename-top-Ref Γ' i x)
rename-top Γ' i (App e₁ e₂) = App (rename-top Γ' i e₁) (rename-top Γ' i e₂)
rename-top Γ' i (Lam e) = Lam (rename-top (_ ∷ Γ') i e)
rename-top Γ' i (Let e₁ e₂) = Let (rename-top Γ' i e₁) (rename-top (_ ∷ Γ') i e₂)
rename-top Γ' i (Val v) = Val v
rename-top Γ' i (Plus e₁ e₂) = Plus (rename-top Γ' i e₁) (rename-top Γ' i e₂)

-- TODO: can we find a more general type, to allow for reordering and only optionally popping something?
push-let : (i : Ref σ Γ) → Expr (pop-at Γ i) σ → Expr Γ τ → Expr (pop-at Γ i) τ
push-let {Γ = Γ} i decl (Var x) with rename-top-Ref [] i x
... | Top = decl
... | Pop x' = Var x'
push-let i decl (App e₁ e₂) with strengthen-pop-at i e₁ | strengthen-pop-at i e₂
... | inj₁ tt  | inj₁ tt  = Let decl (App (rename-top [] i e₁) (rename-top [] i e₂))
... | inj₁ tt  | inj₂ e₂' = App (push-let i decl e₁) e₂'
... | inj₂ e₁' | inj₁ tt  = App e₁' (push-let i decl e₂)
... | inj₂ e₁' | inj₂ e₂' = App e₁' e₂'
push-let i decl (Lam e) = Let decl (Lam (rename-top (_ ∷ []) i e))  -- don't push into lambda
push-let i decl (Let e₁ e₂) with strengthen-pop-at i e₁ | strengthen-keep-pop-at i e₂
... | inj₁ tt  | inj₁ tt  = Let decl (Let (rename-top [] i e₁) (rename-top (_ ∷ []) i e₂))
... | inj₁ tt  | inj₂ e₂' = Let (push-let i decl e₁) e₂'
... | inj₂ e₁' | inj₁ tt  = Let e₁' (push-let (Pop i) (weaken (oi o') decl) e₂)  -- going under the binder here
... | inj₂ e₁' | inj₂ e₂' = Let e₁' e₂'
push-let i decl (Val v) = Val v
push-let i decl (Plus e₁ e₂) with strengthen-pop-at i e₁ | strengthen-pop-at i e₂
... | inj₁ tt  | inj₁ tt  = Let decl (Plus (rename-top [] i e₁) (rename-top [] i e₂))
... | inj₁ tt  | inj₂ e₂' = Plus (push-let i decl e₁) e₂'
... | inj₂ e₁' | inj₁ tt  = Plus e₁' (push-let i decl e₂)
... | inj₂ e₁' | inj₂ e₂' = Plus e₁' e₂'

-- This is the same signature as for `Let` itself.
push-let' : Expr Γ σ → Expr (σ ∷ Γ) τ → Expr Γ τ
push-let' decl e = push-let Top decl e


{- NOTE: `strengthen` traverses the AST every time, which is inefficient.

Another idea is to use LiveExpr
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

-- NOTE: there is an alternative phrasing:
-- push-let : {σ : U} (Γ₁ Γ₂ : Ctx) → Expr (Γ₁ ++ Γ₂) σ → Expr (Γ₁ ++ (σ ∷ Γ₂)) τ → Expr (Γ₁ ++ Γ₂) τ

-- TODO: what would it look like to push multiple bindings simultaneously?
