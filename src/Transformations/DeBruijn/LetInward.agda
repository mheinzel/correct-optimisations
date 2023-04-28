-- Let Floating (inwards)
module Transformations.DeBruijn.LetInward where

open import Data.Nat using (_+_)
open import Data.List using (List ; _∷_ ; [] ; _++_)
open import Data.Unit
open import Data.Product
open import Data.Maybe.Base as Maybe using (Maybe ; just ; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; cong₂ ; sym)
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import Data.Thinning

open import Language.Core
open Language.Core.Env {U} {⟦_⟧}
open Language.Core.Ref {U} {⟦_⟧}
open import Language.DeBruijn

private
  variable
    σ τ : U
    Γ : Ctx

-- Push the let-binding inwards as far as possible without
-- - duplicating it
-- - pushing it into a lambda
  
strengthen-Ref : {Γ' Γ : Ctx} → Γ' ⊑ Γ → Ref σ Γ → Maybe (Ref σ Γ')
strengthen-Ref (os θ) Top     = just Top
strengthen-Ref (os θ) (Pop x) = Maybe.map Pop (strengthen-Ref θ x)
strengthen-Ref (o' θ) Top     = nothing -- ref became invalid by strengthening
strengthen-Ref (o' θ) (Pop x) = strengthen-Ref θ x

strengthen : {Γ' Γ : Ctx} → Γ' ⊑ Γ → Expr τ Γ → Maybe (Expr τ Γ')
strengthen θ (Var x)      = Maybe.map Var (strengthen-Ref θ x)
strengthen θ (App e₁ e₂)  = Maybe.zipWith App (strengthen θ e₁) (strengthen θ e₂)
strengthen θ (Lam e)      = Maybe.map Lam (strengthen (os θ) e)
strengthen θ (Let e₁ e₂)  = Maybe.zipWith Let (strengthen θ e₁) (strengthen (os θ) e₂)
strengthen θ (Val v)      = just (Val v)
strengthen θ (Plus e₁ e₂) = Maybe.zipWith Plus (strengthen θ e₁) (strengthen θ e₂)

pop-at : (Γ : Ctx) → Ref τ Γ → Ctx
pop-at (σ ∷ Γ) Top = Γ
pop-at (σ ∷ Γ) (Pop i) = σ ∷ pop-at Γ i

o-pop-at : (i : Ref τ Γ) → pop-at Γ i ⊑ Γ
o-pop-at Top = o' oi
o-pop-at (Pop i) = os (o-pop-at i)

strengthen-pop-at : (i : Ref σ Γ) → Expr τ Γ → Maybe (Expr τ (pop-at Γ i))
strengthen-pop-at i = strengthen (o-pop-at i)

strengthen-keep-pop-at : {σ' : U} (i : Ref σ Γ) → Expr τ (σ' ∷ Γ) → Maybe (Expr τ (σ' ∷ pop-at Γ i))
strengthen-keep-pop-at i = strengthen (os (o-pop-at i))

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

rename-top-Expr : (Γ' : Ctx) (i : Ref σ Γ) → Expr τ (Γ' ++ Γ) → Expr τ (Γ' ++ (σ ∷ pop-at Γ i))
rename-top-Expr Γ' i (Var x) = Var (rename-top-Ref Γ' i x)
rename-top-Expr Γ' i (App e₁ e₂) = App (rename-top-Expr Γ' i e₁) (rename-top-Expr Γ' i e₂)
rename-top-Expr Γ' i (Lam e) = Lam (rename-top-Expr (_ ∷ Γ') i e)
rename-top-Expr Γ' i (Let e₁ e₂) = Let (rename-top-Expr Γ' i e₁) (rename-top-Expr (_ ∷ Γ') i e₂)
rename-top-Expr Γ' i (Val v) = Val v
rename-top-Expr Γ' i (Plus e₁ e₂) = Plus (rename-top-Expr Γ' i e₁) (rename-top-Expr Γ' i e₂)

-- TODO: can we find a more general type, to allow for reordering and only optionally popping something?
push-let : (i : Ref σ Γ) → Expr σ (pop-at Γ i) → Expr τ Γ → Expr τ (pop-at Γ i)
push-let {Γ = Γ} i decl (Var x) with rename-top-Ref [] i x
... | Top = decl       -- x' was the same as i, so we discover that σ ≡ τ
... | Pop x' = Var x'  -- declaration was unused
push-let i decl e@(App e₁ e₂) with strengthen-pop-at i e₁ | strengthen-pop-at i e₂
... | nothing  | nothing  = Let decl (rename-top-Expr [] i e)
... | nothing  | just e₂' = App (push-let i decl e₁) e₂'
... | just e₁' | nothing  = App e₁' (push-let i decl e₂)
... | just e₁' | just e₂' = App e₁' e₂'
push-let i decl e@(Lam _) = Let decl (rename-top-Expr [] i e)  -- don't push into lambda
push-let i decl e@(Let e₁ e₂) with strengthen-pop-at i e₁ | strengthen-keep-pop-at i e₂
... | nothing  | nothing  = Let decl (rename-top-Expr [] i e)
... | nothing  | just e₂' = Let (push-let i decl e₁) e₂'
... | just e₁' | nothing  = Let e₁' (push-let (Pop i) (rename-Expr (o' oi) decl) e₂)  -- going under the binder here
... | just e₁' | just e₂' = Let e₁' e₂'
push-let i decl (Val v) = Val v
push-let i decl e@(Plus e₁ e₂) with strengthen-pop-at i e₁ | strengthen-pop-at i e₂
... | nothing  | nothing  = Let decl (rename-top-Expr [] i e)
... | nothing  | just e₂' = Plus (push-let i decl e₁) e₂'
... | just e₁' | nothing  = Plus e₁' (push-let i decl e₂)
... | just e₁' | just e₂' = Plus e₁' e₂'

-- This is the same signature as for `Let` itself.
push-let' : Expr σ Γ → Expr τ (σ ∷ Γ) → Expr τ Γ
push-let' decl e = push-let Top decl e


{- NOTE: `strengthen` traverses the AST every time, which is inefficient.

Another idea is to use LiveExpr
-- TODO: Can we assume that the binding must be live? (issues with Var case)
-- TODO: This would be easier with a less restrictive version of LiveExpr
-- IDEA: annotations are updated with each transformation, changes bubble up
-- IDEA/HACK: Also push binding into branches where they're not used, but don't recurse.
--            Then they can be removed again in a separate pass.
-}

-- NOTE: there is an alternative phrasing:
-- push-let : {σ : U} (Γ₁ Γ₂ : Ctx) → Expr σ (Γ₁ ++ Γ₂) → Expr τ (Γ₁ ++ (σ ∷ Γ₂)) → Expr τ (Γ₁ ++ Γ₂)

-- TODO: what would it look like to push multiple bindings simultaneously?
