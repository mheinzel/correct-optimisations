-- Let Floating (inwards)
module Transformations.DeBruijn.LetInwardDirect where

open import Data.Nat using (_+_)
open import Data.List using (List ; _∷_ ; [] ; _++_)
open import Data.Unit
open import Data.Product
open import Data.Maybe.Base as Maybe using (Maybe ; just ; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; cong₂ ; sym)
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import Language.Core
open Language.Core.Env {U} {⟦_⟧}
open Language.Core.Ref {U} {⟦_⟧}
open import Language.DeBruijn

private
  variable
    σ τ : U
    Γ Γ₁ Γ₂ : Ctx

-- Push the let-binding inwards as far as possible without
-- - duplicating it
-- - pushing it into a lambda

strengthen-Ref : Ref τ (Γ₁ ++ σ ∷ Γ₂) → Maybe (Ref τ (Γ₁ ++ Γ₂))
strengthen-Ref {Γ₁ = _ ∷ Γ₁} Top = just Top
strengthen-Ref {Γ₁ = _ ∷ Γ₁} (Pop x) = Maybe.map Pop (strengthen-Ref x)
strengthen-Ref {Γ₁ = []} Top = nothing
strengthen-Ref {Γ₁ = []} (Pop x) = just x

strengthen : Expr τ (Γ₁ ++ σ ∷ Γ₂) → Maybe (Expr τ (Γ₁ ++ Γ₂))
strengthen (Var x) = Maybe.map Var (strengthen-Ref x)
strengthen (App e₁ e₂) = Maybe.zipWith App (strengthen e₁) (strengthen e₂)
strengthen {Γ₁ = Γ₁} (Lam e) = Maybe.map Lam (strengthen {Γ₁ = _ ∷ Γ₁} e)
strengthen {Γ₁ = Γ₁} (Let e₁ e₂)  = Maybe.zipWith Let (strengthen e₁) (strengthen {Γ₁ = _ ∷ Γ₁} e₂)
strengthen (Val v) = just (Val v)
strengthen (Plus e₁ e₂) = Maybe.zipWith Plus (strengthen e₁) (strengthen e₂)

lift-Ref : {Γ₁ Γ₂ : Ctx} (f : Ref τ Γ₁ → Ref τ Γ₂) → Ref τ (σ ∷ Γ₁) → Ref τ (σ ∷ Γ₂)
lift-Ref f Top = Top
lift-Ref f (Pop x) = Pop (f x)

flip-Ref : {σ₁ σ₂ : U} → Ref τ (σ₁ ∷ σ₂ ∷ Γ) → Ref τ (σ₂ ∷ σ₁ ∷ Γ)
flip-Ref Top = Pop Top
flip-Ref (Pop Top) = Top
flip-Ref (Pop (Pop x)) = Pop (Pop x)

rename-top-Ref : (Γ' : Ctx) → Ref τ (Γ' ++ Γ₁ ++ σ ∷ Γ₂) → Ref τ (Γ' ++ σ ∷ Γ₁ ++ Γ₂)
rename-top-Ref (σ ∷ Γ') Top = Top
rename-top-Ref (σ ∷ Γ') (Pop x) = Pop (rename-top-Ref Γ' x)
rename-top-Ref {Γ₁ = []} [] x = x
rename-top-Ref {Γ₁ = τ ∷ Γ₁} [] x = flip-Ref (lift-Ref (rename-top-Ref {Γ₁ = Γ₁} []) x)

rename-top-Expr : (Γ' : Ctx) → Expr τ (Γ' ++ Γ₁ ++ σ ∷ Γ₂) → Expr τ (Γ' ++ σ ∷ Γ₁ ++ Γ₂)
rename-top-Expr Γ' (Var x) = Var (rename-top-Ref Γ' x)
rename-top-Expr Γ' (App e₁ e₂) = App (rename-top-Expr Γ' e₁) (rename-top-Expr Γ' e₂)
rename-top-Expr Γ' (Lam e₁) = Lam (rename-top-Expr (_ ∷ Γ') e₁)
rename-top-Expr Γ' (Let e₁ e₂) = Let (rename-top-Expr Γ' e₁) (rename-top-Expr (_ ∷ Γ') e₂)
rename-top-Expr Γ' (Val v) = Val v
rename-top-Expr Γ' (Plus e₁ e₂) = Plus (rename-top-Expr Γ' e₁) (rename-top-Expr Γ' e₂)

-- NOTE: `strengthen` traverses the AST every time, which is inefficient.
push-let : Expr σ (Γ₁ ++ Γ₂) → Expr τ (Γ₁ ++ σ ∷ Γ₂) → Expr τ (Γ₁ ++ Γ₂)
push-let decl (Var x) with rename-top-Ref [] x
... | Top = decl
... | Pop x' = Var x'
push-let decl e@(App e₁ e₂) with strengthen e₁ | strengthen e₂
-- declaration not used at all
... | just e₁' | just e₂' = App e₁' e₂'
-- declaration used in left subexpression
... | nothing  | just e₂' = App (push-let decl e₁) e₂'
-- declaration used in right subexpression
... | just e₁' | nothing  = App e₁' (push-let decl e₂)
-- declaration used in both subexpressions (don't push further!)
... | nothing  | nothing  = Let decl (rename-top-Expr [] e)
push-let decl e@(Lam e₁) =
  Let decl (rename-top-Expr [] e) -- Don't push into Lam!
push-let {Γ₁ = Γ₁} decl e@(Let e₁ e₂) with strengthen e₁ | strengthen {Γ₁ = _ ∷ Γ₁} e₂ 
-- declaration not used at all
... | just e₁' | just e₂' = Let e₁' e₂'
-- declaration used in left subexpression
... | nothing  | just e₂' = Let (push-let decl e₁) e₂'
-- declaration used in right subexpression, weakening declaration as we go under the binder.
... | just e₁' | nothing  = Let e₁' (push-let {Γ₁ = _ ∷ Γ₁} (weaken decl) e₂)
-- declaration used in both subexpressions (don't push further!)
... | nothing  | nothing  = Let decl (rename-top-Expr [] e)
push-let decl (Val v) =
  Val v
push-let decl e@(Plus e₁ e₂) with strengthen e₁ | strengthen e₂
-- declaration not used at all
... | just e₁' | just e₂' = Plus e₁' e₂'
-- declaration used in left subexpression
... | nothing  | just e₂' = Plus (push-let decl e₁) e₂'
-- declaration used in right subexpression
... | just e₁' | nothing  = Plus e₁' (push-let decl e₂)
-- declaration used in both subexpressions (don't push further!)
... | nothing  | nothing  = Let decl (rename-top-Expr [] e)

-- This is the same signature as for `Let` itself.
push-let' : Expr σ Γ → Expr τ (σ ∷ Γ) → Expr τ Γ
push-let' = push-let {Γ₁ = []}

-- TODO: what would it look like to push multiple bindings simultaneously?

-- TODO: Correctness?
