-- Let Floating (inwards), using annotated expressions.
module Transformations.DeBruijn.LetInward where

open import Data.Nat using (_+_)
open import Data.List using (List ; _∷_ ; [] ; _++_)
open import Data.Unit
open import Data.Product
open import Data.Maybe.Base as Maybe using (Maybe ; just ; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; cong₂ ; sym)
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import Data.Thinning
open import Stdlib using (coerce)

open import Language.Core
open Language.Core.Env {U} {⟦_⟧}
open Language.Core.Ref {U} {⟦_⟧}
open import Language.DeBruijn
open import Transformations.DeBruijn.Live
import Transformations.DeBruijn.DeadBinding as DBE
open import Transformations.DeBruijn.LetInwardDirect using (flip-Ref ; lift-Ref ; rename-top-Ref ; rename-top)

private
  variable
    σ τ : U
    Γ Γ₁ Γ₂ Δ : Ctx

-- Push the let-binding inwards as far as possible without
-- - duplicating it
-- - pushing it into a lambda

-- IDEA: Can we find a more general type, to allow for reordering and only optionally popping something?
-- IDEA: Can we avoid repeatedly weakening the declaration?
-- IDEA: Can we assume that the binding must be live? (issues with Var case)
transform : {θ : Δ ⊑ (Γ₁ ++ σ ∷ Γ₂)} → Expr σ (Γ₁ ++ Γ₂) → LiveExpr τ θ → Expr τ (Γ₁ ++ Γ₂)
transform decl (Var x) with rename-top-Ref [] x
... | Top = decl
... | Pop x' = Var x'
transform {Γ₁ = Γ₁} decl e@(App {θ₁ = θ} {θ₂ = ϕ} e₁ e₂) with Γ₁ ⊣ θ | Γ₁ ⊣ ϕ
-- declaration not used at all
... | split θ₁ (o' θ₂) (refl , refl) | split ϕ₁ (o' ϕ₂) (refl , refl) =
  App (DBE.transform e₁ (θ₁ ++⊑ θ₂)) (DBE.transform e₂ (ϕ₁ ++⊑ ϕ₂))
-- declaration used in left subexpression
... | split θ₁ (os θ₂) (refl , refl) | split ϕ₁ (o' ϕ₂) (refl , refl) =
  App (transform decl e₁) (DBE.transform e₂ (ϕ₁ ++⊑ ϕ₂))
-- declaration used in right subexpression
... | split θ₁ (o' θ₂) (refl , refl) | split ϕ₁ (os ϕ₂) (refl , refl) =
  App (DBE.transform e₁ (θ₁ ++⊑ θ₂)) (transform decl e₂)
-- declaration used in both subexpressions (don't push further!)
... | split θ₁ (os θ₂) (refl , refl) | split ϕ₁ (os ϕ₂) (refl , refl) =
  Let decl (rename-top (forget e))
transform decl e@(Lam {θ = θ} _) =
  Let decl (rename-top (forget e))
transform {Γ₁ = Γ₁} decl e@(Let {θ₁ = θ} {θ₂ = ϕ} e₁ e₂) with Γ₁ ⊣ θ | Γ₁ ⊣ pop ϕ
-- declaration not used at all
... | split θ₁ (o' θ₂) (refl , refl) | split ϕ₁ (o' ϕ₂) (p , q) =
  Let (DBE.transform e₁ (θ₁ ++⊑ θ₂)) (DBE.transform e₂ (un-pop ϕ ₒ os (coerce (_⊑ (Γ₁ ++ _)) (sym p) (ϕ₁ ++⊑ ϕ₂))))
-- declaration used in left subexpression
... | split θ₁ (os θ₂) (refl , refl) | split ϕ₁ (o' ϕ₂) (p , q) =
  Let (transform decl e₁) (DBE.transform e₂ (un-pop ϕ ₒ os (coerce (_⊑ (Γ₁ ++ _)) (sym p) (ϕ₁ ++⊑ ϕ₂))))
-- declaration used in right subexpression
... | split θ₁ (o' θ₂) (refl , refl) | split ϕ₁ (os ϕ₂) (p , q) =
  Let (DBE.transform e₁ (θ₁ ++⊑ θ₂)) (transform {Γ₁ = _ ∷ Γ₁} (weaken decl) e₂)
-- declaration used in both subexpressions (don't push further!)
... | split θ₁ (os θ₂) (refl , refl) | split ϕ₁ (os ϕ₂) (p , q) =
  Let decl (rename-top (forget e))
transform decl (Val v) =
  Val v
transform {Γ₁ = Γ₁} decl e@(Plus {θ₁ = θ} {θ₂ = ϕ} e₁ e₂) with Γ₁ ⊣ θ | Γ₁ ⊣ ϕ
-- declaration not used at all
... | split θ₁ (o' θ₂) (refl , refl) | split ϕ₁ (o' ϕ₂) (refl , refl) =
  Plus (DBE.transform e₁ (θ₁ ++⊑ θ₂)) (DBE.transform e₂ (ϕ₁ ++⊑ ϕ₂))
-- declaration used in left subexpression
... | split θ₁ (os θ₂) (refl , refl) | split ϕ₁ (o' ϕ₂) (refl , refl) =
  Plus (transform decl e₁) (DBE.transform e₂ (ϕ₁ ++⊑ ϕ₂))
-- declaration used in right subexpression
... | split θ₁ (o' θ₂) (refl , refl) | split ϕ₁ (os ϕ₂) (refl , refl) =
  Plus (DBE.transform e₁ (θ₁ ++⊑ θ₂)) (transform decl e₂)
-- declaration used in both subexpressions (don't push further!)
... | split θ₁ (os θ₂) (refl , refl) | split ϕ₁ (os ϕ₂) (refl , refl) =
  Let decl (rename-top (forget e))
 
push-let : Expr σ (Γ₁ ++ Γ₂)  → Expr τ (Γ₁ ++ σ ∷ Γ₂) → Expr τ (Γ₁ ++ Γ₂)
push-let decl e = let _ , θ , le = analyse e in transform decl le

-- This is the same signature as for `Let` itself.
push-let' : Expr σ Γ → Expr τ (σ ∷ Γ) → Expr τ Γ
push-let' = push-let {Γ₁ = []}

-- Another idea is to return a LiveExpr.
-- This would be easier with a less restrictive version of LiveExpr.
-- IDEA: annotations are updated with each transformation, changes bubble up
-- IDEA/HACK: Also push binding into branches where they're not used, but don't recurse.
--            Then they can be removed again in a separate pass.

-- TODO: Correctness?
