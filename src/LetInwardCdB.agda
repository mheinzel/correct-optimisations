-- Let Floating (inwards) using co-de-Bruijn representation
module LetInwardCdB where

open import Data.Nat using (_+_)
open import Data.List using (List ; _∷_ ; [] ; _++_)
open import Data.Unit
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; cong₂ ; sym)
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import Lang hiding (Expr ; Var ; App ; Lam ; Let ; Plus)
open import LangCdB
open import OPE

-- Push the let-binding inwards as far as possible without
-- - duplicating it
-- - pushing it into a lambda

pop-at : (Γ : Ctx) → Ref τ Γ → Ctx
pop-at (σ ∷ Γ) Top = Γ
pop-at (σ ∷ Γ) (Pop i) = σ ∷ pop-at Γ i

rename-top : (Γ' : Ctx) (i : Ref σ Γ) → Expr τ (Γ' ++ Γ) → Expr τ (Γ' ++ (σ ∷ pop-at Γ i))
rename-top Γ' i e = {!!}

-- push-let : (i : Ref σ Γ) → Expr σ (pop-at Γ i) → Expr τ Γ → Expr τ (pop-at Γ i)

push-let : {Γ₁ Γ₂ Γ : Ctx} (i : Ref σ Γ₂) → Expr σ Γ₁ → Expr τ Γ₂ → Union Γ₁ (pop-at Γ₂ i) Γ → Expr τ Γ
push-let Top decl Var U with law-Union-Γ₁[] U
... | refl = decl
push-let i decl (App u e₁ e₂) U = {!!}
push-let i decl (Lam b e) U =
  Let live U decl (rename-top [] i (Lam b e))
push-let i decl (Let b u e₁ e₂) U = {!!}
push-let i decl (Plus u e₁ e₂) U =
  let ope₁ = o-Union₁ u
      ope₂ = o-Union₂ u
  in {!!}

-- TODO: continue

{-
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
-}

-- This is the same signature as for `Let live` itself.
push-let' : {Γ₁ Γ₂ Γ : Ctx} → Union Γ₁ Γ₂ Γ → Expr σ Γ₁ → Expr τ (σ ∷ Γ₂) → Expr τ Γ
push-let' u decl e = push-let Top decl e u
