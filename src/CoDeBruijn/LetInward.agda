-- Let Floating (inwards) using co-de-Bruijn representation
--
-- Push the let-binding inwards as far as possible without
-- - duplicating it
-- - pushing it into a lambda
module CoDeBruijn.LetInward where

open import Data.Nat using (_+_)
open import Data.List using (List ; _∷_ ; [] ; _++_)
open import Data.List.Properties using (++-assoc ; ∷-injective ; ++-conicalˡ)
open import Data.Unit
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; cong₂ ; sym ; trans)
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import Core
open import CoDeBruijn.Lang
open import OPE


lemma-[x]≡ : ∀ Γ₁ Γ₂ (p : τ ∷ [] ≡ Γ₁ ++ (σ ∷ Γ₂)) → (σ ≡ τ) × (Γ₁ ≡ []) × (Γ₂ ≡ [])
lemma-[x]≡ [] .[] refl = refl , refl , refl
lemma-[x]≡ (x ∷ Γ₁) Γ₂ p with ∷-injective p
lemma-[x]≡ (x ∷ []) Γ₂ p | _ , ()
lemma-[x]≡ (x ∷ x₁ ∷ Γ₁) Γ₂ p | _ , ()

-- TODO: can this be unified with push-let?
rename-top : (Γ' Γ₁ Γ₂ : Ctx) → Expr τ Γ → (Γ ≡ Γ' ++ Γ₁ ++ σ ∷ Γ₂) → Expr τ (Γ' ++ σ ∷ Γ₁ ++ Γ₂)
rename-top Γ' Γ₁ Γ₂ Var p
  with refl , p' , refl ← lemma-[x]≡ (Γ' ++ Γ₁) Γ₂ (trans p (sym (++-assoc Γ' Γ₁ (_ ∷ Γ₂))))
  with refl ← ++-conicalˡ Γ' Γ₁ p'
  with refl ← p'
  = Var
rename-top Γ' Γ₁ Γ₂ (App (pair (e₁ ↑ θ₁) (e₂ ↑ θ₂) c)) p =
  App (pair ({!rename-top!} ↑ {!!}) {!!} {!!})
rename-top Γ' Γ₁ Γ₂ (Lam x) p = {!!}
rename-top Γ' Γ₁ Γ₂ (Let x) p = {!!}
rename-top Γ' Γ₁ Γ₂ (Val v) p = {!!}
rename-top Γ' Γ₁ Γ₂ (Plus x) p = {!!}

-- push-let : (i : Ref σ Γ) → Expr σ (pop-at Γ i) → Expr τ Γ → Expr τ (pop-at Γ i)

-- TODO: how to introduce reordering?
-- TODO: ideally we would also require some kind of Cover-condition on the inputs,
--       so we don't need to return a thinning/_⇑_
push-let :
  (Γ₁ Γ₂ : Ctx) (decl : Expr σ ⇑ (Γ₁ ++ Γ₂)) (body : Expr τ ⇑ (Γ₁ ++ (σ ∷ Γ₂))) →
  Expr τ ⇑ (Γ₁ ++ Γ₂)
push-let Γ₁ Γ₂ decl (Var ↑ θ)
  with Γ₁ ⊣ θ
...  | ⊣r ϕ₁ (ϕ₂ o') (p₁ , p₂) = Var ↑ {!ϕ₁ ++⊑ ϕ₂!}  -- just need to apply p₁ somehow
...  | ⊣r ϕ₁ (ϕ₂ os) (p₁ , p₂)
    with lemma-[x]≡ _ _ p₁
...    | refl , _ , _ = decl
push-let Γ₁ Γ₂ decl (App (pair (e₁ ↑ θ₁) (e₂ ↑ θ₂) c) ↑ θ) = {!!}  -- need to split (θ₁ ₒ θ) etc.
push-let Γ₁ Γ₂ decl (Lam (ψ \\ e) ↑ θ)
  with Γ₁ ⊣ θ
...  | ⊣r ϕ₁ ϕ₂ (refl , refl)
    with (_ ∷ []) ⊣ ϕ₂
... | ⊣r (oz o') ϕ₂ (refl , refl) =
    -- variable of the Lam is unused, this makes it easy
    map⇑ Let (decl ,R ((oz o' \\ (Lam (ψ \\ e))) ↑ (ϕ₁ ++⊑ ϕ₂)))
... | ⊣r (oz os) ϕ₂ (refl , refl) =
    map⇑ Let (decl ,R ((oz os \\ (Lam (ψ \\ rename-top _ _ _ e refl))) ↑ (ϕ₁ ++⊑ ϕ₂)))
push-let Γ₁ Γ₂ decl (Let x ↑ θ) = {!!}
push-let Γ₁ Γ₂ decl (Val v ↑ θ) = {!!}
push-let Γ₁ Γ₂ decl (Plus x ↑ θ) = {!!}
{-
push-let : {Γ₁ Γ₂ Γ : Ctx} (i : Ref σ Γ) → Expr σ Γ₁ → Expr τ Γ₂ → Cover Γ₁ (pop-at Γ₂ i) Γ → Expr τ Γ
push-let Top decl Var U = ?
push-let i decl (App u e₁ e₂) U = {!!}
push-let i decl (Lam e) U =
  ? -- Let live U decl (rename-top [] i (Lam e))
push-let i decl (Let b u e₁ e₂) U = {!!}
push-let i decl (Plus u e₁ e₂) U =
  {!!}
-}

-- TODO: continue

-- This is the same signature as for `Let live` itself.
push-let' : (Expr σ ×R ((σ ∷ []) ⊢ Expr τ)) Γ → Expr τ ⇑ Γ
push-let' (pair decl ((ψ \\ e) ↑ θ) cover) = push-let [] _ decl (e ↑ (ψ ++⊑ θ))

