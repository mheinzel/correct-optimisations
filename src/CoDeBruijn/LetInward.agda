-- Let Floating (inwards) using co-de-Bruijn representation
--
-- Push the let-binding inwards as far as possible without
-- - duplicating it
-- - pushing it into a lambda
module CoDeBruijn.LetInward where

open import Data.Nat using (_+_)
open import Data.List using (List ; _∷_ ; [] ; _++_)
open import Data.List.Properties using (++-assoc ; ∷-injective ; ∷-injectiveˡ ; ∷-injectiveʳ ; ++-conicalˡ)
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
lemma-[x]≡ (x ∷ y ∷ Γ₁) Γ₂ p | _ , ()

lemma-[]≡++ :
  (Γ₀ Γ₁ Γ₂ Γ₃ : Ctx) →
  ([] ≡ Γ₀ ++ Γ₁ ++ Γ₂ ++ Γ₃) →
  [] ≡ Γ₀ × [] ≡ Γ₁ × [] ≡ Γ₂ × [] ≡ Γ₃
lemma-[]≡++ Γ₀ Γ₁ Γ₂ Γ₃ p
  with refl ← ++-conicalˡ Γ₀ _ (sym p)
  with refl ← ++-conicalˡ Γ₁ _ (sym p)
  with refl ← ++-conicalˡ Γ₂ _ (sym p) =
  refl , refl , refl , p

-- This feels more convoluted than it should be.
lemma-[τ]≡++ :
  (Γ₀ Γ₁ Γ₂ Γ₃ : Ctx) →
  (τ ∷ [] ≡ Γ₀ ++ Γ₁ ++ Γ₂ ++ Γ₃) →
  (τ ∷ [] ≡ Γ₀ ++ Γ₂ ++ Γ₁ ++ Γ₃)
lemma-[τ]≡++ (_ ∷ Γ₀) Γ₁ Γ₂ Γ₃ p
  with refl , refl , refl , refl ← lemma-[]≡++ Γ₀ Γ₁ Γ₂ Γ₃ (∷-injectiveʳ p) = p
lemma-[τ]≡++ [] (_ ∷ Γ₁) Γ₂ Γ₃ p
  with refl , refl , refl , refl ← lemma-[]≡++ [] Γ₁ Γ₂ Γ₃ (∷-injectiveʳ p) = p
lemma-[τ]≡++ [] [] (_ ∷ Γ₂) Γ₃ p
  with refl , refl , refl , refl ← lemma-[]≡++ [] [] Γ₂ Γ₃ (∷-injectiveʳ p) = p
lemma-[τ]≡++ [] [] [] (_ ∷ Γ₃) p
  with refl , refl , refl , refl ← lemma-[]≡++ [] [] [] Γ₃ (∷-injectiveʳ p) = p

coerce : {S : Scoped} {Γ' Γ : Ctx} → Γ ≡ Γ' → S Γ → S Γ'
coerce refl e = e

reorder-Ctx : (Γ₀ Γ₁ Γ₂ Γ₃ : Ctx) → Expr τ Γ → (Γ ≡ Γ₀ ++ Γ₁ ++ Γ₂ ++ Γ₃) → Expr τ (Γ₀ ++ Γ₂ ++ Γ₁ ++ Γ₃)
reorder-Ctx Γ₀ Γ₁ Γ₂ Γ₃ Var p =
  coerce {Expr _} (lemma-[τ]≡++ Γ₀ Γ₁ Γ₂ Γ₃ p) Var
reorder-Ctx Γ₀ Γ₁ Γ₂ Γ₃ (App (pair (e₁ ↑ θ₁) (e₂ ↑ θ₂) c)) p =
  App (pair ({!reorder-Ctx!} ↑ {!!}) {!!} {!!})
reorder-Ctx Γ₀ Γ₁ Γ₂ Γ₃ (Lam {σ} (_\\_ {Γ'} ψ e)) p =
  Lam (ψ \\ coerce {Expr _}
              (++-assoc Γ' Γ₀ _)
              (reorder-Ctx (Γ' ++ Γ₀) Γ₁ Γ₂ Γ₃ e (trans (cong (Γ' ++_) p) (sym (++-assoc Γ' Γ₀ _)))))
reorder-Ctx Γ₀ Γ₁ Γ₂ Γ₃ (Let x) p = {!!}
reorder-Ctx Γ₀ Γ₁ Γ₂ Γ₃ (Val v) p = {!!}
reorder-Ctx Γ₀ Γ₁ Γ₂ Γ₃ (Plus x) p = {!!}

-- TODO: The might be a better specification for this?
--       Ideally we would also require some kind of Cover-condition on the inputs,
--       so we don't need to return a thinning/_⇑_
push-let :
  (Γ₁ Γ₂ : Ctx) (decl : Expr σ ⇑ (Γ₁ ++ Γ₂)) (body : Expr τ ⇑ (Γ₁ ++ (σ ∷ Γ₂))) →
  Expr τ ⇑ (Γ₁ ++ Γ₂)
push-let Γ₁ Γ₂ decl (Var ↑ θ)
  with Γ₁ ⊣ θ
...  | ⊣r ϕ₁ (ϕ₂ o') (p₁ , p₂) = Var ↑ coerce {_⊑ (Γ₁ ++ Γ₂)} (sym p₁) (ϕ₁ ++⊑ ϕ₂)
...  | ⊣r ϕ₁ (ϕ₂ os) (p₁ , p₂) with refl , _ , _ ← lemma-[x]≡ _ _ p₁ = decl
push-let Γ₁ Γ₂ decl (App (pair (e₁ ↑ θ₁) (e₂ ↑ θ₂) c) ↑ θ) = {!!}  -- need to split (θ₁ ₒ θ) etc.

push-let Γ₁ Γ₂ decl (Lam (_\\_ {Γ'} ψ e) ↑ θ)
  with Γ₁ ⊣ θ
...  | ⊣r {Γ₁'} ϕ₁ ϕ₂ (refl , refl)
    with (_ ∷ []) ⊣ ϕ₂
... | ⊣r {Γ₁''} {Γ₂'} ψ' ϕ₂ (refl , refl) =
    -- We could avoid calling reorder-Ctx if Γ₁'' is [], but that just introduces more cases.
    map⇑ Let (decl ,R ((ψ' \\ (Lam (ψ \\ reorder-Ctx Γ' Γ₁' Γ₁'' Γ₂' e refl))) ↑ (ϕ₁ ++⊑ ϕ₂)))

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

