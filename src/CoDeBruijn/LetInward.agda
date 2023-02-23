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
  (Γ₁ Γ₂ Γ₃ Γ₄ : Ctx) →
  ([] ≡ Γ₁ ++ Γ₂ ++ Γ₃ ++ Γ₄) →
  [] ≡ Γ₁ × [] ≡ Γ₂ × [] ≡ Γ₃ × [] ≡ Γ₄
lemma-[]≡++ Γ₁ Γ₂ Γ₃ Γ₄ p
  with refl ← ++-conicalˡ Γ₁ _ (sym p)
  with refl ← ++-conicalˡ Γ₂ _ (sym p)
  with refl ← ++-conicalˡ Γ₃ _ (sym p) =
  refl , refl , refl , p

-- This feels more convoluted than it should be.
lemma-[τ]≡++ :
  (Γ₁ Γ₂ Γ₃ Γ₄ : Ctx) →
  (τ ∷ [] ≡ Γ₁ ++ Γ₂ ++ Γ₃ ++ Γ₄) →
  (τ ∷ [] ≡ Γ₁ ++ Γ₃ ++ Γ₂ ++ Γ₄)
lemma-[τ]≡++ (_ ∷ Γ₁) Γ₂ Γ₃ Γ₄ p
  with refl , refl , refl , refl ← lemma-[]≡++ Γ₁ Γ₂ Γ₃ Γ₄ (∷-injectiveʳ p) = p
lemma-[τ]≡++ [] (_ ∷ Γ₂) Γ₃ Γ₄ p
  with refl , refl , refl , refl ← lemma-[]≡++ [] Γ₂ Γ₃ Γ₄ (∷-injectiveʳ p) = p
lemma-[τ]≡++ [] [] (_ ∷ Γ₃) Γ₄ p
  with refl , refl , refl , refl ← lemma-[]≡++ [] [] Γ₃ Γ₄ (∷-injectiveʳ p) = p
lemma-[τ]≡++ [] [] [] (_ ∷ Γ₄) p
  with refl , refl , refl , refl ← lemma-[]≡++ [] [] [] Γ₄ (∷-injectiveʳ p) = p

cover++⊑4 :
  {Γ₁ Γ₂ Γ₃ Γ₄ Γ₁' Γ₂' Γ₃' Γ₄' Γ₁'' Γ₂'' Γ₃'' Γ₄'' : Ctx} →
  (θ₁ : Γ₁'  ⊑ Γ₁) (θ₂ : Γ₂'  ⊑ Γ₂) (θ₃ : Γ₃'  ⊑ Γ₃) (θ₄ : Γ₄'  ⊑ Γ₄)
  (ϕ₁ : Γ₁'' ⊑ Γ₁) (ϕ₂ : Γ₂'' ⊑ Γ₂) (ϕ₃ : Γ₃'' ⊑ Γ₃) (ϕ₄ : Γ₄'' ⊑ Γ₄) →
  Cover (θ₁ ++⊑ θ₂ ++⊑ θ₃ ++⊑ θ₄) (ϕ₁ ++⊑ ϕ₂ ++⊑ ϕ₃ ++⊑ ϕ₄) →
  Cover (θ₁ ++⊑ θ₃ ++⊑ θ₂ ++⊑ θ₄) (ϕ₁ ++⊑ ϕ₃ ++⊑ ϕ₂ ++⊑ ϕ₄)
cover++⊑4 {Γ₁} θ₁ θ₂ θ₃ θ₄ ϕ₁ ϕ₂ ϕ₃ ϕ₄ c =
  let c₁ , c₂₃₄ = cover-split-++⊑ θ₁ ϕ₁ _ _ c
      c₂ , c₃₄  = cover-split-++⊑ θ₂ ϕ₂ _ _ c₂₃₄
      c₃ , c₄   = cover-split-++⊑ θ₃ ϕ₃ _ _ c₃₄
  in
  c₁ ++ᶜ c₃ ++ᶜ c₂ ++ᶜ c₄
  

coerce : {S : Scoped} {Γ' Γ : Ctx} → Γ ≡ Γ' → S Γ → S Γ'
coerce refl e = e

record ⊣R4 (Γ₁ Γ₂ Γ₃ Γ₄ : Ctx) (ψ : Γ ⊑ (Γ₁ ++ Γ₂ ++ Γ₃ ++ Γ₄)) : Set where
  constructor ⊣r4
  field
    {Γ₁'} : Ctx
    {Γ₂'} : Ctx
    {Γ₃'} : Ctx
    {Γ₄'} : Ctx
    ϕ₁ : Γ₁' ⊑ Γ₁
    ϕ₂ : Γ₂' ⊑ Γ₂
    ϕ₃ : Γ₃' ⊑ Γ₃
    ϕ₄ : Γ₄' ⊑ Γ₄
    H : Σ (Γ ≡ Γ₁' ++ Γ₂' ++ Γ₃' ++ Γ₄') λ { refl → ψ ≡ ϕ₁ ++⊑ ϕ₂ ++⊑ ϕ₃ ++⊑ ϕ₄ }

⊣4 : (Γ₁ Γ₂ Γ₃ Γ₄ : Ctx) (ψ : Γ ⊑ (Γ₁ ++ Γ₂ ++ Γ₃ ++ Γ₄)) → ⊣R4 Γ₁ Γ₂ Γ₃ Γ₄ ψ
⊣4 Γ₁ Γ₂ Γ₃ Γ₄ ψ
  with ⊣r {Γ₁'} {Γ₂₃₄'} ϕ₁ ϕ₂₃₄ (refl , refl) ← Γ₁ ⊣ ψ
  with ⊣r {Γ₂'} {Γ₃₄'}  ϕ₂ ϕ₃₄  (refl , refl) ← Γ₂ ⊣ ϕ₂₃₄
  with ⊣r {Γ₃'} {Γ₄'}   ϕ₃ ϕ₄   (refl , refl) ← Γ₃ ⊣ ϕ₃₄
  = ⊣r4 ϕ₁ ϕ₂ ϕ₃ ϕ₄ (refl , refl)

-- Could probably be refactored a bit to have less stuff in scope.
reorder-Ctx : (Γ₁ Γ₂ Γ₃ Γ₄ : Ctx) → Expr τ Γ → (Γ ≡ Γ₁ ++ Γ₂ ++ Γ₃ ++ Γ₄) → Expr τ (Γ₁ ++ Γ₃ ++ Γ₂ ++ Γ₄)
reorder-Ctx Γ₁ Γ₂ Γ₃ Γ₄ Var p =
  coerce {Expr _} (lemma-[τ]≡++ Γ₁ Γ₂ Γ₃ Γ₄ p) Var
reorder-Ctx Γ₁ Γ₂ Γ₃ Γ₄ (App (pair (e₁ ↑ θ) (e₂ ↑ ϕ) c)) refl
  with ⊣r4 {Γ₁'}  {Γ₂'}  {Γ₃'}  {Γ₄'}  θ₁ θ₂ θ₃ θ₄ (refl , refl) ← ⊣4 Γ₁ Γ₂ Γ₃ Γ₄ θ
  with ⊣r4 {Γ₁''} {Γ₂''} {Γ₃''} {Γ₄''} ϕ₁ ϕ₂ ϕ₃ ϕ₄ (refl , refl) ← ⊣4 Γ₁ Γ₂ Γ₃ Γ₄ ϕ =
  App (pair
         (reorder-Ctx Γ₁'  Γ₂'  Γ₃'  Γ₄'  e₁ refl ↑ (θ₁ ++⊑ θ₃ ++⊑ θ₂ ++⊑ θ₄))
         (reorder-Ctx Γ₁'' Γ₂'' Γ₃'' Γ₄'' e₂ refl ↑ (ϕ₁ ++⊑ ϕ₃ ++⊑ ϕ₂ ++⊑ ϕ₄))
         (cover++⊑4 θ₁ θ₂ θ₃ θ₄ ϕ₁ ϕ₂ ϕ₃ ϕ₄ c))
reorder-Ctx Γ₁ Γ₂ Γ₃ Γ₄ (Lam {σ} (_\\_ {Γ'} ψ e)) p =
  Lam (ψ \\ coerce {Expr _}
              (++-assoc Γ' Γ₁ _)
              (reorder-Ctx (Γ' ++ Γ₁) Γ₂ Γ₃ Γ₄ e (trans (cong (Γ' ++_) p) (sym (++-assoc Γ' Γ₁ _)))))
reorder-Ctx Γ₁ Γ₂ Γ₃ Γ₄ (Let (pair (e₁ ↑ θ) (_\\_ {Γ'} ψ e₂ ↑ ϕ) c)) refl
  with ⊣r4 {Γ₁'}  {Γ₂'}  {Γ₃'}  {Γ₄'}  θ₁ θ₂ θ₃ θ₄ (refl , refl) ← ⊣4 Γ₁ Γ₂ Γ₃ Γ₄ θ
  with ⊣r4 {Γ₁''} {Γ₂''} {Γ₃''} {Γ₄''} ϕ₁ ϕ₂ ϕ₃ ϕ₄ (refl , refl) ← ⊣4 Γ₁ Γ₂ Γ₃ Γ₄ ϕ =
  Let (pair
         (reorder-Ctx Γ₁' Γ₂' Γ₃' Γ₄' e₁ refl ↑ (θ₁ ++⊑ θ₃ ++⊑ θ₂ ++⊑ θ₄))
         ((ψ \\ coerce {Expr _}
                  (++-assoc Γ' Γ₁'' _)
                  (reorder-Ctx (Γ' ++ Γ₁'') Γ₂'' Γ₃'' Γ₄'' e₂ (sym (++-assoc Γ' Γ₁'' _))))
           ↑ (ϕ₁ ++⊑ ϕ₃ ++⊑ ϕ₂ ++⊑ ϕ₄))
         (cover++⊑4 θ₁ θ₂ θ₃ θ₄ ϕ₁ ϕ₂ ϕ₃ ϕ₄ c))
reorder-Ctx Γ₁ Γ₂ Γ₃ Γ₄ (Val v) p
  with refl , refl , refl , refl ← lemma-[]≡++ Γ₁ Γ₂ Γ₃ Γ₄ p =
  Val v
reorder-Ctx Γ₁ Γ₂ Γ₃ Γ₄ (Plus (pair (e₁ ↑ θ) (e₂ ↑ ϕ) c)) refl
  with ⊣r4 {Γ₁'}  {Γ₂'}  {Γ₃'}  {Γ₄'}  θ₁ θ₂ θ₃ θ₄ (refl , refl) ← ⊣4 Γ₁ Γ₂ Γ₃ Γ₄ θ
  with ⊣r4 {Γ₁''} {Γ₂''} {Γ₃''} {Γ₄''} ϕ₁ ϕ₂ ϕ₃ ϕ₄ (refl , refl) ← ⊣4 Γ₁ Γ₂ Γ₃ Γ₄ ϕ =
  Plus (pair
         (reorder-Ctx Γ₁'  Γ₂'  Γ₃'  Γ₄'  e₁ refl ↑ (θ₁ ++⊑ θ₃ ++⊑ θ₂ ++⊑ θ₄))
         (reorder-Ctx Γ₁'' Γ₂'' Γ₃'' Γ₄'' e₂ refl ↑ (ϕ₁ ++⊑ ϕ₃ ++⊑ ϕ₂ ++⊑ ϕ₄))
         (cover++⊑4 θ₁ θ₂ θ₃ θ₄ ϕ₁ ϕ₂ ϕ₃ ϕ₄ c))

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
push-let Γ₁ Γ₂ decl (App (pair (e₁ ↑ θ) (e₂ ↑ ϕ) c) ↑ ψ)
  with Γ₁ ⊣ (θ ₒ ψ)                      | Γ₁ ⊣ (ϕ ₒ ψ)  -- might have to do some Γ' ⊣ θ, so first Γ ⊣ ψ only? :/
... | ⊣r {Γ₁'} {Γ₂'} θ₁ (θ₂ o') (refl , p) | ⊣r {Γ₁''} {Γ₂''} ϕ₁ (ϕ₂ o') (refl , p') =
  App (pair (e₁ ↑ (θ₁ ++⊑ θ₂)) (e₂ ↑ (ϕ₁ ++⊑ ϕ₂)) {!c!}) ↑ oi
... | ⊣r {Γ₁'} {Γ₂'} θ₁ (θ₂ o') (refl , p) | ⊣r {Γ₁''} {.(_ ∷ _)} ϕ₁ (ϕ₂ os) (refl , p') = {!!}
... | ⊣r {Γ₁'} {.(_ ∷ _)} θ₁ (θ₂ os) (refl , p) | ⊣r {Γ₁''} {Γ₂''} ϕ₁ (ϕ₂ o') (refl , p') = {!!}
... | ⊣r {Γ₁'} {.(_ ∷ _)} θ₁ (θ₂ os) (refl , p) | ⊣r {Γ₁''} {.(_ ∷ _)} ϕ₁ (ϕ₂ os) (refl , p') = {!!}
  {-
  let e₁' = push-let {!!} {!!} decl {!e₁!}
  in
  -}

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

