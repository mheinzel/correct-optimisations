-- Let Floating (inwards) using co-de-Bruijn representation
--
-- Push the let-binding inwards as far as possible without
-- - duplicating it
-- - pushing it into a lambda
module CoDeBruijn.LetInward where

open import Data.Nat using (_+_)
open import Data.List using (List ; _∷_ ; [] ; _++_)
open import Data.List.Properties using (++-assoc ; ∷-injective ; ∷-injectiveˡ ; ∷-injectiveʳ ; ++-conicalˡ ; ++-conicalʳ)
open import Data.Unit
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; cong₂ ; sym ; trans)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Function using (_$_)

open import Core
open import CoDeBruijn.Lang
open import OPE

-- TODO: with all the thinning and contexts in scope, I should make the naming scheme more consistent.
-- (θ/ϕ/ψ₁₂ˡʳ'')

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

law-cover++⊑4-Γ₂≡[] :
  {Γ₁ Γ₃ Γ₄ Γ₁' Γ₃' Γ₄' Γ₁'' Γ₃'' Γ₄'' : Ctx} →
  (θ₁ : Γ₁'  ⊑ Γ₁) (θ₃ : Γ₃'  ⊑ Γ₃) (θ₄ : Γ₄'  ⊑ Γ₄)
  (ϕ₁ : Γ₁'' ⊑ Γ₁) (ϕ₃ : Γ₃'' ⊑ Γ₃) (ϕ₄ : Γ₄'' ⊑ Γ₄) →
  (c : Cover (θ₁ ++⊑ oz ++⊑ θ₃ ++⊑ θ₄) (ϕ₁ ++⊑ oz ++⊑ ϕ₃ ++⊑ ϕ₄)) →
  cover++⊑4 θ₁ oz θ₃ θ₄ ϕ₁ oz ϕ₃ ϕ₄ c ≡ c
law-cover++⊑4-Γ₂≡[] {Γ₁} θ₁ θ₃ θ₄ ϕ₁ ϕ₃ ϕ₄ c =
  let c₁ , c₃₄ = cover-split-++⊑ θ₁ ϕ₁ _ _ c
      c₃ , c₄  = cover-split-++⊑ θ₃ ϕ₃ _ _ c₃₄
  in
    c₁ ++ᶜ c₃ ++ᶜ c₄
  ≡⟨ cong (c₁ ++ᶜ_) (law-cover-split-++⊑ θ₃ ϕ₃ _ _ c₃₄) ⟩
    c₁ ++ᶜ c₃₄
  ≡⟨ law-cover-split-++⊑ θ₁ ϕ₁ _ _ c ⟩
    c
  ∎
  
coerce : {S : Scoped} {Γ' Γ : Ctx} → Γ ≡ Γ' → S Γ → S Γ'
coerce refl e = e

-- To factor out the repeated calling of ⊣, packaging up the results in a convenient way.
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

Reorder : Scoped → Set
Reorder T = ∀ {Γ} (Γ₁ Γ₂ Γ₃ Γ₄ : Ctx) → T Γ → (Γ ≡ Γ₁ ++ Γ₂ ++ Γ₃ ++ Γ₄) → T (Γ₁ ++ Γ₃ ++ Γ₂ ++ Γ₄)

mutual
  reorder-Ctx-×R : Reorder (Expr σ ×R Expr τ)
  reorder-Ctx-×R Γ₁ Γ₂ Γ₃ Γ₄ (pair (e₁ ↑ θ) (e₂ ↑ ϕ) c) refl
    with ⊣r4 {Γ₁'}  {Γ₂'}  {Γ₃'}  {Γ₄'}  θ₁ θ₂ θ₃ θ₄ (refl , refl) ← ⊣4 Γ₁ Γ₂ Γ₃ Γ₄ θ
    with ⊣r4 {Γ₁''} {Γ₂''} {Γ₃''} {Γ₄''} ϕ₁ ϕ₂ ϕ₃ ϕ₄ (refl , refl) ← ⊣4 Γ₁ Γ₂ Γ₃ Γ₄ ϕ =
    pair
      (reorder-Ctx Γ₁'  Γ₂'  Γ₃'  Γ₄'  e₁ refl ↑ (θ₁ ++⊑ θ₃ ++⊑ θ₂ ++⊑ θ₄))
      (reorder-Ctx Γ₁'' Γ₂'' Γ₃'' Γ₄'' e₂ refl ↑ (ϕ₁ ++⊑ ϕ₃ ++⊑ ϕ₂ ++⊑ ϕ₄))
      (cover++⊑4 θ₁ θ₂ θ₃ θ₄ ϕ₁ ϕ₂ ϕ₃ ϕ₄ c)

  reorder-Ctx-⊢ : ∀ {Γ'} → Reorder (Γ' ⊢ Expr τ)
  reorder-Ctx-⊢ Γ₁ Γ₂ Γ₃ Γ₄ (_\\_ {Γ''} ψ e) p =
    ψ \\ coerce {Expr _}
           (++-assoc Γ'' Γ₁ _)
           (reorder-Ctx (Γ'' ++ Γ₁) Γ₂ Γ₃ Γ₄ e (trans (cong (Γ'' ++_) p) (sym (++-assoc Γ'' Γ₁ _))))
  
  -- It would be nice to compose the Let case from our helpers above, but it's complicated.
  reorder-Ctx : Reorder (Expr τ)
  reorder-Ctx Γ₁ Γ₂ Γ₃ Γ₄ Var p =
    coerce {Expr _} (lemma-[τ]≡++ Γ₁ Γ₂ Γ₃ Γ₄ p) Var
  reorder-Ctx Γ₁ Γ₂ Γ₃ Γ₄ (App p) q = App (reorder-Ctx-×R Γ₁ Γ₂ Γ₃ Γ₄ p q)
  reorder-Ctx Γ₁ Γ₂ Γ₃ Γ₄ (Lam l) p = Lam (reorder-Ctx-⊢ Γ₁ Γ₂ Γ₃ Γ₄ l p)
  reorder-Ctx Γ₁ Γ₂ Γ₃ Γ₄ (Let (pair (e₁ ↑ θ) (l ↑ ϕ) c)) refl
    with ⊣r4 {Γ₁'}  {Γ₂'}  {Γ₃'}  {Γ₄'}  θ₁ θ₂ θ₃ θ₄ (refl , refl) ← ⊣4 Γ₁ Γ₂ Γ₃ Γ₄ θ
    with ⊣r4 {Γ₁''} {Γ₂''} {Γ₃''} {Γ₄''} ϕ₁ ϕ₂ ϕ₃ ϕ₄ (refl , refl) ← ⊣4 Γ₁ Γ₂ Γ₃ Γ₄ ϕ =
    Let (pair
           (reorder-Ctx Γ₁' Γ₂' Γ₃' Γ₄' e₁ refl ↑ (θ₁ ++⊑ θ₃ ++⊑ θ₂ ++⊑ θ₄))
           (reorder-Ctx-⊢ Γ₁'' Γ₂'' Γ₃'' Γ₄'' l refl ↑ (ϕ₁ ++⊑ ϕ₃ ++⊑ ϕ₂ ++⊑ ϕ₄))
           (cover++⊑4 θ₁ θ₂ θ₃ θ₄ ϕ₁ ϕ₂ ϕ₃ ϕ₄ c))
  reorder-Ctx Γ₁ Γ₂ Γ₃ Γ₄ (Val v) p
    with refl , refl , refl , refl ← lemma-[]≡++ Γ₁ Γ₂ Γ₃ Γ₄ p =
    Val v
  reorder-Ctx Γ₁ Γ₂ Γ₃ Γ₄ (Plus p) q = Plus (reorder-Ctx-×R Γ₁ Γ₂ Γ₃ Γ₄ p q)

cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {x y u v s t} → x ≡ y → u ≡ v → s ≡ t → f x u s ≡ f y v t
cong₃ f refl refl refl = refl

-- TODO: follows from law-reorder-Ctx?
law-reorder-Ctx-Γ₂≡[] : 
  (Γ₁ Γ₃ Γ₄ : Ctx) (e : Expr τ Γ) (p : Γ ≡ Γ₁ ++ Γ₃ ++ Γ₄) →
  reorder-Ctx Γ₁ [] Γ₃ Γ₄ e p ≡ coerce {Expr τ} p e  -- TODO: this is gonna be annoying, isn't it?
law-reorder-Ctx-Γ₂≡[] Γ₁ Γ₃ Γ₄ Var p = {!!}
law-reorder-Ctx-Γ₂≡[] Γ₁ Γ₃ Γ₄ (App (pair (e₁ ↑ θ) (e₂ ↑ ϕ) c)) refl
  with ⊣r4 {Γ₁'}  {[]}  {Γ₃'}  {Γ₄'} θ₁ oz θ₃ θ₄ (refl , refl) ← ⊣4 Γ₁ [] Γ₃ Γ₄ θ
  with ⊣r4 {Γ₁''} {[]} {Γ₃''} {Γ₄''} ϕ₁ oz ϕ₃ ϕ₄ (refl , refl) ← ⊣4 Γ₁ [] Γ₃ Γ₄ ϕ =
  cong App
    (cong₃ (λ x y z → pair (x ↑ _) (y ↑ _) z)
      (law-reorder-Ctx-Γ₂≡[] Γ₁'  Γ₃'  Γ₄'  e₁ refl)
      (law-reorder-Ctx-Γ₂≡[] Γ₁'' Γ₃'' Γ₄'' e₂ refl)
      (law-cover++⊑4-Γ₂≡[] θ₁ θ₃ θ₄ ϕ₁ ϕ₃ ϕ₄ c))
law-reorder-Ctx-Γ₂≡[] Γ₁ Γ₃ Γ₄ (Lam x) p = {!!}
law-reorder-Ctx-Γ₂≡[] Γ₁ Γ₃ Γ₄ (Let x) p = {!!}
law-reorder-Ctx-Γ₂≡[] Γ₁ Γ₃ Γ₄ (Val v) p = {!!}
law-reorder-Ctx-Γ₂≡[] Γ₁ Γ₃ Γ₄ (Plus x) p = {!!}

-- Here we know up front how the body's Ctx is split, and also ensure that the binding is used.
-- We return a thinned value, but we could probably make it return an Expr τ Γ directly,
-- if we show a few things about covers and require a Cover (_⇑_.thinning decl) θ.
push-let :
  ∀ {Γ' Γ σ} (Γ₁ Γ₂ : Ctx)
  (decl : Expr σ ⇑ Γ) (body : Expr τ Γ') (θ : (Γ₁ ++ Γ₂) ⊑ Γ) (p : Γ' ≡ Γ₁ ++ σ ∷ Γ₂) →
  Expr τ ⇑ Γ

push-let Γ₁ Γ₂ decl Var θ p with Γ₁
push-let Γ₁ Γ₂ decl Var θ p    | (_ ∷ Γ₁') with () ← ++-conicalʳ Γ₁' _ (sym (∷-injectiveʳ p))
push-let Γ₁ Γ₂ decl Var θ refl | [] = decl -- The declaration must be live, so we know the variable references it.

push-let Γ₁ Γ₂ decl (App (pair (e₁ ↑ θ) (e₂ ↑ ϕ) c)) ψ refl
  with Γ₁ ⊣ θ | Γ₁ ⊣ ϕ
  -- Let not used at all (should be impossible, but tricky to show!)
...  | ⊣r θ₁ (θ₂ o') (refl , refl) | ⊣r ϕ₁ (ϕ₂ o') (refl , refl) =
  map⇑ App ((e₁ ↑ ((θ₁ ++⊑ θ₂) ₒ ψ)) ,R (e₂ ↑ ((ϕ₁ ++⊑ ϕ₂) ₒ ψ)))
  -- Let used in right subexpression
...  | ⊣r θ₁ (θ₂ o') (refl , refl) | ⊣r {Γ₁'} {_ ∷ Γ₂'} ϕ₁ (ϕ₂ os) (refl , refl) =
                                        -- Here, we should also be able to work in a smaller context, then thin⇑.
                                        -- Parts of Γ might neither be free in decl nor e₂.
                                        -- This is necessary if we want to pass down a cover.
  map⇑ App ((e₁ ↑ ((θ₁ ++⊑ θ₂) ₒ ψ)) ,R push-let Γ₁' Γ₂' decl e₂ ((ϕ₁ ++⊑ ϕ₂) ₒ ψ) refl)
  -- Let used in left subexpression
...  | ⊣r {Γ₁'} {_ ∷ Γ₂'} θ₁ (θ₂ os) (refl , refl) | ⊣r ϕ₁ (ϕ₂ o') (refl , refl) =
  map⇑ App (push-let Γ₁' Γ₂' decl e₁ ((θ₁ ++⊑ θ₂) ₒ ψ) refl ,R (e₂ ↑ ((ϕ₁ ++⊑ ϕ₂) ₒ ψ)))
  -- Let used in both subexpressions
...  | ⊣r θ₁ (θ₂ os) (refl , refl) | ⊣r ϕ₁ (ϕ₂ os) (refl , refl) =
  map⇑ App (push-let _ _ decl e₁ ((θ₁ ++⊑ θ₂) ₒ ψ) refl ,R push-let _ _ decl e₂ ((ϕ₁ ++⊑ ϕ₂) ₒ ψ) refl)

push-let Γ₁ Γ₂ decl (Lam (_\\_ {Γ'} ψ e)) θ refl = -- don't push into lambdas!
  -- If we had the cover, we could just do this:
  -- Let (pair decl (((oz os) \\ (Lam (ψ \\ reorder-Ctx Γ' Γ₁ (_ ∷ []) Γ₂ e refl))) ↑ θ) cover) ↑ oi
  map⇑ Let (decl ,R (((oz os) \\ (Lam (ψ \\ reorder-Ctx Γ' Γ₁ (_ ∷ []) Γ₂ e refl))) ↑ θ))

push-let Γ₁ Γ₂ decl (Let (pair (e₁ ↑ θ) (_\\_ {Γ''} ψ' e₂ ↑ ϕ) c)) ψ refl
  with Γ₁ ⊣ θ | Γ₁ ⊣ ϕ
  -- Let not used at all (should be impossible, but tricky to show!)
...  | ⊣r θ₁ (θ₂ o') (refl , refl) | ⊣r ϕ₁ (ϕ₂ o') (refl , refl) =
  map⇑ Let ((e₁ ↑ ((θ₁ ++⊑ θ₂) ₒ ψ)) ,R ((ψ' \\ e₂) ↑ ((ϕ₁ ++⊑ ϕ₂) ₒ ψ)))
  -- Let used in right subexpression
...  | ⊣r θ₁ (θ₂ o') (refl , refl) | ⊣r {Γ₁'} {_ ∷ Γ₂'} ϕ₁ (ϕ₂ os) (refl , refl)
    with e₂' ↑ ϕ' ← push-let (Γ'' ++ Γ₁') Γ₂' (thin⇑ (oe {Γ''} ++⊑ oi) decl) e₂
                      (coerce {_⊑ (Γ'' ++ _)} (sym (++-assoc Γ'' Γ₁' Γ₂')) (oi {Γ''} ++⊑ ((ϕ₁ ++⊑ ϕ₂) ₒ ψ)))
                      (sym (++-assoc Γ'' Γ₁' (_ ∷ Γ₂')))
    with ⊣r ψ'' ϕ'' (refl , b) ← Γ'' ⊣ ϕ' =
    map⇑ Let ((e₁ ↑ ((θ₁ ++⊑ θ₂) ₒ ψ)) ,R (((ψ'' ₒ ψ') \\ e₂') ↑ ϕ''))
  -- Let used in left subexpression
...  | ⊣r {Γ₁'} {_ ∷ Γ₂'} θ₁ (θ₂ os) (refl , refl) | ⊣r ϕ₁ (ϕ₂ o') (refl , refl) =
  map⇑ Let (push-let Γ₁' Γ₂' decl e₁ ((θ₁ ++⊑ θ₂) ₒ ψ) refl ,R ((ψ' \\ e₂) ↑ ((ϕ₁ ++⊑ ϕ₂) ₒ ψ)))
  -- Let used in both subexpressions
...  | ⊣r θ₁ (θ₂ os) (refl , refl) | ⊣r {Γ₁'} {_ ∷ Γ₂'} ϕ₁ (ϕ₂ os) (refl , refl)
    with e₂' ↑ ϕ' ← push-let (Γ'' ++ Γ₁') Γ₂' (thin⇑ (oe {Γ''} ++⊑ oi) decl) e₂
                      (coerce {_⊑ (Γ'' ++ _)} (sym (++-assoc Γ'' Γ₁' Γ₂')) (oi {Γ''} ++⊑ ((ϕ₁ ++⊑ ϕ₂) ₒ ψ)))
                      (sym (++-assoc Γ'' Γ₁' (_ ∷ Γ₂')))
    with ⊣r ψ'' ϕ'' (refl , b) ← Γ'' ⊣ ϕ' =
    map⇑ Let (push-let _ _ decl e₁ ((θ₁ ++⊑ θ₂) ₒ ψ) refl ,R (((ψ'' ₒ ψ') \\ e₂') ↑ ϕ''))

push-let Γ₁ Γ₂ decl (Val v) θ p =
  (Val v) ↑ oe

push-let Γ₁ Γ₂ decl (Plus (pair (e₁ ↑ θ) (e₂ ↑ ϕ) c)) ψ refl
  with Γ₁ ⊣ θ | Γ₁ ⊣ ϕ
  -- Let not used at all (should be impossible, but tricky to show!)
...  | ⊣r θ₁ (θ₂ o') (refl , refl) | ⊣r ϕ₁ (ϕ₂ o') (refl , refl) =
  map⇑ Plus ((e₁ ↑ ((θ₁ ++⊑ θ₂) ₒ ψ)) ,R (e₂ ↑ ((ϕ₁ ++⊑ ϕ₂) ₒ ψ)))
  -- Let used in right subexpression
...  | ⊣r θ₁ (θ₂ o') (refl , refl) | ⊣r {Γ₁'} {_ ∷ Γ₂'} ϕ₁ (ϕ₂ os) (refl , refl) =
  map⇑ Plus ((e₁ ↑ ((θ₁ ++⊑ θ₂) ₒ ψ)) ,R push-let Γ₁' Γ₂' decl e₂ ((ϕ₁ ++⊑ ϕ₂) ₒ ψ) refl)
  -- Let used in left subexpression
...  | ⊣r {Γ₁'} {_ ∷ Γ₂'} θ₁ (θ₂ os) (refl , refl) | ⊣r ϕ₁ (ϕ₂ o') (refl , refl) =
  map⇑ Plus (push-let Γ₁' Γ₂' decl e₁ ((θ₁ ++⊑ θ₂) ₒ ψ) refl ,R (e₂ ↑ ((ϕ₁ ++⊑ ϕ₂) ₒ ψ)))
  -- Let used in both subexpressions
...  | ⊣r θ₁ (θ₂ os) (refl , refl) | ⊣r ϕ₁ (ϕ₂ os) (refl , refl) =
  map⇑ Plus (push-let _ _ decl e₁ ((θ₁ ++⊑ θ₂) ₒ ψ) refl ,R push-let _ _ decl e₂ ((ϕ₁ ++⊑ ϕ₂) ₒ ψ) refl)

-- This is the same signature as for `Let live` itself, just with a thinning so we can drop the Let.
-- (in case it was dead)
push-let-top : (Expr σ ×R ((σ ∷ []) ⊢ Expr τ)) Γ → Expr τ ⇑ Γ
push-let-top (pair (decl ↑ ϕ) ((oz os \\ e) ↑ θ) c) =
  push-let [] _ (decl ↑ ϕ) e θ refl
push-let-top (pair decl ((oz o' \\ e) ↑ θ) c) =
  e ↑ θ   -- binding is unused, why bother?

eval⇑ : Expr τ ⇑ Γ → Env Γ → ⟦ τ ⟧
eval⇑ x env = let (e ↑ θ) = x in eval e θ env

mutual
  law-eval-reorder-Ctx-×R :
    ∀ {τ₁ τ₂} (binop : ⟦ τ₁ ⟧ → ⟦ τ₂ ⟧ → ⟦ τ ⟧)
    (Γ₁ Γ₂ Γ₃ Γ₄ : Ctx) (e : (Expr τ₁ ×R Expr τ₂) Γ) (p : Γ ≡ Γ₁ ++ Γ₂ ++ Γ₃ ++ Γ₄)
    (env₁ : Env Γ₁) (env₂ : Env Γ₂) (env₃ : Env Γ₃) (env₄ : Env Γ₄) →
      eval-binop binop (reorder-Ctx-×R Γ₁ Γ₂ Γ₃ Γ₄ e p) oi (env₁ ++ᴱ env₃ ++ᴱ env₂ ++ᴱ env₄)
    ≡ eval-binop binop (coerce {Expr τ₁ ×R Expr τ₂} p e) oi (env₁ ++ᴱ env₂ ++ᴱ env₃ ++ᴱ env₄)
  law-eval-reorder-Ctx-×R binop Γ₁ Γ₂ Γ₃ Γ₄ (pair (e₁ ↑ θ) (e₂ ↑ ϕ) c) refl env₁ env₂ env₃ env₄
    with ⊣r4 {Γ₁'}  {Γ₂'}  {Γ₃'}  {Γ₄'}  θ₁ θ₂ θ₃ θ₄ (refl , refl) ← ⊣4 Γ₁ Γ₂ Γ₃ Γ₄ θ
    with ⊣r4 {Γ₁''} {Γ₂''} {Γ₃''} {Γ₄''} ϕ₁ ϕ₂ ϕ₃ ϕ₄ (refl , refl) ← ⊣4 Γ₁ Γ₂ Γ₃ Γ₄ ϕ =
    let h₁ = law-eval-reorder-Ctx Γ₁' Γ₂' Γ₃' Γ₄' e₁ refl
    in
    {!h₁!}
    
  -- TODO: need to generalise?
  -- - Env Γ₁ with Γ₁' ⊑ Γ
  -- - or use law about projectEnv (θ ++⊑ ϕ) (env₁ ++ᴱ env₂)
  law-eval-reorder-Ctx :
    (Γ₁ Γ₂ Γ₃ Γ₄ : Ctx) (e : Expr τ Γ) (p : Γ ≡ Γ₁ ++ Γ₂ ++ Γ₃ ++ Γ₄)
    (env₁ : Env Γ₁) (env₂ : Env Γ₂) (env₃ : Env Γ₃) (env₄ : Env Γ₄) →
      eval (reorder-Ctx Γ₁ Γ₂ Γ₃ Γ₄ e p) oi (env₁ ++ᴱ env₃ ++ᴱ env₂ ++ᴱ env₄)
    ≡ eval (coerce {Expr _} p e) oi (env₁ ++ᴱ env₂ ++ᴱ env₃ ++ᴱ env₄)
  law-eval-reorder-Ctx Γ₁ Γ₂ Γ₃ Γ₄ Var p env₁ env₂ env₃ env₄ =
    {!!}  -- trivial, but painful
  law-eval-reorder-Ctx Γ₁ Γ₂ Γ₃ Γ₄ (App x) refl env₁ env₂ env₃ env₄ =
    law-eval-reorder-Ctx-×R _$_ Γ₁ Γ₂ Γ₃ Γ₄ x refl env₁ env₂ env₃ env₄
  law-eval-reorder-Ctx Γ₁ Γ₂ Γ₃ Γ₄ (Lam x) p env₁ env₂ env₃ env₄ = {!!}
  law-eval-reorder-Ctx Γ₁ Γ₂ Γ₃ Γ₄ (Let x) p env₁ env₂ env₃ env₄ = {!!}
  law-eval-reorder-Ctx Γ₁ Γ₂ Γ₃ Γ₄ (Val v) p env₁ env₂ env₃ env₄ = {!!}
  law-eval-reorder-Ctx Γ₁ Γ₂ Γ₃ Γ₄ (Plus x) refl env₁ env₂ env₃ env₄ =
    law-eval-reorder-Ctx-×R _+_ Γ₁ Γ₂ Γ₃ Γ₄ x refl env₁ env₂ env₃ env₄

law-eval-reorder-Ctx-[] :
  ∀ {σ τ} Γ₁ Γ₂ (e : Expr τ Γ) (p : Γ ≡ Γ₁ ++ σ ∷ Γ₂) (v : ⟦ σ ⟧) (env₁ : Env Γ₁) (env₂ : Env Γ₂) →
    eval (reorder-Ctx [] Γ₁ (σ ∷ []) Γ₂ e p) oi (Cons v (env₁ ++ᴱ env₂))
  ≡ eval (coerce {Expr _} p e) oi (env₁ ++ᴱ Cons v env₂)
law-eval-reorder-Ctx-[] Γ₁ Γ₂ Var p v env₁ env₂ with lemma-[]≡++ [] Γ₁ (_ ∷ []) Γ₂ {!!}
... | p' = {!!}
law-eval-reorder-Ctx-[] Γ₁ Γ₂ (App x) p v env₁ env₂ = {!!}
law-eval-reorder-Ctx-[] Γ₁ Γ₂ (Lam x) p v env₁ env₂ = {!!}
law-eval-reorder-Ctx-[] Γ₁ Γ₂ (Let x) p v env₁ env₂ = {!!}
law-eval-reorder-Ctx-[] Γ₁ Γ₂ (Val v₁) p v env₁ env₂ = {!!}
law-eval-reorder-Ctx-[] Γ₁ Γ₂ (Plus x) p v env₁ env₂ = {!!}


-- TODO: Might have to make more general to make it useful as IH.
-- TODO: What to do about the cover? :/
-- - use _,R_ which introduces another context and thinning, or
-- - demand a cover as an input and manage to adapt it for passing down
push-let-correct :
  ∀ {Γ' Γ σ} (Γ₁ Γ₂ : Ctx)
  (decl : Expr σ ⇑ Γ) (e : Expr τ Γ') (θ : (Γ₁ ++ Γ₂) ⊑ Γ) (p : Γ' ≡ Γ₁ ++ σ ∷ Γ₂) →
  (env : Env Γ) →
    eval⇑ (push-let Γ₁ Γ₂ decl e θ p) env
  ≡ eval (Let (pair decl (((oz os) \\ (reorder-Ctx [] Γ₁ (σ ∷ []) Γ₂ e p)) ↑ θ) {!!})) oi env

push-let-correct Γ₁ Γ₂ decl    Var θ p env with Γ₁
push-let-correct Γ₁ Γ₂ decl    Var θ p env    | (_ ∷ Γ₁') with () ← ++-conicalʳ Γ₁' _ (sym (∷-injectiveʳ p))
push-let-correct Γ₁ Γ₂ (d ↑ ϕ) Var θ refl env | [] =
    eval d ϕ env
  ≡⟨ cong (λ x → eval d x env) (sym (law-ₒoi ϕ)) ⟩
    eval d (ϕ ₒ oi) env
  ∎

push-let-correct Γ₁ Γ₂ decl (App {σ} (pair (e₁ ↑ θ) (e₂ ↑ ϕ) c)) ψ refl env
  with Γ₁ ⊣ θ | Γ₁ ⊣ ϕ
...  | ⊣r θ₁ (θ₂ o') (refl , refl) | ⊣r ϕ₁ (ϕ₂ o') (refl , refl) =
  {!!}
...  | ⊣r θ₁ (θ₂ o') (refl , refl) | ⊣r {Γ₁'} {_ ∷ Γ₂'} ϕ₁ (ϕ₂ os) (refl , refl) =
    eval⇑ (map⇑ App ((e₁ ↑ ((θ₁ ++⊑ θ₂) ₒ ψ)) ,R push-let Γ₁' Γ₂' decl e₂ ((ϕ₁ ++⊑ ϕ₂) ₒ ψ) refl)) env
  ≡⟨ {!!} ⟩
    eval (reorder-Ctx [] Γ₁ (σ ∷ []) Γ₂ (App (pair (e₁ ↑ θ) (e₂ ↑ ϕ) c)) {!!}) (ψ os ₒ oi) (Cons {! eval⇑ (thin⇑ oi decl) env !} env)
  ∎
...  | ⊣r {Γ₁'} {_ ∷ Γ₂'} θ₁ (θ₂ os) (refl , refl) | ⊣r ϕ₁ (ϕ₂ o') (refl , refl) =
  {!!}
...  | ⊣r θ₁ (θ₂ os) (refl , refl) | ⊣r ϕ₁ (ϕ₂ os) (refl , refl) =
  {!!}
push-let-correct Γ₁ Γ₂ decl (Lam x) θ p env = {!!}
push-let-correct Γ₁ Γ₂ decl (Let x) θ p env = {!!}
push-let-correct Γ₁ Γ₂ decl (Val v) θ p env = {!!}
push-let-correct Γ₁ Γ₂ decl (Plus x) θ p env = {!!}

push-let-top-correct :
  (p : (Expr σ ×R ((σ ∷ []) ⊢ Expr τ)) Γ) (env : Env Γ) →
  eval⇑ (push-let-top p) env ≡ eval (Let p) oi env
push-let-top-correct (pair (decl ↑ ϕ) ((oz os \\ e) ↑ θ) c) env =
    eval⇑ (push-let [] _ (decl ↑ ϕ) e θ refl) env
  ≡⟨ push-let-correct [] _ (decl ↑ ϕ) e θ refl env ⟩
    eval (reorder-Ctx [] [] (_ ∷ []) _ e refl) (θ os ₒ oi) (Cons _ env)
  ≡⟨ cong (λ x → eval x (θ os ₒ oi) (Cons _ env)) (law-reorder-Ctx-Γ₂≡[] [] (_ ∷ []) _ e refl) ⟩
    eval e (θ os ₒ oi) (Cons (eval decl (ϕ ₒ oi) env) env)
  ∎
push-let-top-correct (pair decl ((oz o' \\ e) ↑ θ) c) env =
    eval e θ env
  ≡⟨ cong (eval e θ) (sym (law-project-Env-oi env)) ⟩
    eval e θ (project-Env oi env)
  ≡⟨ sym (lemma-eval e (Cons _ env) θ (oi o')) ⟩
    eval e (θ o' ₒ oi) (Cons _ env)
  ∎
