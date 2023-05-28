{-# OPTIONS --allow-unsolved-metas #-}  -- TODO: finish proof

-- Let Floating (inwards) using co-de-Bruijn representation
--
-- Push the let-binding inwards as far as possible without
-- - duplicating it
-- - pushing it into a lambda
module Transformations.CoDeBruijn.LetInward where

open import Data.Nat using (_+_)
open import Data.List using (List ; _∷_ ; [] ; [_] ; _++_)
open import Data.List.Properties using (++-assoc ; ∷-injective ; ∷-injectiveˡ ; ∷-injectiveʳ ; ++-conicalˡ ; ++-conicalʳ)
open import Data.Unit
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; cong₂ ; sym ; trans)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Function using (_$_)

open import Postulates using (extensionality)
open import Stdlib using (coerce)
open import Data.Thinning
open import Data.Relevant

open import Language.Core
open Language.Core.Env {U}
open Language.Core.Ref {U}
open import Language.CoDeBruijn

private
  variable
    σ τ : U
    Γ : List U

-- TODO: with all the thinning and contexts in scope, I should make the naming scheme more consistent.
-- (θ/ϕ/ψ₁₂ˡʳ'')

eval⇑ : Expr τ ⇑ Γ → Env Γ → ⟦ τ ⟧
eval⇑ x env = let (e ↑ θ) = x in eval e θ env

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
  ([ τ ] ≡ Γ₁ ++ Γ₂ ++ Γ₃ ++ Γ₄) →
  ([ τ ] ≡ Γ₁ ++ Γ₃ ++ Γ₂ ++ Γ₄)
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

-- To factor out the repeated calling of ⊣, packaging up the results in a convenient way.
record Split4 (Γ₁ Γ₂ Γ₃ Γ₄ : Ctx) (ψ : Γ ⊑ (Γ₁ ++ Γ₂ ++ Γ₃ ++ Γ₄)) : Set where
  constructor split4
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

⊣4 : (Γ₁ Γ₂ Γ₃ Γ₄ : Ctx) (ψ : Γ ⊑ (Γ₁ ++ Γ₂ ++ Γ₃ ++ Γ₄)) → Split4 Γ₁ Γ₂ Γ₃ Γ₄ ψ
⊣4 Γ₁ Γ₂ Γ₃ Γ₄ ψ
  with split {Γ₁'} {Γ₂₃₄'} ϕ₁ ϕ₂₃₄ (refl , refl) ← Γ₁ ⊣ ψ
  with split {Γ₂'} {Γ₃₄'}  ϕ₂ ϕ₃₄  (refl , refl) ← Γ₂ ⊣ ϕ₂₃₄
  with split {Γ₃'} {Γ₄'}   ϕ₃ ϕ₄   (refl , refl) ← Γ₃ ⊣ ϕ₃₄
  = split4 ϕ₁ ϕ₂ ϕ₃ ϕ₄ (refl , refl)

Reorder : U ─Indexed → Set
Reorder T = ∀ {Γ} (Γ₁ Γ₂ Γ₃ Γ₄ : Ctx) → T Γ → (Γ ≡ Γ₁ ++ Γ₂ ++ Γ₃ ++ Γ₄) → T (Γ₁ ++ Γ₃ ++ Γ₂ ++ Γ₄)

mutual
  reorder-Ctx-×ᴿ : Reorder (Expr σ ×ᴿ Expr τ)
  reorder-Ctx-×ᴿ Γ₁ Γ₂ Γ₃ Γ₄ (pairᴿ (e₁ ↑ θ) (e₂ ↑ ϕ) c) refl
    with split4 {Γ₁'}  {Γ₂'}  {Γ₃'}  {Γ₄'}  θ₁ θ₂ θ₃ θ₄ (refl , refl) ← ⊣4 Γ₁ Γ₂ Γ₃ Γ₄ θ
    with split4 {Γ₁''} {Γ₂''} {Γ₃''} {Γ₄''} ϕ₁ ϕ₂ ϕ₃ ϕ₄ (refl , refl) ← ⊣4 Γ₁ Γ₂ Γ₃ Γ₄ ϕ =
    pairᴿ
      (reorder-Ctx Γ₁'  Γ₂'  Γ₃'  Γ₄'  e₁ refl ↑ (θ₁ ++⊑ θ₃ ++⊑ θ₂ ++⊑ θ₄))
      (reorder-Ctx Γ₁'' Γ₂'' Γ₃'' Γ₄'' e₂ refl ↑ (ϕ₁ ++⊑ ϕ₃ ++⊑ ϕ₂ ++⊑ ϕ₄))
      (cover++⊑4 θ₁ θ₂ θ₃ θ₄ ϕ₁ ϕ₂ ϕ₃ ϕ₄ c)

  reorder-Ctx-⊢ : ∀ {Γ'} → Reorder (Γ' ⊢ Expr τ)
  reorder-Ctx-⊢ Γ₁ Γ₂ Γ₃ Γ₄ (_\\_ {Γ''} ψ e) p =
    ψ \\ coerce (Expr _)
           (++-assoc Γ'' Γ₁ _)
           (reorder-Ctx (Γ'' ++ Γ₁) Γ₂ Γ₃ Γ₄ e (trans (cong (Γ'' ++_) p) (sym (++-assoc Γ'' Γ₁ _))))
  
  -- It would be nice to compose the Let case from our helpers above, but it's complicated.
  reorder-Ctx : Reorder (Expr τ)
  reorder-Ctx Γ₁ Γ₂ Γ₃ Γ₄ Var p =
    coerce (Expr _) (lemma-[τ]≡++ Γ₁ Γ₂ Γ₃ Γ₄ p) Var
  reorder-Ctx Γ₁ Γ₂ Γ₃ Γ₄ (App p) q = App (reorder-Ctx-×ᴿ Γ₁ Γ₂ Γ₃ Γ₄ p q)
  reorder-Ctx Γ₁ Γ₂ Γ₃ Γ₄ (Lam l) p = Lam (reorder-Ctx-⊢ Γ₁ Γ₂ Γ₃ Γ₄ l p)
  reorder-Ctx Γ₁ Γ₂ Γ₃ Γ₄ (Let (pairᴿ (e₁ ↑ θ) (l ↑ ϕ) c)) refl
    with split4 {Γ₁'}  {Γ₂'}  {Γ₃'}  {Γ₄'}  θ₁ θ₂ θ₃ θ₄ (refl , refl) ← ⊣4 Γ₁ Γ₂ Γ₃ Γ₄ θ
    with split4 {Γ₁''} {Γ₂''} {Γ₃''} {Γ₄''} ϕ₁ ϕ₂ ϕ₃ ϕ₄ (refl , refl) ← ⊣4 Γ₁ Γ₂ Γ₃ Γ₄ ϕ =
    Let (pairᴿ
           (reorder-Ctx Γ₁' Γ₂' Γ₃' Γ₄' e₁ refl ↑ (θ₁ ++⊑ θ₃ ++⊑ θ₂ ++⊑ θ₄))
           (reorder-Ctx-⊢ Γ₁'' Γ₂'' Γ₃'' Γ₄'' l refl ↑ (ϕ₁ ++⊑ ϕ₃ ++⊑ ϕ₂ ++⊑ ϕ₄))
           (cover++⊑4 θ₁ θ₂ θ₃ θ₄ ϕ₁ ϕ₂ ϕ₃ ϕ₄ c))
  reorder-Ctx Γ₁ Γ₂ Γ₃ Γ₄ (Val v) p
    with refl , refl , refl , refl ← lemma-[]≡++ Γ₁ Γ₂ Γ₃ Γ₄ p =
    Val v
  reorder-Ctx Γ₁ Γ₂ Γ₃ Γ₄ (Plus p) q = Plus (reorder-Ctx-×ᴿ Γ₁ Γ₂ Γ₃ Γ₄ p q)

cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {x y u v s t} → x ≡ y → u ≡ v → s ≡ t → f x u s ≡ f y v t
cong₃ f refl refl refl = refl

-- TODO: follows from law-reorder-Ctx?
law-reorder-Ctx-Γ₂≡[] : 
  (Γ₁ Γ₃ Γ₄ : Ctx) (e : Expr τ Γ) (p : Γ ≡ Γ₁ ++ Γ₃ ++ Γ₄) →
  reorder-Ctx Γ₁ [] Γ₃ Γ₄ e p ≡ coerce (Expr τ) p e  -- TODO: this is gonna be annoying, isn't it?
law-reorder-Ctx-Γ₂≡[] Γ₁ Γ₃ Γ₄ Var p = {!!}
law-reorder-Ctx-Γ₂≡[] Γ₁ Γ₃ Γ₄ (App (pairᴿ (e₁ ↑ θ) (e₂ ↑ ϕ) c)) refl
  with split4 {Γ₁'}  {[]}  {Γ₃'}  {Γ₄'} θ₁ oz θ₃ θ₄ (refl , refl) ← ⊣4 Γ₁ [] Γ₃ Γ₄ θ
  with split4 {Γ₁''} {[]} {Γ₃''} {Γ₄''} ϕ₁ oz ϕ₃ ϕ₄ (refl , refl) ← ⊣4 Γ₁ [] Γ₃ Γ₄ ϕ =
  cong App
    (cong₃ (λ x y z → pairᴿ (x ↑ _) (y ↑ _) z)
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
-- This could also make the proof easier, as we avoid usage of _,ᴿ_ etc.?
sink-let :
  ∀ {Γ' Γ σ} (Γ₁ Γ₂ : Ctx)
  (decl : Expr σ ⇑ Γ)
  (body : Expr τ Γ') (p : Γ' ≡ Γ₁ ++ σ ∷ Γ₂) (ψ : (Γ₁ ++ Γ₂) ⊑ Γ) →
  Expr τ ⇑ Γ

sink-let Γ₁ Γ₂ decl Var p ψ with Γ₁
sink-let Γ₁ Γ₂ decl Var p ψ    | (_ ∷ Γ₁') with () ← ++-conicalʳ Γ₁' _ (sym (∷-injectiveʳ p))
sink-let Γ₁ Γ₂ decl Var refl ψ | [] = decl -- The declaration must be live, so we know the variable references it.

sink-let Γ₁ Γ₂ decl e@(App (pairᴿ (e₁ ↑ θ) (e₂ ↑ ϕ) c)) refl ψ
  with Γ₁ ⊣ θ | Γ₁ ⊣ ϕ
  -- declaration not used at all (impossible!)
...  | split θ₁ (o' θ₂) (refl , refl) | split ϕ₁ (o' ϕ₂) (refl , refl)
  with c₁ , () ← cover-split-++⊑ θ₁ ϕ₁ _ _ c
  -- declaration used in right subexpression
...  | split θ₁ (o' θ₂) (refl , refl) | split {Γ₁'} {_ ∷ Γ₂'} ϕ₁ (os ϕ₂) (refl , refl) =
                                        -- Here, we should also be able to work in a smaller context, then thin⇑.
                                        -- Parts of Γ might neither be free in decl nor e₂.
                                        -- This is necessary if we want to pass down a cover.
  map⇑ App ((e₁ ↑ ((θ₁ ++⊑ θ₂) ₒ ψ)) ,ᴿ sink-let Γ₁' Γ₂' decl e₂ refl ((ϕ₁ ++⊑ ϕ₂) ₒ ψ))
  -- declaration used in left subexpression
...  | split {Γ₁'} {_ ∷ Γ₂'} θ₁ (os θ₂) (refl , refl) | split ϕ₁ (o' ϕ₂) (refl , refl) =
  map⇑ App (sink-let Γ₁' Γ₂' decl e₁ refl ((θ₁ ++⊑ θ₂) ₒ ψ) ,ᴿ (e₂ ↑ ((ϕ₁ ++⊑ ϕ₂) ₒ ψ)))
  -- declaration used in both subexpressions (don't push further!)
...  | split θ₁ (os θ₂) (refl , refl) | split ϕ₁ (os ϕ₂) (refl , refl) =
  map⇑ Let (decl ,ᴿ ((os oz \\ reorder-Ctx [] Γ₁ [ _ ] _ e refl) ↑ ψ))

sink-let Γ₁ Γ₂ decl e@(Lam _) refl ψ = -- don't push into lambdas!
  map⇑ Let (decl ,ᴿ ((os oz \\ reorder-Ctx [] Γ₁ [ _ ] _ e refl) ↑ ψ))

sink-let Γ₁ Γ₂ decl e@(Let (pairᴿ (e₁ ↑ θ) (_\\_ {Γ''} ψ' e₂ ↑ ϕ) c)) refl ψ
  with Γ₁ ⊣ θ | Γ₁ ⊣ ϕ
  -- declaration not used at all (impossible!)
...  | split θ₁ (o' θ₂) (refl , refl) | split ϕ₁ (o' ϕ₂) (refl , refl)
  with c₁ , () ← cover-split-++⊑ θ₁ ϕ₁ _ _ c
  -- declaration used in right subexpression
...  | split θ₁ (o' θ₂) (refl , refl) | split {Γ₁'} {_ ∷ Γ₂'} ϕ₁ (os ϕ₂) (refl , refl)
    -- TODO: can we avoid this mess?
    with e₂' ↑ ϕ' ← sink-let (Γ'' ++ Γ₁') Γ₂' (thin⇑ (oe ++⊑ oi) decl) e₂
                      (sym (++-assoc Γ'' Γ₁' (_ ∷ Γ₂')))
                      (coerce (_⊑ (Γ'' ++ _)) (sym (++-assoc Γ'' Γ₁' Γ₂')) (oi ++⊑ ((ϕ₁ ++⊑ ϕ₂) ₒ ψ)))
    with split ψ'' ϕ'' (refl , b) ← Γ'' ⊣ ϕ' =
    map⇑ Let ((e₁ ↑ ((θ₁ ++⊑ θ₂) ₒ ψ)) ,ᴿ (((ψ'' ₒ ψ') \\ e₂') ↑ ϕ''))
  -- declaration used in left subexpression
...  | split {Γ₁'} {_ ∷ Γ₂'} θ₁ (os θ₂) (refl , refl) | split ϕ₁ (o' ϕ₂) (refl , refl) =
  map⇑ Let (sink-let Γ₁' Γ₂' decl e₁ refl ((θ₁ ++⊑ θ₂) ₒ ψ) ,ᴿ ((ψ' \\ e₂) ↑ ((ϕ₁ ++⊑ ϕ₂) ₒ ψ)))
  -- declaration used in both subexpressions (don't push further!)
...  | split θ₁ (os θ₂) (refl , refl) | split {Γ₁'} {_ ∷ Γ₂'} ϕ₁ (os ϕ₂) (refl , refl) =
  map⇑ Let (decl ,ᴿ ((os oz \\ reorder-Ctx [] Γ₁ [ _ ] _ e refl) ↑ ψ))

sink-let Γ₁ Γ₂ decl (Val v) p θ =
  (Val v) ↑ oe

sink-let Γ₁ Γ₂ decl e@(Plus (pairᴿ (e₁ ↑ θ) (e₂ ↑ ϕ) c)) refl ψ
  with Γ₁ ⊣ θ | Γ₁ ⊣ ϕ
  -- declaration not used at all (impossible!)
...  | split θ₁ (o' θ₂) (refl , refl) | split ϕ₁ (o' ϕ₂) (refl , refl)
  with c₁ , () ← cover-split-++⊑ θ₁ ϕ₁ _ _ c
  -- declaration used in right subexpression
...  | split θ₁ (o' θ₂) (refl , refl) | split {Γ₁'} {_ ∷ Γ₂'} ϕ₁ (os ϕ₂) (refl , refl) =
  map⇑ Plus ((e₁ ↑ ((θ₁ ++⊑ θ₂) ₒ ψ)) ,ᴿ sink-let Γ₁' Γ₂' decl e₂ refl ((ϕ₁ ++⊑ ϕ₂) ₒ ψ))
  -- declaration used in left subexpression
...  | split {Γ₁'} {_ ∷ Γ₂'} θ₁ (os θ₂) (refl , refl) | split ϕ₁ (o' ϕ₂) (refl , refl) =
  map⇑ Plus (sink-let Γ₁' Γ₂' decl e₁ refl ((θ₁ ++⊑ θ₂) ₒ ψ) ,ᴿ (e₂ ↑ ((ϕ₁ ++⊑ ϕ₂) ₒ ψ)))
  -- declaration used in both subexpressions (don't push further!)
...  | split θ₁ (os θ₂) (refl , refl) | split ϕ₁ (os ϕ₂) (refl , refl) =
  map⇑ Let (decl ,ᴿ ((os oz \\ reorder-Ctx [] Γ₁ [ _ ] _ e refl) ↑ ψ))

-- This is the same signature as for `Let live` itself, just with a thinning so we can drop the Let.
-- (in case it was dead)
sink-let-top : (Expr σ ×ᴿ ([ σ ] ⊢ Expr τ)) Γ → Expr τ ⇑ Γ
sink-let-top (pairᴿ (decl ↑ ϕ) ((os oz \\ e) ↑ θ) c) =
  sink-let [] _ (decl ↑ ϕ) e refl θ
sink-let-top (pairᴿ decl ((o' oz \\ e) ↑ θ) c) =
  e ↑ θ   -- binding is unused, why bother?

mutual
  law-eval-reorder-Ctx-×ᴿ :
    ∀ {τ₁ τ₂} (binop : ⟦ τ₁ ⟧ → ⟦ τ₂ ⟧ → ⟦ τ ⟧)
    (Γ₁ Γ₂ Γ₃ Γ₄ : Ctx) (e : (Expr τ₁ ×ᴿ Expr τ₂) Γ) (p : Γ ≡ Γ₁ ++ Γ₂ ++ Γ₃ ++ Γ₄)
    (env₁ : Env Γ₁) (env₂ : Env Γ₂) (env₃ : Env Γ₃) (env₄ : Env Γ₄) →
      eval-binop binop (reorder-Ctx-×ᴿ Γ₁ Γ₂ Γ₃ Γ₄ e p) oi (env₁ ++ᴱ env₃ ++ᴱ env₂ ++ᴱ env₄)
    ≡ eval-binop binop (coerce (Expr τ₁ ×ᴿ Expr τ₂) p e) oi (env₁ ++ᴱ env₂ ++ᴱ env₃ ++ᴱ env₄)
  law-eval-reorder-Ctx-×ᴿ binop Γ₁ Γ₂ Γ₃ Γ₄ (pairᴿ (e₁ ↑ θ) (e₂ ↑ ϕ) c) refl env₁ env₂ env₃ env₄
    with split4 {Γ₁'}  {Γ₂'}  {Γ₃'}  {Γ₄'}  θ₁ θ₂ θ₃ θ₄ (refl , refl) ← ⊣4 Γ₁ Γ₂ Γ₃ Γ₄ θ
    with split4 {Γ₁''} {Γ₂''} {Γ₃''} {Γ₄''} ϕ₁ ϕ₂ ϕ₃ ϕ₄ (refl , refl) ← ⊣4 Γ₁ Γ₂ Γ₃ Γ₄ ϕ =
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
    ≡ eval (coerce (Expr _) p e) oi (env₁ ++ᴱ env₂ ++ᴱ env₃ ++ᴱ env₄)
  law-eval-reorder-Ctx Γ₁ Γ₂ Γ₃ Γ₄ Var p env₁ env₂ env₃ env₄ =
    {!!}  -- trivial, but painful
  law-eval-reorder-Ctx Γ₁ Γ₂ Γ₃ Γ₄ (App x) refl env₁ env₂ env₃ env₄ =
    law-eval-reorder-Ctx-×ᴿ _$_ Γ₁ Γ₂ Γ₃ Γ₄ x refl env₁ env₂ env₃ env₄
  law-eval-reorder-Ctx Γ₁ Γ₂ Γ₃ Γ₄ (Lam x) p env₁ env₂ env₃ env₄ = {!!}
  law-eval-reorder-Ctx Γ₁ Γ₂ Γ₃ Γ₄ (Let x) p env₁ env₂ env₃ env₄ = {!!}
  law-eval-reorder-Ctx Γ₁ Γ₂ Γ₃ Γ₄ (Val v) p env₁ env₂ env₃ env₄ = {!!}
  law-eval-reorder-Ctx Γ₁ Γ₂ Γ₃ Γ₄ (Plus x) refl env₁ env₂ env₃ env₄ =
    law-eval-reorder-Ctx-×ᴿ _+_ Γ₁ Γ₂ Γ₃ Γ₄ x refl env₁ env₂ env₃ env₄

law-eval-reorder-Ctx-[] :
  ∀ {σ τ} Γ₁ Γ₂ (e : Expr τ Γ) (p : Γ ≡ Γ₁ ++ σ ∷ Γ₂) (v : ⟦ σ ⟧) (env₁ : Env Γ₁) (env₂ : Env Γ₂) →
    eval (reorder-Ctx [] Γ₁ [ σ ] Γ₂ e p) oi (Cons v (env₁ ++ᴱ env₂))
  ≡ eval (coerce (Expr _) p e) oi (env₁ ++ᴱ Cons v env₂)
law-eval-reorder-Ctx-[] Γ₁ Γ₂ Var p v env₁ env₂ = {!!}
-- with lemma-[]≡++ [] Γ₁ [ _ ] Γ₂ {!!}
law-eval-reorder-Ctx-[] Γ₁ Γ₂ (App x) p v env₁ env₂ = {!!}
law-eval-reorder-Ctx-[] Γ₁ Γ₂ (Lam x) p v env₁ env₂ = {!!}
law-eval-reorder-Ctx-[] Γ₁ Γ₂ (Let x) p v env₁ env₂ = {!!}
law-eval-reorder-Ctx-[] Γ₁ Γ₂ (Val v₁) p v env₁ env₂ = {!!}
law-eval-reorder-Ctx-[] Γ₁ Γ₂ (Plus x) p v env₁ env₂ = {!!}


-- TODO: Might have to make more general to make it useful as IH.
-- TODO: What to do about the cover? :/
-- - use _,R_ which introduces another context and thinning, or
-- - demand a cover as an input and manage to adapt it for passing down
sink-let-correct :
  ∀ {Γ' Γ σ} (Γ₁ Γ₂ : Ctx)
  (decl : Expr σ ⇑ Γ) (e : Expr τ Γ') (θ : (Γ₁ ++ Γ₂) ⊑ Γ) (p : Γ' ≡ Γ₁ ++ σ ∷ Γ₂) →
  (env : Env Γ) →
    eval⇑ (sink-let Γ₁ Γ₂ decl e p θ) env
  ≡ eval⇑ (map⇑ Let (decl ,ᴿ ((os oz \\ reorder-Ctx [] Γ₁ [ σ ] Γ₂ e p) ↑ θ))) env

sink-let-correct Γ₁ Γ₂ decl    Var θ p env with Γ₁
sink-let-correct Γ₁ Γ₂ decl    Var θ p env    | (_ ∷ Γ₁') with () ← ++-conicalʳ Γ₁' _ (sym (∷-injectiveʳ p))
sink-let-correct Γ₁ Γ₂ (d ↑ ϕ) Var θ refl env | [] =
  {!!}
    -- eval d ϕ env
  -- ≡⟨ cong (λ x → eval d x env) (sym (law-ₒoi ϕ)) ⟩
    -- eval d (ϕ ₒ oi) env

  -- declaration not used at all (impossible!)
  -- declaration used in right subexpression
  -- declaration used in left subexpression
  -- declaration used in both subexpressions (don't push further!)

sink-let-correct {σ = σ} Γ₁ Γ₂ decl e@(App (pairᴿ (e₁ ↑ θ) (e₂ ↑ ϕ) c)) ψ refl env
  with Γ₁ ⊣ θ | Γ₁ ⊣ ϕ

  -- declaration not used at all (impossible!)
...  | split θ₁ (o' θ₂) (refl , refl) | split ϕ₁ (o' ϕ₂) (refl , refl)
  with c₁ , () ← cover-split-++⊑ θ₁ ϕ₁ _ _ c
  -- declaration used in right subexpression
...  | split θ₁ (o' θ₂) (refl , refl) | split {Γ₁'} {_ ∷ Γ₂'} ϕ₁ (os ϕ₂) (refl , refl) =
    {!!} -- eval⇑ (map⇑ App ((e₁ ↑ ((θ₁ ++⊑ θ₂) ₒ ψ)) ,ᴿ sink-let Γ₁' Γ₂' decl e₂ refl ((ϕ₁ ++⊑ ϕ₂) ₒ ψ) ?)) env
  ≡⟨ {!!} ⟩
    -- eval (reorder-Ctx [] Γ₁ [ σ ] Γ₂ (App (pairᴿ (e₁ ↑ θ) (e₂ ↑ ϕ) c)) {!!}) os (ψ ₒ oi) (Cons {! eval⇑ (thin⇑ oi decl) env !} env)
    {!!}
  ∎
  -- declaration used in left subexpression
...  | split {Γ₁'} {_ ∷ Γ₂'} θ₁ (os θ₂) (refl , refl) | split ϕ₁ (o' ϕ₂) (refl , refl)
  with split4 θ'₁ θ'₂ θ'₃ θ'₄ (pθ , qθ) ← ⊣4 [] Γ₁ [ σ ] _ θ
  with split4 ϕ'₁ ϕ'₂ ϕ'₃ ϕ'₄ (pϕ , qϕ) ← ⊣4 [] Γ₁ [ σ ] _ ϕ
  =
  let e₁' ↑ θ' = sink-let Γ₁' Γ₂' decl e₁ refl ((θ₁ ++⊑ θ₂) ₒ ψ)
      coproduct Γ' ψ' θ'' ϕ'' eqθ eqϕ c = cop θ' ((ϕ₁ ++⊑ ϕ₂) ₒ ψ)
  in
    eval e₁' (θ'' ₒ ψ') env (eval e₂ (ϕ'' ₒ ψ') env)
  ≡⟨ {!x!} ⟩
    {!pθ!}
    -- eval (reorder-Ctx [] Γ₁ [ σ ] Γ₂ (App (pairᴿ (e₁ ↑ θ) (e₂ ↑ ϕ) {!!})) {!!}) (os ψ ₒ oi) (Cons {! eval⇑ (thin⇑ oi decl) env !} env)
    -- eval (Let (pairᴿ decl ((os oz \\ reorder-Ctx [] Γ₁ [ _ ] Γ₂ e {!refl!}) ↑ ψ) {!!})) oi env
  ∎
  -- declaration used in both subexpressions (don't push further!)
...  | split θ₁ (os θ₂) (refl , refl) | split ϕ₁ (os ϕ₂) (refl , refl) =
  {!!}
sink-let-correct Γ₁ Γ₂ decl e@(Lam _) θ refl env =
  extensionality _ _ λ v →
    let e' ↑ θ' = sink-let Γ₁ Γ₂ decl e refl θ
    in
      eval e' θ' env v
    ≡⟨ refl ⟩
      eval⇑ (map⇑ Let (decl ,ᴿ ((os oz \\ reorder-Ctx [] Γ₁ [ _ ] Γ₂ e refl) ↑ θ))) env v
    ∎

sink-let-correct Γ₁ Γ₂ decl (Let x) θ p env = {!!}
sink-let-correct Γ₁ Γ₂ decl (Val v) θ p env = {!!}
sink-let-correct Γ₁ Γ₂ decl (Plus x) θ p env = {!!}

sink-let-top-correct :
  (p : (Expr σ ×ᴿ ([ σ ] ⊢ Expr τ)) Γ) (env : Env Γ) →
  eval⇑ (sink-let-top p) env ≡ eval (Let p) oi env
sink-let-top-correct (pairᴿ (decl ↑ ϕ) ((os oz \\ e) ↑ θ) c) env
  with cop ϕ θ | sink-let-correct [] _ (decl ↑ ϕ) e θ refl env
...  | coproduct Γ' ψ ϕ' θ' refl refl cover | h =
    eval⇑ (sink-let [] _ (decl ↑ ϕ) e refl θ) env
  ≡⟨ h ⟩
    eval (Let (pairᴿ (decl ↑ ϕ') ((os oz \\ reorder-Ctx [] [] [ _ ] _ e refl) ↑ θ') cover)) ψ env
  ≡⟨ refl ⟩
    eval (reorder-Ctx [] [] [ _ ] _ e refl) (os θ) (Cons (eval decl ϕ env) env)
  ≡⟨ cong (λ x → eval x (os θ) (Cons _ env)) (law-reorder-Ctx-Γ₂≡[] [] [ _ ] _ e refl) ⟩
    eval e (os θ) (Cons (eval decl ϕ env) env)
  ≡⟨ cong (λ x → eval e (os θ) (Cons (eval decl x env) env)) (sym (law-ₒoi ϕ)) ⟩
    eval e (os θ) (Cons (eval decl (ϕ ₒ oi) env) env)
  ≡⟨ cong (λ x → eval e (os x) _) (sym (law-ₒoi θ)) ⟩
    eval e (os θ ₒ oi) (Cons (eval decl (ϕ ₒ oi) env) env)
  ∎
sink-let-top-correct (pairᴿ decl ((o' oz \\ e) ↑ θ) c) env =
    eval e θ env
  ≡⟨ cong (eval e θ) (sym (law-project-Env-oi env)) ⟩
    eval e θ (project-Env oi env)
  ≡⟨ sym (lemma-eval e (Cons _ env) θ (o' oi)) ⟩
    eval e (o' θ ₒ oi) (Cons _ env)
  ∎
