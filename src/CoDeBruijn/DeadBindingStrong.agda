-- Dead binding elimination, but in a single pass (equivalent to strongly live variable analysis)
-- Using co-de-Bruijn representation.
module CoDeBruijn.DeadBindingStrong where

open import Data.Nat using (_+_)
open import Data.List using (List ; _∷_ ; [] ; _++_)
open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; cong₂ ; sym ; trans)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Function using (_∘_)

open import Core
open import CoDeBruijn.Lang
open import OPE

-- This is needed because our notion of semantical equivalence is "same evaluation result",
-- and values include Agda functions.
-- We might want something different?
postulate
  -- extensionality : {A B : Set} → (f g : A → B) (H : (x : A) → f x ≡ g x) → f ≡ g
  extensionality :
    {S : Set} {T : S -> Set} (f g : (x : S) -> T x) ->
    ((x : S) -> f x ≡ g x) ->
    f ≡ g

let-? : ∀ {σ τ Γ₁ Γ₂ Γ} → Union Γ₁ Γ₂ Γ → Expr σ Γ₁ → ((σ ∷ []) ⊢ Expr τ) Γ₂ → Expr τ ⇑ Γ
let-? u e₁ (oz o' \\ e₂) = e₂ ↑ o-Union₂ u
let-? u e₁ (oz os \\ e₂) = Let u e₁ ((oz os) \\ e₂) ↑ oi

-- Also remove bindings that are tagged live in the input Expr,
-- but where the body is revealed to not use the top variable after the recursive call.
dbe : Expr τ Γ → Expr τ ⇑ Γ
dbe Var =
  Var ↑ oz os
dbe (App u e₁ e₂) =
  let e₁' ↑ θ₁ = dbe e₁
      e₂' ↑ θ₂ = dbe e₂
      u'  ↑ θ  = cover-Union (θ₁ ₒ o-Union₁ u) (θ₂ ₒ o-Union₂ u)
  in App u' e₁' e₂' ↑ θ
dbe (Lam {σ} (_\\_ {bound = Γ'} ψ e)) =
  let (ϕ \\ e') ↑ θ = Γ' \\R dbe e
  in Lam ((ϕ ₒ ψ) \\ e') ↑ θ
  -- this gets in the way of evaluation
  -- map⇑ (Lam ∘ map⊢ ψ) (Γ' \\R dbe e)
dbe (Let {σ} u e₁ (_\\_ {bound = Γ'} ψ e₂)) =
  let e₁'        ↑ θ₁  = dbe e₁
      (ϕ \\ e₂') ↑ θ₂  = Γ' \\R dbe e₂
      u'  ↑ θ   = cover-Union (θ₁ ₒ o-Union₁ u) (θ₂ ₒ o-Union₂ u)
      e'  ↑ θ?  = let-? u' e₁' ((ϕ ₒ ψ) \\ e₂')
  in e' ↑ (θ? ₒ θ)
dbe (Val v) = Val v ↑ oz
dbe (Plus u e₁ e₂) =
  let e₁' ↑ θ₁ = dbe e₁
      e₂' ↑ θ₂ = dbe e₂
      u'  ↑ θ  = cover-Union (θ₁ ₒ o-Union₁ u) (θ₂ ₒ o-Union₂ u)
  in Plus u' e₁' e₂' ↑ θ

-- IDEA: We could show that this is a fixpoint? dbe (dbe e) ≡ dbe e


-- Is this just a part of Union forming a coproduct?
law-o-Union₁ :
  ∀ {Γ₁ Γ₂ Γ} → (θ₁ : Γ₁ ⊑ Γ) → (θ₂ : Γ₂ ⊑ Γ) →
  let u ↑ θ = cover-Union θ₁ θ₂
  in o-Union₁ u ₒ θ ≡ θ₁
law-o-Union₁ (θ₁ o') (θ₂ o') = cong _o' (law-o-Union₁ θ₁ θ₂)
law-o-Union₁ (θ₁ o') (θ₂ os) = cong _o' (law-o-Union₁ θ₁ θ₂)
law-o-Union₁ (θ₁ os) (θ₂ o') = cong _os (law-o-Union₁ θ₁ θ₂)
law-o-Union₁ (θ₁ os) (θ₂ os) = cong _os (law-o-Union₁ θ₁ θ₂)
law-o-Union₁ oz oz = refl

law-o-Union₂ :
  ∀ {Γ₁ Γ₂ Γ} → (θ₁ : Γ₁ ⊑ Γ) → (θ₂ : Γ₂ ⊑ Γ) →
  let u ↑ θ = cover-Union θ₁ θ₂
  in o-Union₂ u ₒ θ ≡ θ₂
law-o-Union₂ (θ₁ o') (θ₂ o') = cong _o' (law-o-Union₂ θ₁ θ₂)
law-o-Union₂ (θ₁ o') (θ₂ os) = cong _os (law-o-Union₂ θ₁ θ₂)
law-o-Union₂ (θ₁ os) (θ₂ o') = cong _o' (law-o-Union₂ θ₁ θ₂)
law-o-Union₂ (θ₁ os) (θ₂ os) = cong _os (law-o-Union₂ θ₁ θ₂)
law-o-Union₂ oz oz = refl

helper-assoc :
  ∀ {Γ Γ₁ Γ₂ Γ' Γ''} →
  (θ₁  : Γ  ⊑ Γ₁) →
  (θ₁' : Γ₁ ⊑ Γ') →
  (θ₂  : Γ  ⊑ Γ₂) →
  (θ₂' : Γ₂ ⊑ Γ') →
  (θ   : Γ' ⊑ Γ'') →
  θ₁ ₒ θ₁' ≡ θ₂ ₒ θ₂' →
  θ₁ ₒ θ₁' ₒ θ ≡ θ₂ ₒ θ₂' ₒ θ
helper-assoc θ₁ θ₁' θ₂ θ₂' θ h =
    θ₁ ₒ θ₁' ₒ θ
  ≡⟨ law-ₒₒ _ _ _ ⟩
    (θ₁ ₒ θ₁') ₒ θ
  ≡⟨  cong (_ₒ θ) h ⟩
    (θ₂ ₒ θ₂') ₒ θ
  ≡⟨ sym (law-ₒₒ _ _ _) ⟩
    θ₂ ₒ θ₂' ₒ θ
  ∎

-- TODO: prove semantics preserving!
dbe-correct :
  {Γₑ : Ctx} (e : Expr τ Γ) (env : Env Γₑ) (θ : Γ ⊑ Γₑ) →
  let e' ↑ θ' = dbe e
  in eval e' (θ' ₒ θ) env ≡ eval e θ env
dbe-correct Var env θ =
  cong (λ x → lookup Top (project-Env x env)) (law-oiₒ θ)
dbe-correct (App u e₁ e₂) env θ =
  let
      e₁' ↑ θ₁ = dbe e₁
      e₂' ↑ θ₂ = dbe e₂
      h₁ = dbe-correct e₁ env (o-Union₁ u ₒ θ)
      h₂ = dbe-correct e₂ env (o-Union₂ u ₒ θ)
      u' ↑ θ' = cover-Union (θ₁ ₒ o-Union₁ u) (θ₂ ₒ o-Union₂ u)
  in
    eval e₁' (o-Union₁ u' ₒ θ' ₒ θ) env
      (eval e₂' (o-Union₂ u' ₒ θ' ₒ θ) env)
  ≡⟨ cong (λ x → eval e₁' (o-Union₁ u' ₒ θ' ₒ θ) env (eval e₂' x env))
      (helper-assoc _ _ _ _ _ (law-o-Union₂ (θ₁ ₒ o-Union₁ u) (θ₂ ₒ o-Union₂ u))) ⟩
    eval e₁' (o-Union₁ u' ₒ θ' ₒ θ) env
      (eval e₂' (θ₂ ₒ o-Union₂ u ₒ θ) env)
  ≡⟨ cong (λ x → eval e₁' x env _)
      (helper-assoc _ _ _ _ _ (law-o-Union₁ (θ₁ ₒ o-Union₁ u) (θ₂ ₒ o-Union₂ u))) ⟩
    eval e₁' (θ₁ ₒ o-Union₁ u ₒ θ) env
      (eval e₂' (θ₂ ₒ o-Union₂ u ₒ θ) env)
  ≡⟨ cong₂ (λ f x → f x) h₁ h₂ ⟩
    eval e₁ (o-Union₁ u ₒ θ) env
      (eval e₂ (o-Union₂ u ₒ θ) env)
  ∎

dbe-correct (Lam (_\\_ {bound = Γ'} ψ e)) env θ with dbe e   | dbe-correct e
dbe-correct (Lam (_\\_ {bound = Γ'} ψ e)) env θ    | e' ↑ θ' | h with Γ' ⊣ θ'
dbe-correct (Lam (_\\_ {bound = Γ'} ψ e)) env θ    | e' ↑ θ' | h    | ⊣r ϕ₁ ϕ₂ (refl , refl) =
  extensionality _ _ λ v →
      eval e' ((ϕ₁ ₒ ψ) ++⊑ (ϕ₂ ₒ θ)) (Cons v env)
    ≡⟨ cong (λ x → eval e' x (Cons v env)) (law-commute-ₒ++⊑ ϕ₁ ψ ϕ₂ θ) ⟩
      eval e' ((ϕ₁ ++⊑ ϕ₂) ₒ (ψ ++⊑ θ)) (Cons v env)
    ≡⟨ h (Cons v env) (ψ ++⊑ θ) ⟩
      eval e (ψ ++⊑ θ) (Cons v env)
    ∎
    
dbe-correct (Let u e₁ e₂) env θ = {!!}
dbe-correct (Val v) env θ = {!!}
dbe-correct (Plus u e₁ e₂) env θ = {!!}
