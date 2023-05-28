-- Dead binding elimination,
-- Using co-de-Bruijn representation.
module Transformations.CoDeBruijn.DeadBinding where

open import Data.Nat using (_+_)
open import Data.List using (List ; _∷_ ; [_])
open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; cong₂ ; sym; trans)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Function using (_∘_; _$_)

open import Postulates using (extensionality)
open import Data.Thinning
open import Data.Relevant

open import Language.Core
open Language.Core.Env {U}
open Language.Core.Ref {U}
open import Language.CoDeBruijn

private
  variable
    σ τ : U
    Γ : Ctx

-- Only remove directly dead bindings.
dbe : Expr τ Γ → Expr τ ⇑ Γ
dbe Var =
  Var ↑ oi
dbe (App (pairᴿ (e₁ ↑ ϕ₁) (e₂ ↑ ϕ₂) c)) =
  map⇑ App (thin⇑ ϕ₁ (dbe e₁) ,ᴿ thin⇑ ϕ₂ (dbe e₂))
dbe (Lam (_\\_ {Γ'} ψ e)) =
  map⇑ (Lam ∘ map⊢ ψ) (Γ' \\ᴿ dbe e)
-- NOTE: We check liveness given based on the the variable usage in the input Expr.
-- But dbe e₂ might reveal the variable to be dead even if previously marked live!
dbe (Let (pairᴿ (e₁ ↑ ϕ₁) ((o' oz \\ e₂) ↑ ϕ₂) c)) =
  thin⇑ ϕ₂ (dbe e₂)
dbe (Let (pairᴿ (e₁ ↑ ϕ₁) ((os oz \\ e₂) ↑ ϕ₂) c)) =
  map⇑ Let (thin⇑ ϕ₁ (dbe e₁) ,ᴿ thin⇑ ϕ₂ ([ _ ] \\ᴿ dbe e₂))
dbe (Val v) =
  Val v ↑ oz
dbe (Plus (pairᴿ (e₁ ↑ ϕ₁) (e₂ ↑ ϕ₂) c)) =
  map⇑ Plus (thin⇑ ϕ₁ (dbe e₁) ,ᴿ thin⇑ ϕ₂ (dbe e₂))

-- TODO: iterate!

helper-assoc :
  {Γ Γ₁ Γ₂ Γ' Γ'' : Ctx} →
  {θ₁  : Γ  ⊑ Γ₁} {θ₁' : Γ₁ ⊑ Γ'} {θ₂  : Γ  ⊑ Γ₂} {θ₂' : Γ₂ ⊑ Γ'} {θ : Γ' ⊑ Γ''} →
  θ₁ ₒ θ₁' ≡ θ₂ ₒ θ₂' →
  θ₁ ₒ θ₁' ₒ θ ≡ θ₂ ₒ θ₂' ₒ θ
helper-assoc {θ₁ = θ₁} {θ₁' = θ₁'} {θ₂ = θ₂} {θ₂' = θ₂'} {θ = θ} h =
    θ₁ ₒ θ₁' ₒ θ
  ≡⟨ law-ₒₒ _ _ _ ⟩
    (θ₁ ₒ θ₁') ₒ θ
  ≡⟨  cong (_ₒ θ) h ⟩
    (θ₂ ₒ θ₂') ₒ θ
  ≡⟨ sym (law-ₒₒ _ _ _) ⟩
    θ₂ ₒ θ₂' ₒ θ
  ∎

dbe-correct-Lam :
  {Γₑ : Ctx} (l : ([ σ ] ⊢ Expr τ) Γ) (env : Env Γₑ) (θ : Γ ⊑ Γₑ) →
  let _\\_ {bound = Γ'} ψ e₁ = l
      e₁' ↑ θ₁' = dbe e₁
      e = Lam l
      e' ↑ θ' = dbe e
  in
  (h : (v : ⟦ σ ⟧) → eval e₁' (θ₁' ₒ (ψ ++⊑ θ)) (Cons v env) ≡ eval e₁ (ψ ++⊑ θ) (Cons v env)) →
  eval e' (θ' ₒ θ) env ≡ eval e θ env
dbe-correct-Lam (_\\_ {bound = Γ'} ψ e₁) env θ h
  with dbe e₁
...  | e₁' ↑ θ₁
  with Γ' ⊣ θ₁
...  | split ϕ₁ ϕ₂ (refl , refl) =
  extensionality _ _ λ v →  -- TODO: move extensionality out?
      eval e₁' ((ϕ₁ ₒ ψ) ++⊑ (ϕ₂ ₒ θ)) (Cons v env)
    ≡⟨ cong (λ x → eval e₁' x (Cons v env)) (law-commute-ₒ++⊑ ϕ₁ ψ ϕ₂ θ) ⟩
      eval e₁' ((ϕ₁ ++⊑ ϕ₂) ₒ (ψ ++⊑ θ)) (Cons v env)
    ≡⟨ h v ⟩
      eval e₁ (ψ ++⊑ θ) (Cons v env)
    ∎

dbe-correct-×ᴿ :
  {Γₑ : Ctx}
  {τ₁ τ₂ τ : U} (eval-step : ⟦ τ₁ ⟧ → ⟦ τ₂ ⟧ → ⟦ τ ⟧) →
  (p : (Expr τ₁ ×ᴿ Expr τ₂) Γ) (env : Env Γₑ) (θ : Γ ⊑ Γₑ) →
  let pairᴿ (e₁ ↑ θ₁) (e₂ ↑ θ₂) c = p
      e₁' ↑ θ₁' = dbe e₁
      e₂' ↑ θ₂' = dbe e₂
      p' ↑ θ' = (e₁' ↑ (θ₁' ₒ θ₁)) ,ᴿ (e₂' ↑ (θ₂' ₒ θ₂))
  in
  (h₁ : eval e₁' (θ₁' ₒ θ₁ ₒ θ) env ≡ eval e₁ (θ₁ ₒ θ) env) →
  (h₂ : eval e₂' (θ₂' ₒ θ₂ ₒ θ) env ≡ eval e₂ (θ₂ ₒ θ) env) →
  eval-binop eval-step p' (θ' ₒ θ) env ≡ eval-binop eval-step p θ env
  --   eval-step (eval e₁'' (θ₁'' ₒ θ' ₒ θ) env) (eval e₂'' (θ₂'' ₒ θ' ₒ θ) env)
  -- ≡ eval-step (eval e₁ (θ₁ ₒ θ) env) (eval e₂ (θ₂ ₒ θ) env)
dbe-correct-×ᴿ eval-step (pairᴿ (e₁ ↑ θ₁) (e₂ ↑ θ₂) c) env θ h₁ h₂
  with dbe e₁    | dbe e₂
...  | e₁' ↑ θ₁' | e₂' ↑ θ₂'
  with cop (θ₁' ₒ θ₁) (θ₂' ₒ θ₂) 
...  | coproduct Γ' ψ θ₁'' θ₂'' p₁ p₂ c =
     eval-step
       (eval e₁' (θ₁'' ₒ ψ ₒ θ) env)
       (eval e₂' (θ₂'' ₒ ψ ₒ θ) env)
   ≡⟨ cong (λ x → eval-step (eval e₁' _ _) (eval e₂' x env)) (helper-assoc (sym p₂)) ⟩
     eval-step
       (eval e₁' (θ₁'' ₒ ψ ₒ θ) env)
       (eval e₂' (θ₂' ₒ θ₂ ₒ θ) env)
   ≡⟨ cong (λ x → eval-step (eval e₁' x env) _) (helper-assoc (sym p₁)) ⟩
     eval-step
       (eval e₁' (θ₁' ₒ θ₁ ₒ θ) env)
       (eval e₂' (θ₂' ₒ θ₂ ₒ θ) env)
   ≡⟨ cong₂ eval-step h₁ h₂ ⟩
    eval-step
      (eval e₁ (θ₁ ₒ θ) env)
      (eval e₂ (θ₂ ₒ θ) env)
  ∎

dbe-correct :
  {Γₑ : Ctx} (e : Expr τ Γ) (env : Env Γₑ) (θ : Γ ⊑ Γₑ) →
  let e' ↑ θ' = dbe e
  in eval e' (θ' ₒ θ) env ≡ eval e θ env
dbe-correct Var env θ =
  cong (λ x → lookup Top (project-Env x env)) (law-oiₒ θ)
dbe-correct (App (pairᴿ (e₁ ↑ θ₁) (e₂ ↑ θ₂) cover)) env θ =
  dbe-correct-×ᴿ _$_ (pairᴿ (e₁ ↑ θ₁) (e₂ ↑ θ₂) cover) env θ
    (dbe-correct e₁ env (θ₁ ₒ θ))
    (dbe-correct e₂ env (θ₂ ₒ θ))
dbe-correct (Lam (_\\_ {bound = Γ'} ψ e₁)) env θ =
  dbe-correct-Lam (ψ \\ e₁) env θ  λ v → dbe-correct e₁ (Cons v env) (ψ ++⊑ θ)
dbe-correct (Let {σ} (pairᴿ (e₁ ↑ θ₁) ((o' oz \\ e₂) ↑ θ₂) c)) env θ =
  let e₂' ↑ θ₂' = dbe e₂
      h₂ = dbe-correct e₂ env (θ₂ ₒ θ)
  in
    eval e₂' ((θ₂' ₒ θ₂) ₒ θ) env
  ≡⟨ cong (λ x → eval e₂' x env) (sym (law-ₒₒ θ₂' θ₂ θ)) ⟩
    eval e₂' (θ₂' ₒ θ₂ ₒ θ) env
  ≡⟨ h₂ ⟩
    eval e₂ (θ₂ ₒ θ) env
  ≡⟨ cong (λ x → eval e₂ _ x) (sym (law-project-Env-oi env)) ⟩
    eval e₂ (θ₂ ₒ θ) (project-Env oi env)
  ≡⟨ sym (lemma-eval e₂ (Cons _ env) (θ₂ ₒ θ) (o' oi)) ⟩
    eval e₂ (o' ((θ₂ ₒ θ) ₒ oi)) (Cons (eval e₁ (θ₁ ₒ θ) env) env)
  ≡⟨ cong (λ x → eval e₂ (o' x) _) (law-ₒoi (θ₂ ₒ θ)) ⟩
    eval e₂ (o' (θ₂ ₒ θ)) (Cons (eval e₁ (θ₁ ₒ θ) env) env)
  ∎
dbe-correct (Let {σ} p@(pairᴿ (e₁ ↑ θ₁) ((os oz \\ e₂) ↑ θ₂) c)) env θ
  -- Would have been nicer to reuse the two proofs above (Let is basically App (Lam _)),
  -- but it turned out to be more cumbersome than expected.
  with dbe e₁    | dbe e₂    | dbe-correct e₁ env (θ₁ ₒ θ) | dbe-correct e₂
...  | e₁' ↑ θ₁' | e₂' ↑ θ₂' | h₁                          | h₂
  with [ _ ] ⊣ θ₂'
...  | split ϕ₁ ϕ₂ (refl , refl)
  with cop (θ₁' ₒ θ₁) (ϕ₂ ₒ θ₂)
...  | coproduct Γ' ψ' θ₁'' θ₂'' p₁ p₂ c =
    eval e₂' (ϕ₁ ++⊑ θ₂'' ₒ ψ' ₒ θ) (Cons (eval e₁' (θ₁'' ₒ ψ' ₒ θ) env) env)
  ≡⟨ cong (λ x → eval e₂' (x ++⊑ _) (Cons _ env)) (sym (law-ₒoi ϕ₁)) ⟩
    eval e₂' ((ϕ₁ ₒ os oz) ++⊑ θ₂'' ₒ ψ' ₒ θ) (Cons (eval e₁' (θ₁'' ₒ ψ' ₒ θ) env) env)
  ≡⟨ cong (λ x → eval e₂' _ (Cons (eval e₁' x env) env)) (helper-assoc (sym p₁)) ⟩
    eval e₂' ((ϕ₁ ₒ os oz) ++⊑ θ₂'' ₒ ψ' ₒ θ) (Cons (eval e₁' (θ₁' ₒ θ₁ ₒ θ) env) env)
  ≡⟨ cong (λ x → eval e₂' x (Cons _ env)) (trans
      (cong ((ϕ₁ ₒ os oz) ++⊑_) (helper-assoc (sym p₂)) )
      (law-commute-ₒ++⊑ ϕ₁ (os oz) ϕ₂ (θ₂ ₒ θ))) ⟩
    eval e₂' ((ϕ₁ ++⊑ ϕ₂) ₒ (os oz ++⊑ (θ₂ ₒ θ))) (Cons (eval e₁' (θ₁' ₒ θ₁ ₒ θ) env) env)
  ≡⟨ h₂ (Cons (eval e₁' (θ₁' ₒ θ₁ ₒ θ) env) env) (os (θ₂ ₒ θ)) ⟩
    eval e₂ (os (θ₂ ₒ θ)) (Cons (eval e₁' (θ₁' ₒ θ₁ ₒ θ) env) env)
  ≡⟨ cong (λ x → eval e₂ (os (θ₂ ₒ θ)) (Cons x env)) h₁ ⟩
    eval e₂ (os (θ₂ ₒ θ)) (Cons (eval e₁ (θ₁ ₒ θ) env) env)
  ∎
dbe-correct (Val v) env θ =
  refl
dbe-correct (Plus (pairᴿ (e₁ ↑ θ₁) (e₂ ↑ θ₂) cover)) env θ =
  dbe-correct-×ᴿ _+_ (pairᴿ (e₁ ↑ θ₁) (e₂ ↑ θ₂) cover) env θ
    (dbe-correct e₁ env (θ₁ ₒ θ))
    (dbe-correct e₂ env (θ₂ ₒ θ))
