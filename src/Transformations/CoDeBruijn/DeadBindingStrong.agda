-- Dead binding elimination, but in a single pass (equivalent to strongly live variable analysis)
-- Using co-de-Bruijn representation.
module Transformations.CoDeBruijn.DeadBindingStrong where

open import Data.Nat using (_+_)
open import Data.List using (List ; _∷_ ; [_] ; _++_)
open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; cong₂ ; sym ; trans)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Function using (_∘_ ; _$_ ; flip)

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
    Γ : List U

Let? : (Expr σ ×ᴿ ([ σ ] ⊢ Expr τ)) Γ → Expr τ ⇑ Γ
Let?   (pairᴿ _ ((o' oz \\ e₂) ↑ θ₂) _) = e₂ ↑ θ₂  -- remove binding
Let? p@(pairᴿ _ ((os oz \\ _)  ↑ _)  _) = Let p ↑ oi

lemma-Let? :
  (p : (Expr σ ×ᴿ ([ σ ] ⊢ Expr τ)) Γ) (env : Env Γ) →
  let e' ↑ θ' = Let? p
  in eval (Let p) oi env ≡ eval e' θ' env
lemma-Let? (pairᴿ (e₁ ↑ θ₁) (((o' oz) \\ e₂) ↑ θ₂) c) env =
  trans
    (lemma-eval e₂ (Cons (eval e₁ (θ₁ ₒ oi) env) env) θ₂ (o' oi))
    (cong (eval e₂ θ₂) (law-project-Env-oi env))
lemma-Let? (pairᴿ (e₁ ↑ θ₁) (((os oz) \\ e₂) ↑ θ₂) c) env = refl

lemma-Let?' :
  {Γₑ : Ctx} (p : (Expr σ ×ᴿ ([ σ ] ⊢ Expr τ)) Γ) (env : Env Γₑ) (θ : Γ ⊑ Γₑ) →
  let e' ↑ θ' = Let? p
  in eval (Let p) θ env ≡ eval e' (θ' ₒ θ) env
lemma-Let?' p env θ =
  let pairᴿ (e₁ ↑ θ₁) ((ψ \\ e₂) ↑ θ₂) c = p
      e' ↑ θ' = Let? p
  in
    eval (Let p) θ env
  ≡⟨ refl ⟩
    eval e₂ (ψ ++⊑ (θ₂ ₒ θ)) (Cons (eval e₁ (θ₁ ₒ θ) env) env)
  ≡⟨ cong (λ x → eval e₂ _ (Cons x env)) (trans (lemma-eval e₁ env θ₁ θ) (cong (λ x → eval e₁ x (project-Env θ env)) (sym (law-ₒoi θ₁) ))) ⟩
    eval e₂ (ψ ++⊑ (θ₂ ₒ θ)) (Cons (eval e₁ (θ₁ ₒ oi) (project-Env θ env)) env)
  ≡⟨ cong (λ x → eval e₂ x (Cons (eval e₁ _ _) _)) (trans (cong (_++⊑ (θ₂ ₒ θ)) (sym (law-ₒoi ψ))) (law-commute-ₒ++⊑ ψ oi θ₂ θ)) ⟩
    eval e₂ ((ψ ++⊑ θ₂) ₒ (oi ++⊑ θ)) (Cons (eval e₁ (θ₁ ₒ oi) (project-Env θ env)) env)
  ≡⟨ lemma-eval e₂ (Cons (eval e₁ (θ₁ ₒ oi) (project-Env θ env)) env) (ψ ++⊑ θ₂) (oi ++⊑ θ) ⟩
    eval e₂ (ψ ++⊑ θ₂) (project-Env (oi ++⊑ θ) (Cons (eval e₁ (θ₁ ₒ oi) (project-Env θ env)) env))
  ≡⟨ refl ⟩
    eval e₂ (ψ ++⊑ θ₂) (Cons (eval e₁ (θ₁ ₒ oi) (project-Env θ env)) (project-Env θ env))
  ≡⟨ cong (λ x → eval e₂ (ψ ++⊑ x) _) (sym (law-ₒoi θ₂)) ⟩
    eval e₂ (ψ ++⊑ (θ₂ ₒ oi)) (Cons (eval e₁ (θ₁ ₒ oi) (project-Env θ env)) (project-Env θ env))
  ≡⟨ lemma-Let? p (project-Env θ env) ⟩
    eval e' θ' (project-Env θ env)
  ≡⟨ sym (lemma-eval e' env θ' θ) ⟩
    eval e' (θ' ₒ θ) env
  ∎

mutual
  -- Also remove bindings that are tagged live in the input Expr,
  -- but where the body is revealed to not use the top variable after the recursive call.
  dbe : Expr τ Γ → Expr τ ⇑ Γ
  dbe Var =
    Var ↑ oi
  dbe (App (pairᴿ (e₁ ↑ ϕ₁) (e₂ ↑ ϕ₂) c)) =
    map⇑ App (thin⇑ ϕ₁ (dbe e₁) ,ᴿ thin⇑ ϕ₂ (dbe e₂))
  dbe (Lam (_\\_ {bound = Γ'} ψ e)) =
    map⇑ (Lam ∘ map⊢ ψ) (Γ' \\ᴿ dbe e)
  dbe (Let p) =
    bind⇑ Let? (dbe-Let p)
  dbe (Val v) =
    Val v ↑ oz
  dbe (Plus (pairᴿ (e₁ ↑ ϕ₁) (e₂ ↑ ϕ₂) c)) =
    map⇑ Plus (thin⇑ ϕ₁ (dbe e₁) ,ᴿ thin⇑ ϕ₂ (dbe e₂))

  dbe-Let : (Expr σ ×ᴿ ([ σ ] ⊢ Expr τ)) Γ → (Expr σ ×ᴿ ([ σ ] ⊢ Expr τ)) ⇑ Γ
  dbe-Let (pairᴿ (e₁ ↑ ϕ₁) ((_\\_ {bound = Γ'} ψ e₂) ↑ ϕ₂) c) =
    thin⇑ ϕ₁ (dbe e₁) ,ᴿ thin⇑ ϕ₂ (map⇑ (map⊢ ψ) (Γ' \\ᴿ dbe e₂))

-- IDEA: We could show that this is a fixpoint? dbe (dbe e) ≡ dbe e

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

-- Would have been nicer to reuse the two proofs above (Let is basically App (Lam _)),
-- but it turned out to be more cumbersome than expected.
dbe-correct-Let : 
  {Γₑ : Ctx} (p : (Expr σ ×ᴿ ([ σ ] ⊢ Expr τ)) Γ) (env : Env Γₑ) (θ : Γ ⊑ Γₑ) →
  let pairᴿ (e₁ ↑ θ₁) (l ↑ θ₂) c = p
      _\\_ {bound = Γ'} ψ e₂ = l
      e₁' ↑ θ₁' = dbe e₁
      e₂' ↑ θ₂' = dbe e₂
      p' ↑ θ' = dbe-Let p
  in
  (h₁ : eval e₁' (θ₁' ₒ θ₁ ₒ θ) env ≡ eval e₁ (θ₁ ₒ θ) env) →
  (h₂ : (v : ⟦ σ ⟧) → eval e₂' (θ₂' ₒ (ψ ++⊑ (θ₂ ₒ θ))) (Cons v env) ≡ eval e₂ (ψ ++⊑ (θ₂ ₒ θ)) (Cons v env)) →
  eval (Let p') (θ' ₒ θ) env ≡ eval (Let p) θ env
dbe-correct-Let (pairᴿ (e₁ ↑ θ₁) (_\\_ {bound = Γ'} ψ e₂ ↑ θ₂) c) env θ h₁ h₂
  with dbe e₁    | dbe e₂
...  | e₁' ↑ θ₁' | e₂' ↑ θ₂'
  with Γ' ⊣ θ₂'
...  | split ϕ₁ ϕ₂ (refl , refl)
  with cop (θ₁' ₒ θ₁) (ϕ₂ ₒ θ₂)
...  | coproduct Γ' ψ' θ₁'' θ₂'' p₁ p₂ c =
    eval e₂' ((ϕ₁ ₒ ψ) ++⊑ (θ₂'' ₒ ψ' ₒ θ)) (Cons (eval e₁' (θ₁'' ₒ ψ' ₒ θ) env) env)
  ≡⟨ cong (λ x → eval e₂' _ (Cons (eval e₁' x env) env)) (helper-assoc (sym p₁)) ⟩
    eval e₂' ((ϕ₁ ₒ ψ) ++⊑ (θ₂'' ₒ ψ' ₒ θ)) (Cons (eval e₁' (θ₁' ₒ θ₁ ₒ θ) env) env)
  ≡⟨ cong (λ x → eval e₂' x (Cons _ env)) (trans
      (cong ((ϕ₁ ₒ ψ) ++⊑_) (helper-assoc (sym p₂)) )
      (law-commute-ₒ++⊑ ϕ₁ ψ ϕ₂ (θ₂ ₒ θ))) ⟩
    eval e₂' ((ϕ₁ ++⊑ ϕ₂) ₒ (ψ ++⊑ (θ₂ ₒ θ))) (Cons (eval e₁' (θ₁' ₒ θ₁ ₒ θ) env) env)
  ≡⟨ h₂ (eval e₁' (θ₁' ₒ θ₁ ₒ θ) env) ⟩
    eval e₂ (ψ ++⊑ (θ₂ ₒ θ)) (Cons (eval e₁' (θ₁' ₒ θ₁ ₒ θ) env) env)
  ≡⟨ cong (λ x → eval e₂ _ (Cons x env)) h₁ ⟩
    eval e₂ (ψ ++⊑ (θ₂ ₒ θ)) (Cons (eval e₁ (θ₁ ₒ θ) env) env)
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
dbe-correct (Let {σ} (pairᴿ (e₁ ↑ θ₁) (_\\_ {bound = Γ'} ψ e₂ ↑ θ₂) c)) env θ =
  let p = pairᴿ (e₁ ↑ θ₁) (_\\_ {bound = Γ'} ψ e₂ ↑ θ₂) c
      p' ↑ θ' = dbe-Let p
      e' ↑ θ'' = Let? p'
  in
    eval e' ((θ'' ₒ θ') ₒ θ) env
  ≡⟨ cong (λ x → eval e' x env) (sym (law-ₒₒ θ'' θ' θ)) ⟩
    eval e' (θ'' ₒ θ' ₒ θ) env
  ≡⟨ sym (lemma-Let?' p' env (θ' ₒ θ)) ⟩
    eval (Let p') (θ' ₒ θ) env
  ≡⟨ dbe-correct-Let (pairᴿ (e₁ ↑ θ₁) ((ψ \\ e₂) ↑ θ₂) c) env θ
      (dbe-correct e₁ env (θ₁ ₒ θ))
      (λ v → dbe-correct e₂ (Cons v env) (ψ ++⊑ (θ₂ ₒ θ))) ⟩
    eval (Let p) θ env
  ∎
dbe-correct (Val v) env θ =
  refl
dbe-correct (Plus (pairᴿ (e₁ ↑ θ₁) (e₂ ↑ θ₂) cover)) env θ =
  dbe-correct-×ᴿ _+_ (pairᴿ (e₁ ↑ θ₁) (e₂ ↑ θ₂) cover) env θ
    (dbe-correct e₁ env (θ₁ ₒ θ))
    (dbe-correct e₂ env (θ₂ ₒ θ))
