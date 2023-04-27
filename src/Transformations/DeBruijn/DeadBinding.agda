-- Dead Binding Elimination (simple),
-- but using liveness annotations to avoid quadratic complexity for renaming.
module Transformations.DeBruijn.DeadBinding where

open import Data.Nat using (_+_; ℕ)
open import Data.List using (List ; _∷_ ; [])
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; cong₂ ; sym ; trans)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Function using (_$_)

open import Data.OPE
open import Postulates using (extensionality)

open import Language.Core
open Language.Core.Env {U} {⟦_⟧}
open Language.Core.Ref {U} {⟦_⟧}
open import Language.DeBruijn
open import Transformations.Recursion
open import Transformations.DeBruijn.Live

private
  variable
    σ τ : U
    Γ Γ' Δ : Ctx

transform : {θ : Δ ⊑ Γ} → LiveExpr σ θ → Δ ⊑ Γ' → Expr σ Γ'
transform (Var x) θ' = Var (ref-o θ')
transform (App {θ₁ = θ₁} {θ₂ = θ₂} e₁ e₂) θ' =
  App
    (transform e₁ (un-∪₁ θ₁ θ₂ ₒ θ'))
    (transform e₂ (un-∪₂ θ₁ θ₂ ₒ θ'))
transform (Lam {θ = θ} e₁) θ' =
  Lam (transform e₁ (un-pop θ ₒ θ' os))
transform (Let {θ₁ = θ₁} {θ₂ = θ₂ o'} e₁ e₂) θ' =
  transform e₂ (un-∪₂ θ₁ θ₂  ₒ θ')
transform (Let {θ₁ = θ₁} {θ₂ = θ₂ os} e₁ e₂) θ' =
  Let
    (transform e₁ (un-∪₁ θ₁ θ₂ ₒ θ'))
    (transform e₂ ((un-∪₂ θ₁ θ₂ ₒ θ') os))
transform (Val v) θ' =
  Val v
transform (Plus {θ₁ = θ₁} {θ₂ = θ₂} e₁ e₂) θ' =
  Plus
    (transform e₁ (un-∪₁ θ₁ θ₂ ₒ θ'))
    (transform e₂ (un-∪₂ θ₁ θ₂ ₒ θ'))

-- eval ∘ transform ≡ evalLive
transform-correct :
  {θ : Δ ⊑ Γ} (e : LiveExpr σ θ) (θ' : Δ ⊑ Γ') (env : Env Γ') →
  eval (transform e θ') env ≡ evalLive e env θ'
transform-correct (Var x) θ' env =
  refl
transform-correct (App {θ₁ = θ₁} {θ₂ = θ₂} e₁ e₂) θ' env =
  cong₂ _$_
    (transform-correct e₁ (un-∪₁ θ₁ θ₂ ₒ θ') env)
    (transform-correct e₂ (un-∪₂ θ₁ θ₂ ₒ θ') env)
transform-correct (Lam {θ = θ} e₁) θ' env =
  extensionality _ _ λ v →
    transform-correct e₁ (un-pop θ ₒ θ' os) (Cons v env)
transform-correct (Let {θ₁ = θ₁} {θ₂ = θ₂ o'} e₁ e₂) θ' env =
  transform-correct e₂ (un-∪₂ θ₁ θ₂ ₒ θ') env
transform-correct (Let {θ₁ = θ₁} {θ₂ = θ₂ os} e₁ e₂) θ' env =
  trans
    (transform-correct e₂ _ (Cons (eval (transform e₁ _) env) env))
    (cong (λ x → evalLive e₂ (Cons x env) _)
      (transform-correct e₁ _ env))
transform-correct (Val v) θ' env =
  refl
transform-correct (Plus {θ₁ = θ₁} {θ₂ = θ₂} e₁ e₂) θ' env =
  cong₂ _+_
    (transform-correct e₁ (un-∪₁ θ₁ θ₂ ₒ θ') env)
    (transform-correct e₂ (un-∪₂ θ₁ θ₂ ₒ θ') env)

dbe : Expr σ Γ → Expr σ ⇑ Γ
dbe e = let Δ , θ , le = analyse e in transform le oi ↑ θ

dbe-correct :
  (e : Expr σ Γ) (env : Env Γ) →
  let e' ↑ θ = dbe e
  in eval e' (project-Env θ env) ≡ eval e env
dbe-correct e env =
  let Δ , θ , le = analyse e
  in
    eval (transform le oi) (project-Env θ env)
  ≡⟨ transform-correct le oi (project-Env θ env) ⟩
    evalLive le (project-Env θ env) oi
  ≡⟨ evalLive-correct le env oi θ ⟩
    eval (forget le) env
  ≡⟨ cong (λ x → eval x env) (analyse-preserves e) ⟩
    eval e env
  ∎

-- ITERATION

num-bindings' : Expr σ ⇑ Γ → ℕ
num-bindings' (e ↑ _) = num-bindings e

module <-num-bindings-Well-founded { Γ σ } where
  open Inverse-image-Well-founded {Expr σ ⇑ Γ} _<_ num-bindings' public

  wf : WF.Well-founded _⊰_
  wf = ii-wf <-ℕ-wf

_<-bindings_ : (e₁ e₂ : Expr σ ⇑ Γ) → Set
e₁ <-bindings e₂ = num-bindings' e₁ < num-bindings' e₂

<-bindings-wf : WF.Well-founded (_<-bindings_ {σ} {Γ})
<-bindings-wf = wf
  where
    open <-num-bindings-Well-founded

-- Keep optimising as long as the number of bindings decreases.
-- This is not structurally recursive, but we have a Well-Foundedness proof.
fix-dbe-wf : (e : Expr σ ⇑ Γ) → WF.Acc _<-bindings_ e → Expr σ ⇑ Γ
fix-dbe-wf (e ↑ θ) (WF.acc g) with num-bindings' (thin⇑ θ (dbe e)) <? num-bindings' (e ↑ θ)
... | inj₂ p = thin⇑ θ (dbe e)
... | inj₁ p = fix-dbe-wf (thin⇑ θ (dbe e)) (g (thin⇑ θ (dbe e)) p)

fix-dbe : Expr σ Γ → Expr σ ⇑ Γ
fix-dbe e = fix-dbe-wf (e ↑ oi) (<-bindings-wf (e ↑ oi))

fix-dbe-wf-lemma : 
  (e : Expr σ Δ) (θ : Δ ⊑ Γ) (env : Env Γ) (accu : WF.Acc _<-bindings_ (e ↑ θ)) →
  let e' ↑ θ' = dbe e
      e'' ↑ θ'' = fix-dbe-wf (e ↑ θ) accu
  in eval e'' (project-Env θ'' env) ≡ eval e' (project-Env (θ' ₒ θ) env)

fix-dbe-wf-correct : 
  (e : Expr σ Δ) (θ : Δ ⊑ Γ) (env : Env Γ) (accu : WF.Acc _<-bindings_ (e ↑ θ)) →
  let e' ↑ θ' = fix-dbe-wf (e ↑ θ) accu
  in eval e' (project-Env θ' env) ≡ eval e (project-Env θ env)

fix-dbe-wf-lemma e θ env (WF.acc g) with num-bindings' (thin⇑ θ (dbe e)) <? num-bindings' (e ↑ θ)
... | inj₂ p = refl
... | inj₁ p =
  let e' ↑ θ' = dbe e
  in fix-dbe-wf-correct e' (θ' ₒ θ) env (g (thin⇑ θ (dbe e)) p)

fix-dbe-wf-correct e θ env accu =
  let e' ↑ θ' = dbe e
      e'' ↑ θ'' = fix-dbe-wf (e ↑ θ) accu
  in
    eval e'' (project-Env θ'' env)
  ≡⟨ fix-dbe-wf-lemma e θ env accu ⟩
    eval e' (project-Env (θ' ₒ θ) env)
  ≡⟨ cong (eval e') (law-project-Env-ₒ θ' θ env) ⟩
    eval e' (project-Env θ' (project-Env θ env))
  ≡⟨ dbe-correct e (project-Env θ env) ⟩
    eval e (project-Env θ env)
  ∎

fix-dbe-correct : 
  (e : Expr σ Γ) (env : Env Γ) →
  let e' ↑ θ = fix-dbe e
  in eval e' (project-Env θ env) ≡ eval e env
fix-dbe-correct e env =
  trans
    (fix-dbe-wf-correct e oi env (<-bindings-wf (e ↑ oi)))
    (cong (eval e) (law-project-Env-oi env))
