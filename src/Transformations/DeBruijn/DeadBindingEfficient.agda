-- Dead Binding Elimination (simple),
-- but ideally without quadratic complexity for renaming.
module Transformations.DeBruijn.DeadBindingEfficient where

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
open import Transformations.DeBruijn.Live2
open import Language.CoDeBruijn using (o-Ref ; ref-o; ref-o-Ref≡id; project-Env; law-project-Env-ₒ; law-project-Env-oi)  -- TODO: put somewhere else

private
  variable
    σ τ : U
    Γ Γ' Δ : Ctx

dbe : {θ : Δ ⊑ Γ} → LiveExpr σ θ → Δ ⊑ Γ' → Expr σ Γ'
dbe (Var x) θ' = Var (ref-o θ')
dbe (App {θ₁ = θ₁} {θ₂ = θ₂} e₁ e₂) θ' =
  App
    (dbe e₁ (Δ₁⊑∪-domain θ₁ θ₂ ₒ θ'))
    (dbe e₂ (Δ₂⊑∪-domain θ₁ θ₂ ₒ θ'))
dbe (Lam {θ = θ} e₁) θ' =
  Lam (dbe e₁ (un-pop θ ₒ θ' os))
dbe (Let {θ₁ = θ₁} {θ₂ = θ₂ o'} e₁ e₂) θ' =
  dbe e₂ (Δ₂⊑∪-domain θ₁ θ₂  ₒ θ')
dbe (Let {θ₁ = θ₁} {θ₂ = θ₂ os} e₁ e₂) θ' =
  Let
    (dbe e₁ (Δ₁⊑∪-domain θ₁ θ₂ ₒ θ'))
    (dbe e₂ ((Δ₂⊑∪-domain θ₁ θ₂ ₒ θ') os))
dbe (Val x) θ' =
  Val x
dbe (Plus {θ₁ = θ₁} {θ₂ = θ₂} e₁ e₂) θ' =
  Plus
    (dbe e₁ (Δ₁⊑∪-domain θ₁ θ₂ ₒ θ'))
    (dbe e₂ (Δ₂⊑∪-domain θ₁ θ₂ ₒ θ'))

-- eval ∘ dbe ≡ evalLive
dbe-correct :
  {θ : Δ ⊑ Γ} (e : LiveExpr σ θ) (θ' : Δ ⊑ Γ') (env : Env Γ') →
  eval (dbe e θ') env ≡ evalLive e env θ'
dbe-correct (Var x) θ' env =
  refl
dbe-correct (App {θ₁ = θ₁} {θ₂ = θ₂} e₁ e₂) θ' env =
  cong₂ _$_
    (dbe-correct e₁ (Δ₁⊑∪-domain θ₁ θ₂ ₒ θ') env)
    (dbe-correct e₂ (Δ₂⊑∪-domain θ₁ θ₂ ₒ θ') env)
dbe-correct (Lam {θ = θ} e₁) θ' env =
  extensionality _ _ λ v →
    dbe-correct e₁ (un-pop θ ₒ θ' os) (Cons v env)
dbe-correct (Let {θ₁ = θ₁} {θ₂ = θ₂ o'} e₁ e₂) θ' env =
  dbe-correct e₂ (Δ₂⊑∪-domain θ₁ θ₂ ₒ θ') env
dbe-correct (Let {θ₁ = θ₁} {θ₂ = θ₂ os} e₁ e₂) θ' env =
  trans
    (dbe-correct e₂ _ (Cons (eval (dbe e₁ _) env) env))
    (cong (λ x → evalLive e₂ (Cons x env) _)
      (dbe-correct e₁ _ env))
dbe-correct (Val x) θ' env =
  refl
dbe-correct (Plus {θ₁ = θ₁} {θ₂ = θ₂} e₁ e₂) θ' env =
  cong₂ _+_
    (dbe-correct e₁ (Δ₁⊑∪-domain θ₁ θ₂ ₒ θ') env)
    (dbe-correct e₂ (Δ₂⊑∪-domain θ₁ θ₂ ₒ θ') env)

optimise : Expr σ Γ → Expr σ ⇑ Γ
optimise e = let Δ , θ , e' = analyse e in dbe e' oi ↑ θ

optimise-correct :
  (e : Expr σ Γ) (env : Env Γ) →
  let e' ↑ θ = optimise e
  in eval e' (project-Env θ env) ≡ eval e env
optimise-correct e env =
  let Δ , θ , le = analyse e
  in
    eval (dbe le oi) (project-Env θ env)
  ≡⟨ dbe-correct le oi (project-Env θ env) ⟩
    evalLive le (project-Env θ env) oi
  ≡⟨ evalLive-correct' le env oi θ (sym (law-oiₒ θ)) ⟩
    eval (forget le) env
  ≡⟨ cong (λ x → eval x env) (analyse-preserves e) ⟩
    eval e env
  ∎

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
fix-optimise-wf : (e : Expr σ ⇑ Γ) → WF.Acc _<-bindings_ e → Expr σ ⇑ Γ
fix-optimise-wf (e ↑ θ) (WF.acc g) with num-bindings' (thin⇑ θ (optimise e)) <? num-bindings' (e ↑ θ)
... | inj₂ p = thin⇑ θ (optimise e)
... | inj₁ p = fix-optimise-wf (thin⇑ θ (optimise e)) (g (thin⇑ θ (optimise e)) p)

fix-optimise : Expr σ Γ → Expr σ ⇑ Γ
fix-optimise e = fix-optimise-wf (e ↑ oi) (<-bindings-wf (e ↑ oi))

fix-optimise-wf-lemma : 
  (e : Expr σ Δ) (θ : Δ ⊑ Γ) (env : Env Γ) (accu : WF.Acc _<-bindings_ (e ↑ θ)) →
  let e' ↑ θ' = optimise e
      e'' ↑ θ'' = fix-optimise-wf (e ↑ θ) accu
  in eval e'' (project-Env θ'' env) ≡ eval e' (project-Env (θ' ₒ θ) env)

fix-optimise-wf-correct : 
  (e : Expr σ Δ) (θ : Δ ⊑ Γ) (env : Env Γ) (accu : WF.Acc _<-bindings_ (e ↑ θ)) →
  let e' ↑ θ' = fix-optimise-wf (e ↑ θ) accu
  in eval e' (project-Env θ' env) ≡ eval e (project-Env θ env)

fix-optimise-wf-lemma e θ env (WF.acc g) with num-bindings' (thin⇑ θ (optimise e)) <? num-bindings' (e ↑ θ)
... | inj₂ p = refl
... | inj₁ p =
  let e' ↑ θ' = optimise e
  in fix-optimise-wf-correct e' (θ' ₒ θ) env (g (thin⇑ θ (optimise e)) p)

fix-optimise-wf-correct e θ env accu =
  let e' ↑ θ' = optimise e
      e'' ↑ θ'' = fix-optimise-wf (e ↑ θ) accu
  in
    eval e'' (project-Env θ'' env)
  ≡⟨ fix-optimise-wf-lemma e θ env accu ⟩
    eval e' (project-Env (θ' ₒ θ) env)
  ≡⟨ cong (eval e') (law-project-Env-ₒ θ' θ env) ⟩
    eval e' (project-Env θ' (project-Env θ env))
  ≡⟨ optimise-correct e (project-Env θ env) ⟩
    eval e (project-Env θ env)
  ∎

fix-optimise-correct : 
  (e : Expr σ Γ) (env : Env Γ) →
  let e' ↑ θ' = fix-optimise e
  in eval e' (project-Env θ' env) ≡ eval e env
fix-optimise-correct e env =
  trans
    (fix-optimise-wf-correct e oi env (<-bindings-wf (e ↑ oi)))
    (cong (eval e) (law-project-Env-oi env))
