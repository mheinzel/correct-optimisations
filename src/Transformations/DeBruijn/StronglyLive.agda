{-# OPTIONS --allow-unsolved-metas #-}  -- TODO: finish proof

-- Live variable analysis, without SubCtx
module Transformations.DeBruijn.StronglyLive where

open import Data.Nat using (_+_)
open import Data.List using (List ; _∷_ ; [])
open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; cong₂ ; sym; trans)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Function using (_$_ ; _∘_)

open import Postulates using (extensionality)
open import Data.Thinning

open import Language.Core
open Language.Core.Env {U} {⟦_⟧}
open Language.Core.Ref {U} {⟦_⟧}
open import Language.DeBruijn

private
  variable
    σ τ : U
    Γ Γ' Γ₁ Γ₂ Δ Δ' Δ₁ Δ₂ : Ctx

-- Free variables from declaration of a binding are only live, if the body uses the binding.
combine-domain : (θ₁ : Δ₁ ⊑ Γ) (θ₂ : Δ₂ ⊑ (σ ∷ Γ)) → Ctx
combine-domain {Δ₂ = Δ₂} θ₁ (o' θ₂) = Δ₂
combine-domain           θ₁ (os θ₂) = ∪-domain θ₁ θ₂

combine : (θ₁ : Δ₁ ⊑ Γ) (θ₂ : Δ₂ ⊑ (σ ∷ Γ)) → combine-domain θ₁ θ₂ ⊑ Γ
combine θ₁ (o' θ₂) = θ₂
combine θ₁ (os θ₂) = θ₁ ∪ θ₂

-- TODO: bind implicit variables explicitly in an order that makes pattern matching on them nicer?
-- TODO: Or just make thinnings normal arguments?
data LiveExpr {Γ : Ctx} : U → {Δ : Ctx} → Δ ⊑ Γ → Set where
  Var :
    (x : Ref σ Γ) →
    LiveExpr σ (o-Ref x)
  App :
    {θ₁ : Δ₁ ⊑ Γ} {θ₂ : Δ₂ ⊑ Γ} →
    LiveExpr (σ ⇒ τ) θ₁ →
    LiveExpr σ θ₂ →
    LiveExpr τ (θ₁ ∪ θ₂)
  Lam :
    {θ : Δ ⊑ (σ ∷ Γ)} →
    LiveExpr τ θ →
    LiveExpr (σ ⇒ τ) (pop θ)
  Let :
    {θ₁ : Δ₁ ⊑ Γ} {θ₂ : Δ₂ ⊑ (σ ∷ Γ)} →
    LiveExpr σ θ₁ →
    LiveExpr τ θ₂ →
    LiveExpr τ (combine θ₁ θ₂)
  Val :
    ⟦ σ ⟧ →
    LiveExpr σ oe
  Plus :
    {θ₁ : Δ₁ ⊑ Γ} {θ₂ : Δ₂ ⊑ Γ} →
    LiveExpr NAT θ₁ →
    LiveExpr NAT θ₂ →
    LiveExpr NAT (θ₁ ∪ θ₂)

-- forget the information about variable usage
forget : {θ : Δ ⊑ Γ} → LiveExpr σ θ → Expr σ Γ
forget (Var x) = Var x
forget (App e₁ e₂) = App (forget e₁) (forget e₂)
forget (Lam e₁) = Lam (forget e₁)
forget (Let e₁ e₂) = Let (forget e₁) (forget e₂)
forget (Val v) = Val v
forget (Plus e₁ e₂) = Plus (forget e₁) (forget e₂)

-- decide which variables are used or not
analyse : Expr σ Γ → Σ[ Δ ∈ Ctx ] Σ[ θ ∈ (Δ ⊑ Γ) ] LiveExpr σ θ
analyse (Var {σ} x) =
  σ ∷ [] , o-Ref x , Var x
analyse (App e₁ e₂) =
  let Δ₁ , θ₁ , le₁ = analyse e₁
      Δ₂ , θ₂ , le₂ = analyse e₂
  in ∪-domain θ₁ θ₂ , (θ₁ ∪ θ₂) , App le₁ le₂
analyse (Lam e₁) =
  let Δ₁ , θ₁ , le₁ = analyse e₁
  in pop-domain θ₁ , pop θ₁ , Lam le₁
analyse (Let e₁ e₂) =
  let Δ₁ , θ₁ , le₁ = analyse e₁
      Δ₂ , θ₂ , le₂ = analyse e₂
  in combine-domain θ₁ θ₂ , combine θ₁ θ₂ , Let le₁ le₂
analyse (Val v) =
  [] , oe , Val v
analyse (Plus e₁ e₂) =
  let Δ₁ , θ₁ , le₁ = analyse e₁
      Δ₂ , θ₂ , le₂ = analyse e₂
  in ∪-domain θ₁ θ₂ , (θ₁ ∪ θ₂) , Plus le₁ le₂

-- forget ∘ analyse ≡ id
analyse-preserves :
  (e : Expr σ Γ) →
  let _ , _ , le = analyse e
  in forget le ≡ e
analyse-preserves (Var x) = refl
analyse-preserves (App e₁ e₂) = cong₂ App (analyse-preserves e₁) (analyse-preserves e₂)
analyse-preserves (Lam e₁) = cong Lam (analyse-preserves e₁)
analyse-preserves (Let e₁ e₂) = cong₂ Let (analyse-preserves e₁) (analyse-preserves e₂)
analyse-preserves (Val v) = refl
analyse-preserves (Plus e₁ e₂) = cong₂ Plus (analyse-preserves e₁) (analyse-preserves e₂)

evalLive : {θ : Δ ⊑ Γ} → LiveExpr τ θ → Env Γ' → Δ ⊑ Γ' → ⟦ τ ⟧
evalLive (Var x) env θ' =
  lookup (ref-o θ') env
evalLive (App {θ₁ = θ₁} {θ₂ = θ₂} e₁ e₂) env θ' =
  evalLive e₁ env (un-∪₁ θ₁ θ₂ ₒ θ')
    (evalLive e₂ env (un-∪₂ θ₁ θ₂ ₒ θ'))
evalLive (Lam {θ = θ} e₁) env θ' =
  λ v → evalLive e₁ (Cons v env) (un-pop θ ₒ os θ')
evalLive (Let {θ₁ = θ₁} {θ₂ = o' θ₂} e₁ e₂) env θ' =
  evalLive e₂ env θ' 
evalLive (Let {θ₁ = θ₁} {θ₂ = os θ₂} e₁ e₂) env θ' =
  evalLive e₂
    (Cons (evalLive e₁ env (un-∪₁ θ₁ θ₂ ₒ θ')) env)
    (os (un-∪₂ θ₁ θ₂ ₒ θ'))
evalLive (Val v) env θ' =
  v
evalLive (Plus {θ₁ = θ₁} {θ₂ = θ₂} e₁ e₂) env θ' =
  evalLive e₁ env (un-∪₁ θ₁ θ₂ ₒ θ')
    + evalLive e₂ env (un-∪₂ θ₁ θ₂ ₒ θ')

law-lookup-ref-o :
  (x : Ref σ Γ) (env : Env Γ) (θ' : (σ ∷ []) ⊑ Γ') (θ'' : Γ' ⊑ Γ) →
  (o-Ref x ≡ θ' ₒ θ'') →
  lookup (ref-o θ') (project-Env θ'' env) ≡ lookup x env
law-lookup-ref-o (Pop x) (Cons v env) θ'      (o' θ'') H = law-lookup-ref-o x env θ' θ'' (law-inj-o' _ _ H)
law-lookup-ref-o (Pop x) (Cons v env) (o' θ') (os θ'') H = law-lookup-ref-o x env θ' θ'' (law-inj-o' _ _ H)
law-lookup-ref-o Top     (Cons v env) (os θ') (os θ'') H = refl
  
evalLive-correct :
  {θ : Δ ⊑ Γ} (e : LiveExpr σ θ) (env : Env Γ) (θ' : Δ ⊑ Γ') (θ'' : Γ' ⊑ Γ) →
  evalLive e (project-Env θ'' env) θ' ≡ eval (forget e) env
evalLive-correct {θ = θ} (Var x) env θ' θ'' =
  -- law-lookup-ref-o x env θ' θ'' ?
  trans
    (sym (law-lookup-rename-Ref (ref-o θ') θ'' env))
    {!foo!}
evalLive-correct (App e₁ e₂) env θ' θ'' =
  cong₂ _$_
    (evalLive-correct e₁ env _ θ'')
    (evalLive-correct e₂ env _ θ'')
evalLive-correct (Lam e₁) env θ' θ'' =
  extensionality _ _ λ v →
    evalLive-correct e₁ (Cons v env) _ (os θ'')
evalLive-correct (Let {θ₂ = o' _} e₁ e₂) env θ' θ'' =
  evalLive-correct e₂ (Cons (eval (forget e₁) env) env) θ' (o' θ'')
evalLive-correct (Let {θ₂ = os _} e₁ e₂) env θ' θ'' =
    evalLive e₂ (Cons (evalLive e₁ (project-Env θ'' env) _) (project-Env θ'' env)) _
  ≡⟨ evalLive-correct e₂ (Cons (evalLive e₁ (project-Env θ'' env) _) env) _ (os θ'') ⟩
    eval (forget e₂) (Cons (evalLive e₁ (project-Env θ'' env) _) env)
  ≡⟨ cong (λ x → eval (forget e₂) (Cons x env)) (evalLive-correct e₁ env _ θ'') ⟩
    eval (forget e₂) (Cons (eval (forget e₁) env) env)
  ∎
evalLive-correct (Val v) env θ' θ'' =
  refl
evalLive-correct (Plus e₁ e₂) env θ' θ'' =
  cong₂ _+_
    (evalLive-correct e₁ env _ θ'')
    (evalLive-correct e₂ env _ θ'')

  
evalLive-correct' :
  {θ : Δ ⊑ Γ} (e : LiveExpr σ θ) (env : Env Γ) (θ' : Δ ⊑ Γ') (θ'' : Γ' ⊑ Γ) →
  θ ≡ θ' ₒ θ'' →
  evalLive e (project-Env θ'' env) θ' ≡ eval (forget e) env
evalLive-correct' {θ = θ} (Var x) env θ' θ'' H =
  -- foo x env θ' θ''
  trans
    (sym (law-lookup-rename-Ref (ref-o θ') θ'' env))
    {!!}
evalLive-correct' (App {θ₁ = θ₁} {θ₂ = θ₂} e₁ e₂) env θ' θ'' H =
  cong₂ _$_
    (evalLive-correct' e₁ env _ θ'' {!sym (law-∪₁-inv θ₁ θ₂)!})
    (evalLive-correct' e₂ env _ θ'' {!!})
evalLive-correct' (Lam e₁) env θ' θ'' H =
  extensionality _ _ λ v →
    evalLive-correct' e₁ (Cons v env) _ (os θ'') {!!}
evalLive-correct' (Let {θ₂ = o' _} e₁ e₂) env θ' θ'' H =
  evalLive-correct' e₂ (Cons (eval (forget e₁) env) env) θ' (o' θ'') {!!}
evalLive-correct' (Let {θ₂ = os _} e₁ e₂) env θ' θ'' H =
    evalLive e₂ (Cons (evalLive e₁ (project-Env θ'' env) _) (project-Env θ'' env)) _
  ≡⟨ evalLive-correct' e₂ (Cons (evalLive e₁ (project-Env θ'' env) _) env) _ (os θ'') {!!} ⟩
    eval (forget e₂) (Cons (evalLive e₁ (project-Env θ'' env) _) env)
  ≡⟨ cong (λ x → eval (forget e₂) (Cons x env)) (evalLive-correct' e₁ env _ θ'' {!!}) ⟩
    eval (forget e₂) (Cons (eval (forget e₁) env) env)
  ∎
evalLive-correct' (Val v) env θ' θ'' H =
  refl
evalLive-correct' (Plus e₁ e₂) env θ' θ'' H =
  cong₂ _+_
    (evalLive-correct' e₁ env _ θ'' {!!})
    (evalLive-correct' e₂ env _ θ'' {!!})

lemma-evalLive :
  {θ : Δ ⊑ Γ} (e : LiveExpr σ θ) (env : Env Γ') (θ' : Δ ⊑ Γ') →
  evalLive e (project-Env θ' env) oi ≡ evalLive e env θ'
lemma-evalLive (Var x) env θ' = {!!}
lemma-evalLive (App e₁ e₂) env θ' =
  {!lemma-evalLive e₁ env !}
lemma-evalLive (Lam e₁) env θ' = {!!}
lemma-evalLive (Let e₁ e₂) env θ' = {!!}
lemma-evalLive (Val v) env θ' = {!!}
lemma-evalLive (Plus e₁ e₂) env θ' = {!!}

{-
lemma-evalLive' :
  {θ : Δ ⊑ Γ} (e : LiveExpr σ θ) (env : Env Γ') (ϕ : Δ' ⊑ Δ) →
  evalLive e (project-Env ϕ env) θ ≡ evalLive e env (ϕ ₒ θ)
lemma-evalLive' = ?
-}

evalLive-correct'' :
  {θ : Δ ⊑ Γ} (e : LiveExpr σ θ) (env : Env Γ) →
  evalLive e env θ ≡ eval (forget e) env
evalLive-correct'' (Var x) env =
  cong (λ x' → lookup x' env) (law-ref-o-Ref x)
evalLive-correct'' (App e₁ e₂) env = {!!}
evalLive-correct'' (Lam e₁) env = {!!}
evalLive-correct'' (Let {θ₂ = o' θ₂} e₁ e₂) env =
  trans
    {!lemma-evalLive e₂ (Cons _ env) (o' θ₂)!}
    (evalLive-correct'' e₂ (Cons _ env))
evalLive-correct'' (Let {θ₂ = os θ₂} e₁ e₂) env =
  {!!}
evalLive-correct'' (Val v) env = {!!}
evalLive-correct'' (Plus e₁ e₂) env = {!!}

evalLive-correct''' :
  {θ : Δ ⊑ Γ} (e : LiveExpr σ θ) (env : Env Γ) →
  evalLive e env θ ≡ eval (forget e) env
evalLive-correct''' (Var x) env =
  {! cong (λ x' → lookup x' env) (law-ref-o-Ref x) !}
evalLive-correct''' (App e₁ e₂) env = {!!}
evalLive-correct''' (Lam e₁) env = {!!}
evalLive-correct''' (Let {θ₂ = o' θ₂} e₁ e₂) env =
  {!!}
evalLive-correct''' (Let {θ₂ = os θ₂} e₁ e₂) env =
  {!!}
evalLive-correct''' (Val v) env = {!!}
evalLive-correct''' (Plus e₁ e₂) env = {!!}
