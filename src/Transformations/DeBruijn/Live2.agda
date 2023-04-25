{-# OPTIONS --allow-unsolved-metas #-}  -- TODO: finish proof

-- Live variable analysis, without SubCtx
module Transformations.DeBruijn.Live2 where

open import Data.Nat using (_+_)
open import Data.List using (List ; _∷_ ; [])
open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; cong₂ ; sym; trans)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Function using (_$_ ; _∘_)

open import Postulates using (extensionality)
open import Data.OPE

open import Language.Core
open Language.Core.Env {U} {⟦_⟧}
open Language.Core.Ref {U} {⟦_⟧}
open import Language.DeBruijn
open import Language.CoDeBruijn using (o-Ref ; ref-o ; ref-o-Ref≡id ; project-Env)  -- TODO: put somewhere else

private
  variable
    σ τ : U
    Γ Γ' Γ₁ Γ₂ Δ Δ₁ Δ₂ : Ctx

-- TODO: bind implicit variables explicitly in an order that makes pattern matching on them nicer?
-- IDEA: in Let, add explicit KeepBinding/RemBinding field to match on instead of Δ₂?
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
    LiveExpr τ (θ₁ ∪ pop θ₂)
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
analyse (Var {σ} x) = σ ∷ [] , o-Ref x , Var x
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
  in ∪-domain θ₁ (pop θ₂) , (θ₁ ∪ pop θ₂) , Let le₁ le₂
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
  evalLive e₁ env (Δ₁⊑∪-domain θ₁ θ₂ ₒ θ')
    (evalLive e₂ env (Δ₂⊑∪-domain θ₁ θ₂ ₒ θ'))
evalLive (Lam {θ = θ} e₁) env θ' =
  λ v → evalLive e₁ (Cons v env) (un-pop θ ₒ θ' os)
evalLive (Let {θ₁ = θ₁} {θ₂ = θ₂ o'} e₁ e₂) env θ' =
  evalLive e₂ env (Δ₂⊑∪-domain θ₁ θ₂ ₒ θ')
evalLive (Let {θ₁ = θ₁} {θ₂ = θ₂ os} e₁ e₂) env θ' =
  evalLive e₂
    (Cons (evalLive e₁ env (Δ₁⊑∪-domain θ₁ θ₂ ₒ θ')) env)
    ((Δ₂⊑∪-domain θ₁ θ₂ ₒ θ') os)
evalLive (Val v) env θ' =
  v
evalLive (Plus {θ₁ = θ₁} {θ₂ = θ₂} e₁ e₂) env θ' =
  evalLive e₁ env (Δ₁⊑∪-domain θ₁ θ₂ ₒ θ')
    + evalLive e₂ env (Δ₂⊑∪-domain θ₁ θ₂ ₒ θ')

lookup-ref-o-project-Env :
  {θ : (σ ∷ []) ⊑ Γ} (θ' : (σ ∷ []) ⊑ Γ') (θ'' : Γ' ⊑ Γ) (x : Ref σ Γ) (env : Env Γ) → θ ≡ θ' ₒ θ'' →
  lookup (ref-o θ') (project-Env θ'' env) ≡ lookup (ref-o (o-Ref x)) env
lookup-ref-o-project-Env θ θ' x env H = {!!}

evalLive-project-Env :
  {θ : Δ ⊑ Γ} (θ' : Δ ⊑ Γ') (θ'' : Γ' ⊑ Γ) (e : LiveExpr σ θ) (env : Env Γ) → θ ≡ θ' ₒ θ'' →
  evalLive e (project-Env θ'' env) θ' ≡ evalLive e env (θ' ₒ θ'')
evalLive-project-Env θ' θ'' (Var x) env H = {!!}
evalLive-project-Env θ' θ'' (App {θ₁ = θ₁} {θ₂ = θ₂} e₁ e₂) env H =
  let h₁ = evalLive-project-Env (Δ₁⊑∪-domain θ₁ θ₂ ₒ θ') θ'' e₁ env
             (trans (trans (sym (law-∪₁-inv θ₁ θ₂)) (cong (_ ₒ_) H)) (law-ₒₒ (Δ₁⊑∪-domain θ₁ θ₂) θ' θ''))
  in {!h₁!}
evalLive-project-Env θ' θ'' (Lam {θ = θ} e₁) env H =
  extensionality _ _ λ v →
    trans
      (evalLive-project-Env (un-pop θ ₒ θ' os) (θ'' os) e₁ (Cons v env) {!!})
      (cong (evalLive e₁ (Cons v env)) (sym (law-ₒₒ (un-pop θ) (θ' os) (θ'' os))))
evalLive-project-Env θ' θ'' (Let {θ₁ = θ₁} {θ₂ = θ₂} e₁ e₂) env H = {!!}
evalLive-project-Env θ' θ'' (Val x) env H = {!!}
evalLive-project-Env θ' θ'' (Plus {θ₁ = θ₁} {θ₂ = θ₂} e₁ e₂) env H = {!!}

-- evalLive ≡ eval ∘ forget
evalLive-correct :
  {θ : Δ ⊑ Γ} (e : LiveExpr σ θ) (env : Env Γ) → -- (θ' : Δ ⊑ Γ') (θ'' : Γ' ⊑ Γ) →
  evalLive e env θ ≡ eval (forget e) env
  -- evalLive e (project-Env θ'' env) θ' ≡ eval (forget e) env
evalLive-correct (Var x) env =
  cong (λ x₁ → lookup x₁ env) (ref-o-Ref≡id x)
evalLive-correct (App {θ₁ = θ₁} {θ₂ = θ₂} e₁ e₂) env =
  cong₂ _$_
    (trans (cong (evalLive e₁ env) (law-∪₁-inv θ₁ θ₂)) (evalLive-correct e₁ env))
    (trans (cong (evalLive e₂ env) (law-∪₂-inv θ₁ θ₂)) (evalLive-correct e₂ env))
evalLive-correct (Lam {θ = θ} e₁) env =
  extensionality _ _ λ v →
    trans (cong (evalLive e₁ (Cons v env)) (law-pop-inv θ)) (evalLive-correct e₁ (Cons v env))
evalLive-correct (Let {θ₁ = θ₁} {θ₂ = θ₂ o'} e₁ e₂) env =
  trans
    {!evalLive-project-Env (Δ₂⊑∪-domain θ₁ θ₂ ₒ ?) (oi o') e₂ (Cons ? env) ?!}
    (evalLive-correct e₂ (Cons (eval (forget e₁) env) env))
evalLive-correct (Let {θ₁ = θ₁} {θ₂ = θ₂ os} e₁ e₂) env =
  {!!}
  {-
    evalLive e₂ (Cons (evalLive e₁ env _) env) _
  ≡⟨ trans (cong (evalLive e₂ _) (trans (cong ((un-pop θ₂ ₒ_) ∘ _os) (law-∪₂-inv θ₁ (pop θ₂))) (law-pop-inv θ₂)))
           (evalLive-correct e₂ (Cons _ env)) ⟩
    eval (forget e₂) (Cons (evalLive e₁ env _) env)
  ≡⟨ cong (λ x → eval (forget e₂) (Cons x env)) (trans (cong (evalLive e₁ env) (law-∪₁-inv θ₁ (pop θ₂)))
                                                       (evalLive-correct e₁ env)) ⟩
    eval (forget e₂) (Cons (eval (forget e₁) env) env)
  ∎
  -}
evalLive-correct (Val x) env =
  refl
evalLive-correct (Plus {θ₁ = θ₁} {θ₂ = θ₂} e₁ e₂) env =
  cong₂ _+_
    (trans (cong (evalLive e₁ env) (law-∪₁-inv θ₁ θ₂)) (evalLive-correct e₁ env))
    (trans (cong (evalLive e₂ env) (law-∪₂-inv θ₁ θ₂)) (evalLive-correct e₂ env))


evalLive-correct' :
  {θ : Δ ⊑ Γ} (e : LiveExpr σ θ) (env : Env Γ) (θ' : Δ ⊑ Γ') (θ'' : Γ' ⊑ Γ) → θ ≡ θ' ₒ θ'' →
  evalLive e (project-Env θ'' env) θ' ≡ eval (forget e) env
evalLive-correct' = {!!}
