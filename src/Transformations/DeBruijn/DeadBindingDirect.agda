-- A simpler version of strong Dead Binding Elimination without using annotations.
module Transformations.DeBruijn.DeadBindingDirect where

open import Data.Nat using (_+_; ℕ)
open import Data.List using (List ; _∷_ ; [])
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; cong₂ ; sym ; trans)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Function using (_$_)

open import Postulates using (extensionality)
open import Data.OPE

open import Language.Core
open Language.Core.Env {U} {⟦_⟧}
open Language.Core.Ref {U} {⟦_⟧}
open import Language.DeBruijn
open import Transformations.Recursion

private
  variable
    σ τ : U
    Γ : Ctx

-- Note that we cannot avoid renaming the subexpressions at each layer (quadratic complexity).
optimise : Expr σ Γ → Expr σ ⇑ Γ
optimise (Var x) =
  Var Top ↑ o-Ref x
optimise (App e₁ e₂) =
  let e₁' ↑ θ₁ = optimise e₁
      e₂' ↑ θ₂ = optimise e₂
  in App
       (rename-Expr (Δ₁⊑∪-domain θ₁ θ₂) e₁')
       (rename-Expr (Δ₂⊑∪-domain θ₁ θ₂) e₂') ↑ (θ₁ ∪ θ₂)
optimise (Lam e₁) =
  let e₁' ↑ θ = optimise e₁
  in Lam (rename-Expr (un-pop θ) e₁') ↑ pop θ
optimise (Let e₁ e₂) with optimise e₁ | optimise e₂
... | e₁' ↑ θ₁  | e₂' ↑ θ₂ o' =
  e₂' ↑ θ₂
... | e₁' ↑ θ₁  | e₂' ↑ θ₂ os =
  Let (rename-Expr (Δ₁⊑∪-domain θ₁ θ₂) e₁') (rename-Expr (Δ₂⊑∪-domain θ₁ θ₂ os) e₂') ↑ (θ₁ ∪ θ₂)
optimise (Val v) =
  (Val v) ↑ oe
optimise (Plus e₁ e₂) =
  let e₁' ↑ θ₁ = optimise e₁
      e₂' ↑ θ₂ = optimise e₂
  in Plus
       (rename-Expr (Δ₁⊑∪-domain θ₁ θ₂) e₁')
       (rename-Expr (Δ₂⊑∪-domain θ₁ θ₂) e₂') ↑ (θ₁ ∪ θ₂)

optimise-correct-Var :
  (x : Ref σ Γ) (env : Env Γ) →
  lookup Top (project-Env (o-Ref x) env) ≡ lookup x env
optimise-correct-Var Top (Cons v env) = refl
optimise-correct-Var (Pop x) (Cons v env) = optimise-correct-Var x env
  
optimise-correct :
  (e : Expr σ Γ) (env : Env Γ) →
  let e' ↑ θ = optimise e
  in eval e' (project-Env θ env) ≡ eval e env
optimise-correct (Var x) env =
  optimise-correct-Var x env
optimise-correct (App e₁ e₂) env =
  let e₁' ↑ θ₁ = optimise e₁
      e₂' ↑ θ₂ = optimise e₂
  in
    cong₂ _$_
      (trans
        (law-eval-rename-Expr e₁' _ _)
        (trans
          (cong (eval e₁') (trans (sym (law-project-Env-ₒ (Δ₁⊑∪-domain θ₁ θ₂) (θ₁ ∪ θ₂) env))
                                  (cong (λ x → project-Env x env) (law-∪₁-inv θ₁ θ₂))))
          (optimise-correct e₁ env)))
      (trans
        (law-eval-rename-Expr e₂' _ _)
        (trans
          (cong (eval e₂') (trans (sym (law-project-Env-ₒ (Δ₂⊑∪-domain θ₁ θ₂) (θ₁ ∪ θ₂) env))
                                  (cong (λ x → project-Env x env) (law-∪₂-inv θ₁ θ₂))))
          (optimise-correct e₂ env)))
optimise-correct (Lam e₁) env =
  let e₁' ↑ θ₁ = optimise e₁
  in
  extensionality _ _ λ v →
    trans
      (law-eval-rename-Expr e₁' (un-pop θ₁) (project-Env (pop θ₁ os) (Cons v env)))
      (trans
        (cong (eval e₁') (trans
                           (sym (law-project-Env-ₒ (un-pop θ₁) (pop θ₁ os) (Cons v env)))
                           (cong (λ x → project-Env x (Cons v env)) (law-pop-inv θ₁))))
        (optimise-correct e₁ (Cons v env)))
optimise-correct (Let e₁ e₂) env with optimise e₁ | optimise e₂ | optimise-correct e₁ | optimise-correct e₂
... | e₁' ↑ θ₁ | e₂' ↑ θ₂ o' | h₁ | h₂ =
  h₂ (Cons (eval e₁ env) env)
... | e₁' ↑ θ₁  | e₂' ↑ θ₂ os | h₁ | h₂ =
  let v = eval (rename-Expr (Δ₁⊑∪-domain θ₁ θ₂) e₁') (project-Env (θ₁ ∪ θ₂) env)
  in
    eval (rename-Expr (Δ₂⊑∪-domain θ₁ θ₂ os) e₂') (Cons v (project-Env (θ₁ ∪ θ₂) env))
  ≡⟨ law-eval-rename-Expr e₂' _ _ ⟩
    eval e₂' (Cons _ (project-Env (Δ₂⊑∪-domain θ₁ θ₂) (project-Env (θ₁ ∪ θ₂) env)))
  ≡⟨ cong (λ x → eval e₂' (Cons v x)) (sym (law-project-Env-ₒ (Δ₂⊑∪-domain θ₁ θ₂) (θ₁ ∪ θ₂) env)) ⟩
    eval e₂' (Cons _ (project-Env (Δ₂⊑∪-domain θ₁ θ₂ ₒ (θ₁ ∪ θ₂)) env))
  ≡⟨ cong (λ x → eval e₂' (Cons v (project-Env x env))) (law-∪₂-inv θ₁ θ₂) ⟩
    eval e₂' (Cons _ (project-Env θ₂ env))
  ≡⟨ h₂ (Cons _ env) ⟩
    eval e₂ (Cons _ env)
  ≡⟨ refl ⟩
    eval e₂ (Cons (eval (rename-Expr (Δ₁⊑∪-domain θ₁ θ₂) e₁') (project-Env (θ₁ ∪ θ₂) env)) env)
  ≡⟨ cong (λ x → eval e₂ (Cons x env)) (law-eval-rename-Expr e₁' _ _) ⟩
    eval e₂ (Cons (eval e₁' (project-Env (Δ₁⊑∪-domain θ₁ θ₂) (project-Env (θ₁ ∪ θ₂) env))) env)
  ≡⟨ cong (λ x → eval e₂ (Cons (eval e₁' x) env)) (sym (law-project-Env-ₒ (Δ₁⊑∪-domain θ₁ θ₂) (θ₁ ∪ θ₂) env)) ⟩
    eval e₂ (Cons (eval e₁' (project-Env (Δ₁⊑∪-domain θ₁ θ₂ ₒ (θ₁ ∪ θ₂)) env)) env)
  ≡⟨ cong (λ x → eval e₂ (Cons (eval e₁' (project-Env x env)) env)) (law-∪₁-inv θ₁ θ₂) ⟩
    eval e₂ (Cons (eval e₁' (project-Env θ₁ env)) env)
  ≡⟨ cong (λ x → eval e₂ (Cons x env)) (h₁ env) ⟩
    eval e₂ (Cons (eval e₁ env) env)
  ∎
optimise-correct (Val v) env =
  refl
optimise-correct (Plus e₁ e₂) env =
  let e₁' ↑ θ₁ = optimise e₁
      e₂' ↑ θ₂ = optimise e₂
  in
    cong₂ _+_
      (trans
        (law-eval-rename-Expr e₁' _ _)
        (trans
          (cong (eval e₁') (trans (sym (law-project-Env-ₒ (Δ₁⊑∪-domain θ₁ θ₂) (θ₁ ∪ θ₂) env))
                                  (cong (λ x → project-Env x env) (law-∪₁-inv θ₁ θ₂))))
          (optimise-correct e₁ env)))
      (trans
        (law-eval-rename-Expr e₂' _ _)
        (trans
          (cong (eval e₂') (trans (sym (law-project-Env-ₒ (Δ₂⊑∪-domain θ₁ θ₂) (θ₁ ∪ θ₂) env))
                                  (cong (λ x → project-Env x env) (law-∪₂-inv θ₁ θ₂))))
          (optimise-correct e₂ env)))
