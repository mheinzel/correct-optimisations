{-# OPTIONS --allow-unsolved-metas #-}  -- TODO: finish (slightly nicer?) alternative proof

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
open import Data.Thinning

open import Language.Core
open Language.Core.Env {U} {⟦_⟧}
open Language.Core.Ref {U} {⟦_⟧}
open import Language.DeBruijn

private
  variable
    σ τ : U
    Γ : Ctx

-- Note that we cannot avoid renaming the subexpressions at each layer (quadratic complexity).
dbe : Expr σ Γ → Expr σ ⇑ Γ
dbe (Var x) =
  Var Top ↑ o-Ref x
dbe (App e₁ e₂) =
  let e₁' ↑ θ₁ = dbe e₁
      e₂' ↑ θ₂ = dbe e₂
  in App (rename-Expr (un-∪₁ θ₁ θ₂) e₁')
         (rename-Expr (un-∪₂ θ₁ θ₂) e₂')
     ↑ (θ₁ ∪ θ₂)
dbe (Lam e₁) =
  let e₁' ↑ θ = dbe e₁
  in Lam (rename-Expr (un-pop θ) e₁') ↑ pop θ
dbe (Let e₁ e₂) with dbe e₁ | dbe e₂
... | e₁' ↑ θ₁  | e₂' ↑ o' θ₂ =
  e₂' ↑ θ₂
... | e₁' ↑ θ₁  | e₂' ↑ os θ₂ =
  Let (rename-Expr (un-∪₁ θ₁ θ₂) e₁')
      (rename-Expr (os (un-∪₂ θ₁ θ₂)) e₂')
  ↑ (θ₁ ∪ θ₂)
dbe (Val v) =
  Val v ↑ oe
dbe (Plus e₁ e₂) =
  let e₁' ↑ θ₁ = dbe e₁
      e₂' ↑ θ₂ = dbe e₂
  in Plus (rename-Expr (un-∪₁ θ₁ θ₂) e₁')
          (rename-Expr (un-∪₂ θ₁ θ₂) e₂')
     ↑ (θ₁ ∪ θ₂)

dbe-correct-Var :
  (x : Ref σ Γ) (env : Env Γ) →
  lookup Top (project-Env (o-Ref x) env) ≡ lookup x env
dbe-correct-Var Top (Cons v env) = refl
dbe-correct-Var (Pop x) (Cons v env) = dbe-correct-Var x env
  
dbe-correct :
  (e : Expr σ Γ) (env : Env Γ) →
  let e' ↑ θ = dbe e
  in eval e' (project-Env θ env) ≡ eval e env
dbe-correct (Var x) env =
  dbe-correct-Var x env
dbe-correct (App e₁ e₂) env =
  let e₁' ↑ θ₁ = dbe e₁
      e₂' ↑ θ₂ = dbe e₂
  in
    cong₂ _$_
      (trans
        (law-eval-rename-Expr e₁' _ _)
        (trans
          (cong (eval e₁') (trans (sym (law-project-Env-ₒ (un-∪₁ θ₁ θ₂) (θ₁ ∪ θ₂) env))
                                  (cong (λ x → project-Env x env) (law-∪₁-inv θ₁ θ₂))))
          (dbe-correct e₁ env)))
      (trans
        (law-eval-rename-Expr e₂' _ _)
        (trans
          (cong (eval e₂') (trans (sym (law-project-Env-ₒ (un-∪₂ θ₁ θ₂) (θ₁ ∪ θ₂) env))
                                  (cong (λ x → project-Env x env) (law-∪₂-inv θ₁ θ₂))))
          (dbe-correct e₂ env)))
dbe-correct (Lam e₁) env =
  let e₁' ↑ θ₁ = dbe e₁
  in extensionality _ _ λ v →
      eval (rename-Expr (un-pop θ₁) e₁') (project-Env (os (pop θ₁)) (Cons v env))
    ≡⟨ law-eval-rename-Expr e₁' (un-pop θ₁) (project-Env (os (pop θ₁)) (Cons v env)) ⟩
      eval e₁' (project-Env (un-pop θ₁) (project-Env (os (pop θ₁)) (Cons v env)))
    ≡⟨ cong (eval e₁') (sym (law-project-Env-ₒ (un-pop θ₁) (os (pop θ₁)) (Cons v env))) ⟩
      eval e₁' (project-Env (un-pop θ₁ ₒ os (pop θ₁)) (Cons v env))
    ≡⟨ cong (λ x → eval e₁' (project-Env x (Cons v env))) (law-pop-inv θ₁) ⟩
      eval e₁' (project-Env θ₁ (Cons v env))
    ≡⟨ dbe-correct e₁ (Cons v env) ⟩
      eval e₁ (Cons v env)
    ∎
dbe-correct (Let e₁ e₂) env with dbe e₁ | dbe e₂ | dbe-correct e₁ | dbe-correct e₂
... | e₁' ↑ θ₁ | e₂' ↑ o' θ₂ | h₁ | h₂ =
  h₂ (Cons (eval e₁ env) env)
... | e₁' ↑ θ₁ | e₂' ↑ os θ₂ | h₁ | h₂ =
  let v = eval (rename-Expr (un-∪₁ θ₁ θ₂) e₁') (project-Env (θ₁ ∪ θ₂) env)
  in
    eval (rename-Expr (os (un-∪₂ θ₁ θ₂)) e₂') (Cons v (project-Env (θ₁ ∪ θ₂) env))
  ≡⟨ law-eval-rename-Expr e₂' _ _ ⟩
    eval e₂' (Cons _ (project-Env (un-∪₂ θ₁ θ₂) (project-Env (θ₁ ∪ θ₂) env)))
  ≡⟨ cong (λ x → eval e₂' (Cons v x)) (sym (law-project-Env-ₒ (un-∪₂ θ₁ θ₂) (θ₁ ∪ θ₂) env)) ⟩
    eval e₂' (Cons _ (project-Env (un-∪₂ θ₁ θ₂ ₒ (θ₁ ∪ θ₂)) env))
  ≡⟨ cong (λ x → eval e₂' (Cons v (project-Env x env))) (law-∪₂-inv θ₁ θ₂) ⟩
    eval e₂' (Cons _ (project-Env θ₂ env))
  ≡⟨ h₂ (Cons _ env) ⟩
    eval e₂ (Cons _ env)
  ≡⟨ refl ⟩
    eval e₂ (Cons (eval (rename-Expr (un-∪₁ θ₁ θ₂) e₁') (project-Env (θ₁ ∪ θ₂) env)) env)
  ≡⟨ cong (λ x → eval e₂ (Cons x env)) (law-eval-rename-Expr e₁' _ _) ⟩
    eval e₂ (Cons (eval e₁' (project-Env (un-∪₁ θ₁ θ₂) (project-Env (θ₁ ∪ θ₂) env))) env)
  ≡⟨ cong (λ x → eval e₂ (Cons (eval e₁' x) env)) (sym (law-project-Env-ₒ (un-∪₁ θ₁ θ₂) (θ₁ ∪ θ₂) env)) ⟩
    eval e₂ (Cons (eval e₁' (project-Env (un-∪₁ θ₁ θ₂ ₒ (θ₁ ∪ θ₂)) env)) env)
  ≡⟨ cong (λ x → eval e₂ (Cons (eval e₁' (project-Env x env)) env)) (law-∪₁-inv θ₁ θ₂) ⟩
    eval e₂ (Cons (eval e₁' (project-Env θ₁ env)) env)
  ≡⟨ cong (λ x → eval e₂ (Cons x env)) (h₁ env) ⟩
    eval e₂ (Cons (eval e₁ env) env)
  ∎
dbe-correct (Val v) env =
  refl
dbe-correct (Plus e₁ e₂) env =
  let e₁' ↑ θ₁ = dbe e₁
      e₂' ↑ θ₂ = dbe e₂
  in
    cong₂ _+_
      (trans
        (law-eval-rename-Expr e₁' _ _)
        (trans
          (cong (eval e₁') (trans (sym (law-project-Env-ₒ (un-∪₁ θ₁ θ₂) (θ₁ ∪ θ₂) env))
                                  (cong (λ x → project-Env x env) (law-∪₁-inv θ₁ θ₂))))
          (dbe-correct e₁ env)))
      (trans
        (law-eval-rename-Expr e₂' _ _)
        (trans
          (cong (eval e₂') (trans (sym (law-project-Env-ₒ (un-∪₂ θ₁ θ₂) (θ₁ ∪ θ₂) env))
                                  (cong (λ x → project-Env x env) (law-∪₂-inv θ₁ θ₂))))
          (dbe-correct e₂ env)))

dbe-correct' :
  (e : Expr σ Γ) (env : Env Γ) →
  let e' ↑ θ = dbe e
  in eval (rename-Expr θ e') env ≡ eval e env
dbe-correct' (Var x) env =
  cong (λ x → lookup x env) (law-rename-Ref-o-Ref x)
dbe-correct' (App e₁ e₂) env =
  let e₁' ↑ θ₁ = dbe e₁
      e₂' ↑ θ₂ = dbe e₂
  in
    cong₂ _$_
        (trans
            (cong (λ x → eval x env)
            (trans
                (sym (law-rename-Expr-ₒ e₁' (un-∪₁ θ₁ θ₂) (θ₁ ∪ θ₂)))
                (cong (λ x → rename-Expr x e₁') (law-∪₁-inv θ₁ θ₂))))
            (dbe-correct' e₁ env))
        (trans
            (cong (λ x → eval x env)
            (trans
                (sym (law-rename-Expr-ₒ e₂' (un-∪₂ θ₁ θ₂) (θ₁ ∪ θ₂)))
                (cong (λ x → rename-Expr x e₂') (law-∪₂-inv θ₁ θ₂))))
            (dbe-correct' e₂ env))
dbe-correct' (Lam e₁) env =
  let e₁' ↑ θ = dbe e₁
  in extensionality _ _ λ v →
      eval (rename-Expr (os (pop θ)) (rename-Expr (un-pop θ) e₁')) (Cons v env)
    ≡⟨ cong (λ x → eval x (Cons v env)) (sym (law-rename-Expr-ₒ e₁' (un-pop θ) (os (pop θ)))) ⟩
      eval (rename-Expr (un-pop θ ₒ os (pop θ)) e₁') (Cons v env)
    ≡⟨ cong (λ x → eval (rename-Expr x e₁') (Cons v env)) (law-pop-inv θ) ⟩
      eval (rename-Expr θ e₁') (Cons v env)
    ≡⟨ dbe-correct' e₁ (Cons v env) ⟩
      eval e₁ (Cons v env)
    ∎
dbe-correct' (Let e₁ e₂) env with dbe e₁ | dbe e₂ | dbe-correct' e₁ | dbe-correct' e₂
... | e₁' ↑ θ₁ | e₂' ↑ o' θ₂ | h₁ | h₂ =
  trans
    -- TODO: doable, but kind of gets annoying...
    (sym {!law-eval-rename-Expr (rename-Expr θ₂ e₂') (o' oi) (Cons (eval e₁ env) env)!})
    (h₂ (Cons (eval e₁ env) env))
  -- h₂ (Cons (eval e₁ env) env)
... | e₁' ↑ θ₁  | e₂' ↑ os θ₂ | h₁ | h₂ =
  -- let v = eval (rename-Expr (un-∪₁ θ₁ θ₂ ₒ (θ₁ ∪ θ₂)) e₁') env
  let v = eval (rename-Expr (θ₁ ∪ θ₂) (rename-Expr (un-∪₁ θ₁ θ₂) e₁')) env
  in
    eval (rename-Expr (os (θ₁ ∪ θ₂)) (rename-Expr (os (un-∪₂ θ₁ θ₂)) e₂')) (Cons v env)
  ≡⟨ {!!} ⟩
  -- ≡⟨ law-eval-rename-Expr e₂' _ _ ⟩
  --   eval e₂' (Cons _ (project-Env (un-∪₂ θ₁ θ₂) (project-Env (θ₁ ∪ θ₂) env)))
  -- ≡⟨ cong (λ x → eval e₂' (Cons v x)) (sym (law-project-Env-ₒ (un-∪₂ θ₁ θ₂) (θ₁ ∪ θ₂) env)) ⟩
  --   eval e₂' (Cons _ (project-Env (un-∪₂ θ₁ θ₂ ₒ (θ₁ ∪ θ₂)) env))
  -- ≡⟨ cong (λ x → eval e₂' (Cons v (project-Env x env))) (law-∪₂-inv θ₁ θ₂) ⟩
  --   eval e₂' (Cons _ (project-Env θ₂ env))
  -- ≡⟨ h₂ (Cons _ env) ⟩
    eval e₂ (Cons v env)
  -- ≡⟨ refl ⟩
  --   eval e₂ (Cons (eval (rename-Expr (un-∪₁ θ₁ θ₂) e₁') (project-Env (θ₁ ∪ θ₂) env)) env)
  -- ≡⟨ cong (λ x → eval e₂ (Cons x env)) (law-eval-rename-Expr e₁' _ _) ⟩
  --   eval e₂ (Cons (eval e₁' (project-Env (un-∪₁ θ₁ θ₂) (project-Env (θ₁ ∪ θ₂) env))) env)
  -- ≡⟨ cong (λ x → eval e₂ (Cons (eval e₁' x) env)) (sym (law-project-Env-ₒ (un-∪₁ θ₁ θ₂) (θ₁ ∪ θ₂) env)) ⟩
  --   eval e₂ (Cons (eval e₁' (project-Env (un-∪₁ θ₁ θ₂ ₒ (θ₁ ∪ θ₂)) env)) env)
  -- ≡⟨ cong (λ x → eval e₂ (Cons (eval e₁' (project-Env x env)) env)) (law-∪₁-inv θ₁ θ₂) ⟩
  --   eval e₂ (Cons (eval e₁' (project-Env θ₁ env)) env)
  -- ≡⟨ cong (λ x → eval e₂ (Cons x env)) (h₁ env) ⟩
  ≡⟨ {!!} ⟩
    eval e₂ (Cons (eval e₁ env) env)
  ∎
dbe-correct' (Val v) env =
  refl
dbe-correct' (Plus e₁ e₂) env =
  let e₁' ↑ θ₁ = dbe e₁
      e₂' ↑ θ₂ = dbe e₂
  in
    cong₂ _+_
        (trans
            (cong (λ x → eval x env)
            (trans
                (sym (law-rename-Expr-ₒ e₁' (un-∪₁ θ₁ θ₂) (θ₁ ∪ θ₂)))
                (cong (λ x → rename-Expr x e₁') (law-∪₁-inv θ₁ θ₂))))
            (dbe-correct' e₁ env))
        (trans
            (cong (λ x → eval x env)
            (trans
                (sym (law-rename-Expr-ₒ e₂' (un-∪₂ θ₁ θ₂) (θ₁ ∪ θ₂)))
                (cong (λ x → rename-Expr x e₂') (law-∪₂-inv θ₁ θ₂))))
            (dbe-correct' e₂ env))
