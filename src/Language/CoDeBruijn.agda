-- using co-de-Bruijn representation
module Language.CoDeBruijn where

open import Data.Unit
open import Data.Nat using (_+_)
open import Data.List using (List ; _∷_ ; [] ; _++_)
open import Data.Product
open import Function using (_∘_ ; _$_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; cong₂ ; sym ; trans)
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import Postulates using (extensionality)
open import Data.Thinning
open import Data.Relevant

open import Language.Core
open Language.Core.Env {U} {⟦_⟧}
open Language.Core.Ref {U} {⟦_⟧}
import Language.DeBruijn as DeBruijn

private
  variable
    σ τ τ₁ τ₂ : U
    Γ Γ₁ Γ₂ Γ₃ Δ : List U

data Expr : (σ : U) (Γ : Ctx) → Set where
  Var :
    Expr σ (σ ∷ [])
  App :
    (Expr (σ ⇒ τ) ×ᴿ Expr σ) Γ →
    Expr τ Γ
  Lam :
    ((σ ∷ []) ⊢ Expr τ) Γ →
    Expr (σ ⇒ τ) Γ
  Let :
    (Expr σ ×ᴿ ((σ ∷ []) ⊢ Expr τ)) Γ →
    Expr τ Γ
  Val :
    (v : ⟦ σ ⟧) →
    Expr σ []
  Plus :
    (Expr NAT ×ᴿ Expr NAT) Γ →
    Expr NAT Γ

-- TODO: Pass thinning as last argument?
eval : Expr τ Δ → Δ ⊑ Γ → Env Γ → ⟦ τ ⟧
eval Var θ env =
  lookup (ref-o θ) env
eval (App (pairᴿ (e₁ ↑ θ₁) (e₂ ↑ θ₂) cover)) θ env =
  eval e₁ (θ₁ ₒ θ) env
    (eval e₂ (θ₂ ₒ θ) env)
eval (Lam (ψ \\ e)) θ env =
  λ v → eval e (ψ ++⊑ θ) (Cons v env)
eval (Let (pairᴿ (e₁ ↑ θ₁) ((ψ \\ e₂) ↑ θ₂) c)) θ env =
  eval e₂ (ψ ++⊑ (θ₂ ₒ θ))
    (Cons (eval e₁ (θ₁ ₒ θ) env) env)
eval (Val v) θ env =
  v
eval (Plus (pairᴿ (e₁ ↑ θ₁) (e₂ ↑ θ₂) cover)) θ env =
    eval e₁ (θ₁ ₒ θ) env
  + eval e₂ (θ₂ ₒ θ) env

eval-binop : (eval-step : ⟦ τ₁ ⟧ → ⟦ τ₂ ⟧ → ⟦ τ ⟧) → (Expr τ₁ ×ᴿ Expr τ₂) Δ → Δ ⊑ Γ → Env Γ → ⟦ τ ⟧
eval-binop eval-step (pairᴿ (e₁ ↑ θ₁) (e₂ ↑ θ₂) c) ϕ env =
  eval-step (eval e₁ (θ₁ ₒ ϕ) env) (eval e₂ (θ₂ ₒ ϕ) env)

lemma-eval-Var :
  (env : Env Γ₃) (θ : (σ ∷ []) ⊑ Γ₂) (ϕ : Γ₂ ⊑ Γ₃) →
  lookup (ref-o (θ ₒ ϕ)) env ≡ lookup (ref-o θ) (project-Env ϕ env)
lemma-eval-Var (Cons x env) θ      (o' ϕ) = lemma-eval-Var env θ ϕ
lemma-eval-Var (Cons x env) (o' θ) (os ϕ) = lemma-eval-Var env θ ϕ
lemma-eval-Var (Cons x env) (os θ) (os ϕ) = refl

-- TODO: clean up, factor out?
lemma-eval :
  (e : Expr τ Γ₁) (env : Env Γ₃) (θ : Γ₁ ⊑ Γ₂) (ϕ : Γ₂ ⊑ Γ₃) →
  eval e (θ ₒ ϕ) env ≡ eval e θ (project-Env ϕ env)
lemma-eval Var env θ ϕ =
  lemma-eval-Var env θ ϕ
lemma-eval (App (pairᴿ (e₁ ↑ θ₁) (e₂ ↑ θ₂) c)) env θ ϕ =
  cong₂ _$_
    (trans (cong (λ x → eval e₁ x env) (law-ₒₒ θ₁ θ ϕ)) (lemma-eval e₁ env (θ₁ ₒ θ) ϕ))
    (trans (cong (λ x → eval e₂ x env) (law-ₒₒ θ₂ θ ϕ)) (lemma-eval e₂ env (θ₂ ₒ θ) ϕ))
lemma-eval (Lam (ψ \\ e)) env θ ϕ =
  extensionality _ _ λ v →
    let h = trans (cong (λ x → x ++⊑ (θ ₒ ϕ)) (sym (law-ₒoi ψ))) (law-commute-ₒ++⊑ ψ oi θ ϕ)
    in trans (cong (λ x → eval e x (Cons v env)) h) (lemma-eval e (Cons v env) (ψ ++⊑ θ) (os ϕ))
lemma-eval (Let (pairᴿ (e₁ ↑ θ₁) ((ψ \\ e₂) ↑ θ₂) c)) env θ ϕ =
  let h₁ = lemma-eval e₁ env (θ₁ ₒ θ) ϕ
      h₂ = lemma-eval e₂ (Cons (eval e₁ (θ₁ ₒ θ) (project-Env ϕ env)) env) (ψ ++⊑ (θ₂ ₒ θ)) (os ϕ)
      shuffle  = trans (cong₂ _++⊑_ (sym (law-ₒoi ψ)) (law-ₒₒ θ₂ θ ϕ)) (law-commute-ₒ++⊑ ψ oi (θ₂ ₒ θ) ϕ)
      H₁ = cong (λ x → Cons x (project-Env ϕ env)) (trans (cong (λ x → eval e₁ x env) (law-ₒₒ θ₁ θ ϕ)) h₁)
  in  trans
        (cong (λ x → eval e₂ _ (Cons x env)) (trans (cong (λ x → eval e₁ x env) (law-ₒₒ θ₁ θ ϕ)) h₁))
        (trans (cong (λ x → eval e₂ x _) shuffle) h₂)
lemma-eval (Val v) env θ ϕ = refl
lemma-eval (Plus (pairᴿ (e₁ ↑ θ₁) (e₂ ↑ θ₂) c)) env θ ϕ =
  cong₂ _+_
    (trans (cong (λ x → eval e₁ x env) (law-ₒₒ θ₁ θ ϕ)) (lemma-eval e₁ env (θ₁ ₒ θ) ϕ))
    (trans (cong (λ x → eval e₂ x env) (law-ₒₒ θ₂ θ ϕ)) (lemma-eval e₂ env (θ₂ ₒ θ) ϕ))

lemma-eval-Let :
  {Γₑ Γ : Ctx} (p : (Expr σ ×ᴿ ((σ ∷ []) ⊢ Expr τ)) Γ) (env : Env Γₑ) (θ : Γ ⊑ Γₑ) →
  let pairᴿ (e₁ ↑ θ₁) ((ψ \\ e₂) ↑ θ₂) c = p
  in  eval (Let p) θ env ≡ eval (App (pairᴿ ((Lam (ψ \\ e₂)) ↑ θ₂) (e₁ ↑ θ₁) (cover-flip c))) θ env
lemma-eval-Let p env θ = refl


-- CONVERSION

-- decide which variables are used or not
tighten : DeBruijn.Expr σ Γ → Expr σ ⇑ Γ
tighten (DeBruijn.Var x) =
  Var ↑ o-Ref x
tighten (DeBruijn.App e₁ e₂) =
  map⇑ App (tighten e₁ ,ᴿ tighten e₂)
tighten (DeBruijn.Lam e) =
  map⇑ Lam (_ \\ᴿ tighten e)
tighten (DeBruijn.Let e₁ e₂) =
  map⇑ Let (tighten e₁ ,ᴿ (_ \\ᴿ tighten e₂))
tighten (DeBruijn.Val v) =
  Val v ↑ oe
tighten (DeBruijn.Plus e₁ e₂) =
  map⇑ Plus (tighten e₁ ,ᴿ tighten e₂)

relax : Δ ⊑ Γ → Expr σ Δ → DeBruijn.Expr σ Γ
relax θ Var =
  DeBruijn.Var (ref-o θ)
relax θ (App (pairᴿ (e₁ ↑ θ₁) (e₂ ↑ θ₂) cover)) =
  DeBruijn.App (relax (θ₁ ₒ θ) e₁) (relax (θ₂ ₒ θ) e₂)
relax θ (Lam (ψ \\ e)) =
  DeBruijn.Lam (relax (ψ ++⊑ θ) e)
relax θ (Let (pairᴿ (e₁ ↑ θ₁) ((ψ \\ e₂) ↑ θ₂) c)) =
  DeBruijn.Let (relax (θ₁ ₒ θ) e₁) (relax (ψ ++⊑ (θ₂ ₒ θ)) e₂)
relax θ (Val v) =
  DeBruijn.Val v
relax θ (Plus (pairᴿ (e₁ ↑ θ₁) (e₂ ↑ θ₂) cover)) =
  DeBruijn.Plus (relax (θ₁ ₒ θ) e₁) (relax (θ₂ ₒ θ) e₂)


tighten-correct :
  (e : DeBruijn.Expr τ Γ) (env : Env Γ) →
  let e' ↑ θ = tighten e
  in eval e' θ env ≡ DeBruijn.eval e env
tighten-correct (DeBruijn.Var x) env =
  cong (λ x₁ → lookup x₁ env) (law-ref-o-Ref x)
tighten-correct (DeBruijn.App e₁ e₂) env
  with tighten e₁ | tighten e₂ | tighten-correct e₁ env | tighten-correct e₂ env
...  | e₁' ↑ θ₁   | e₂' ↑ θ₂   | h₁                     | h₂
  with cop θ₁ θ₂
...  | coproduct _ ψ ϕ₁ ϕ₂ refl refl c =
    eval e₁' (ϕ₁ ₒ ψ) env (eval e₂' (ϕ₂ ₒ ψ) env)
  ≡⟨ cong₂ _$_ h₁ h₂ ⟩
    DeBruijn.eval e₁ env (DeBruijn.eval e₂ env)
  ∎
tighten-correct (DeBruijn.Lam e) env
  with tighten e  | tighten-correct e
...  | e' ↑ θ' | h
  with (_ ∷ []) ⊣ θ'
... | split ϕ₁ ϕ₂ (refl , refl) =
  extensionality _ _ λ v →
    h (Cons v env)
tighten-correct (DeBruijn.Let e₁ e₂) env
  with tighten e₁  | tighten e₂  | tighten-correct e₁ env | tighten-correct e₂ (Cons (DeBruijn.eval e₁ env) env)
...  | e₁' ↑ θ₁    | e₂' ↑ θ₂    | h₁                     | h₂
  with (_ ∷ []) ⊣ θ₂
... | split ψ θ₂' (refl , refl)
  with cop θ₁ θ₂'
...  | coproduct _ θ ϕ₁ ϕ₂ refl refl c =
    eval e₂' (ψ ++⊑ (ϕ₂ ₒ θ)) (Cons (eval e₁' (ϕ₁ ₒ θ) env) env)
  ≡⟨ cong (λ x → eval e₂' _ (Cons x env)) h₁ ⟩
    eval e₂' (ψ ++⊑ (ϕ₂ ₒ θ)) (Cons (DeBruijn.eval e₁ env) env)
  ≡⟨ h₂ ⟩
    DeBruijn.eval e₂ (Cons (DeBruijn.eval e₁ env) env)
  ∎
tighten-correct (DeBruijn.Val v) env =
  refl
tighten-correct (DeBruijn.Plus e₁ e₂) env
  with tighten e₁ | tighten e₂ | tighten-correct e₁ env | tighten-correct e₂ env
...  | e₁' ↑ θ₁   | e₂' ↑ θ₂   | h₁                     | h₂
  with cop θ₁ θ₂
...  | coproduct _ ψ ϕ₁ ϕ₂ refl refl c =
    eval e₁' (ϕ₁ ₒ ψ) env + eval e₂' (ϕ₂ ₒ ψ) env
  ≡⟨ cong₂ _+_ h₁ h₂ ⟩
    DeBruijn.eval e₁ env + DeBruijn.eval e₂ env
  ∎

relax-correct :
  (e : Expr τ Δ) (env : Env Γ) (θ : Δ ⊑ Γ) →
  let e' = relax θ e
  in DeBruijn.eval e' env ≡ eval e θ env
relax-correct Var env θ =
  refl
relax-correct (App (pairᴿ (e₁ ↑ θ₁) (e₂ ↑ θ₂) _)) env θ =
  cong₂ _$_ (relax-correct e₁ env (θ₁ ₒ θ)) (relax-correct e₂ env (θ₂ ₒ θ))
relax-correct (Lam (ψ \\ e)) env θ =
  extensionality _ _ λ v →
    relax-correct e (Cons v env) (ψ ++⊑ θ)
relax-correct (Let (pairᴿ (e₁ ↑ θ₁) ((ψ \\ e₂) ↑ θ₂) _)) env θ =
  trans
    (cong (λ x → DeBruijn.eval (relax _ e₂) (Cons x env)) (relax-correct e₁ env (θ₁ ₒ θ)))
    (relax-correct e₂ (Cons (eval e₁ (θ₁ ₒ θ) env) env) (ψ ++⊑ (θ₂ ₒ θ)))
relax-correct (Val v) env θ =
  refl
relax-correct (Plus (pairᴿ (e₁ ↑ θ₁) (e₂ ↑ θ₂) _)) env θ =
  cong₂ _+_ (relax-correct e₁ env (θ₁ ₒ θ)) (relax-correct e₂ env (θ₂ ₒ θ))
