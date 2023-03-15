-- using co-de-Bruijn representation
module Language.CoDeBruijn where

open import Data.Unit
open import Data.Nat using (_+_)
open import Data.List using (List ; _∷_ ; [] ; _++_)
open import Data.Product
open import Function using (_∘_ ; _$_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; cong₂ ; sym ; trans)
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import Data.OPE

open import Language.Core
open Language.Core.Env {U} {⟦_⟧}
open Language.Core.Ref {U} {⟦_⟧}
import Language.DeBruijn as DeBruijn
open import Language.CoDeBruijn.Core {U}

-- This is needed because our notion of semantical equivalence is "same evaluation result",
-- and values include Agda functions.
-- We might want something different?
postulate
  extensionality :
    {S : Set} {T : S -> Set} (f g : (x : S) -> T x) ->
    ((x : S) -> f x ≡ g x) ->
    f ≡ g

private
  variable
    σ τ : U
    Γ : List U

module _ where
  -- OPEs from a singleton context are isomorphic to Ref.
  o-Ref : Ref τ Γ → (τ ∷ []) ⊑ Γ
  o-Ref Top     = oe os
  o-Ref (Pop x) = (o-Ref x) o'

  ref-o : (τ ∷ []) ⊑ Γ → Ref τ Γ
  ref-o (θ o') = Pop (ref-o θ)
  ref-o (θ os) = Top

  project-Env : ∀ {Γ₁ Γ₂} → Γ₁ ⊑ Γ₂ → Env Γ₂ → Env Γ₁
  project-Env oz     env          = env
  project-Env (θ os) (Cons v env) = Cons v (project-Env θ env)
  project-Env (θ o') (Cons v env) = project-Env θ env

  law-project-Env-ₒ :
    ∀ {Γ₁ Γ₂ Γ₃} (θ : Γ₁ ⊑ Γ₂) (ϕ : Γ₂ ⊑ Γ₃) (env : Env Γ₃) →
    project-Env (θ ₒ ϕ) env ≡ project-Env θ (project-Env ϕ env)
  law-project-Env-ₒ θ (ϕ o') (Cons v env) = law-project-Env-ₒ θ ϕ env
  law-project-Env-ₒ (θ o') (ϕ os) (Cons v env) = law-project-Env-ₒ θ ϕ env
  law-project-Env-ₒ (θ os) (ϕ os) (Cons v env) = cong (Cons v) (law-project-Env-ₒ θ ϕ env)
  law-project-Env-ₒ oz oz env = refl

  law-project-Env-oi : (env : Env Γ) → project-Env oi env ≡ env
  law-project-Env-oi Nil = refl
  law-project-Env-oi (Cons x env) = cong (Cons x) (law-project-Env-oi env)

data Expr : (σ : U) (Γ : Ctx) → Set where
  Var :
    ∀ {σ} →
    Expr σ (σ ∷ [])
  App :
    ∀ {σ τ Γ} →
    (Expr (σ ⇒ τ) ×ᴿ Expr σ) Γ →
    Expr τ Γ
  Lam :
    ∀ {σ τ Γ} →
    ((σ ∷ []) ⊢ Expr τ) Γ →
    Expr (σ ⇒ τ) Γ
  Let :
    ∀ {σ τ Γ} →
    (Expr σ ×ᴿ ((σ ∷ []) ⊢ Expr τ)) Γ →
    Expr τ Γ
  Val :
    ∀ {σ} →
    (v : ⟦ σ ⟧) →
    Expr σ []
  Plus :
    ∀ {Γ} →
    (Expr NAT ×ᴿ Expr NAT) Γ →
    Expr NAT Γ

eval : ∀ {Γ' Γ} → Expr τ Γ' → Γ' ⊑ Γ → Env Γ → ⟦ τ ⟧
eval Var ϕ env =
  lookup Top (project-Env ϕ env)
eval (App (pairᴿ (e₁ ↑ θ₁) (e₂ ↑ θ₂) cover)) ϕ env =
  eval e₁ (θ₁ ₒ ϕ) env
    (eval e₂ (θ₂ ₒ ϕ) env)
eval (Lam {σ} (θ \\ e)) ϕ env =
  λ v → eval e (θ ++⊑ ϕ) (Cons v env)
eval (Let (pairᴿ (e₁ ↑ θ₁) ((ψ \\ e₂) ↑ θ₂) c)) ϕ env =
  eval e₂ (ψ ++⊑ (θ₂ ₒ ϕ))
    (Cons (eval e₁ (θ₁ ₒ ϕ) env) env)
eval (Val v) ϕ env =
  v
eval (Plus (pairᴿ (e₁ ↑ θ₁) (e₂ ↑ θ₂) cover)) ϕ env =
    eval e₁ (θ₁ ₒ ϕ) env
  + eval e₂ (θ₂ ₒ ϕ) env

eval-binop : ∀ {Γ' Γ τ₁ τ₂ τ} → (eval-step : ⟦ τ₁ ⟧ → ⟦ τ₂ ⟧ → ⟦ τ ⟧) → (Expr τ₁ ×ᴿ Expr τ₂) Γ' → Γ' ⊑ Γ → Env Γ → ⟦ τ ⟧
eval-binop eval-step (pairᴿ (e₁ ↑ θ₁) (e₂ ↑ θ₂) c) ϕ env =
  eval-step (eval e₁ (θ₁ ₒ ϕ) env) (eval e₂ (θ₂ ₒ ϕ) env)

-- TODO: clean up, factor out?
lemma-eval :
  ∀ {Γ₁ Γ₂ Γ₃ τ} →
  (e : Expr τ Γ₁) (env : Env Γ₃) (θ : Γ₁ ⊑ Γ₂) (ϕ : Γ₂ ⊑ Γ₃) →
  eval e (θ ₒ ϕ) env ≡ eval e θ (project-Env ϕ env)
lemma-eval Var env θ ϕ = cong (lookup Top) (law-project-Env-ₒ θ ϕ env)
lemma-eval (App (pairᴿ (e₁ ↑ θ₁) (e₂ ↑ θ₂) c)) env θ ϕ =
  cong₂ _$_
    (trans (cong (λ x → eval e₁ x env) (law-ₒₒ θ₁ θ ϕ)) (lemma-eval e₁ env (θ₁ ₒ θ) ϕ))
    (trans (cong (λ x → eval e₂ x env) (law-ₒₒ θ₂ θ ϕ)) (lemma-eval e₂ env (θ₂ ₒ θ) ϕ))
lemma-eval (Lam (ψ \\ e)) env θ ϕ =
  extensionality _ _ λ v →
    let h = trans (cong (λ x → x ++⊑ (θ ₒ ϕ)) (sym (law-ₒoi ψ))) (law-commute-ₒ++⊑ ψ oi θ ϕ)
    in trans (cong (λ x → eval e x (Cons v env)) h) (lemma-eval e (Cons v env) (ψ ++⊑ θ) (ϕ os))
lemma-eval (Let (pairᴿ (e₁ ↑ θ₁) ((ψ \\ e₂) ↑ θ₂) c)) env θ ϕ =
  let h₁ = lemma-eval e₁ env (θ₁ ₒ θ) ϕ
      h₂ = lemma-eval e₂ (Cons (eval e₁ (θ₁ ₒ θ) (project-Env ϕ env)) env) (ψ ++⊑ (θ₂ ₒ θ)) (ϕ os)
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
into : DeBruijn.Expr Γ σ → Expr σ ⇑ Γ
into (DeBruijn.Var {σ} x) =
  Var {σ} ↑ o-Ref x
into (DeBruijn.App e₁ e₂) =
  map⇑ App (into e₁ ,ᴿ into e₂)
into (DeBruijn.Lam e) =
  map⇑ Lam ((_ ∷ []) \\R into e)
into (DeBruijn.Let e₁ e₂) =
  map⇑ Let (into e₁ ,ᴿ ((_ ∷ []) \\R into e₂))
into (DeBruijn.Val v) =
  (Val v) ↑ oe
into (DeBruijn.Plus e₁ e₂) =
  map⇑ Plus (into e₁ ,ᴿ into e₂)

from : ∀ {Γ' Γ σ} → Γ' ⊑ Γ → Expr σ Γ' → DeBruijn.Expr Γ σ
from θ Var =
  DeBruijn.Var (ref-o θ)
from θ (App (pairᴿ (e₁ ↑ ϕ₁) (e₂ ↑ ϕ₂) cover)) =
  DeBruijn.App (from (ϕ₁ ₒ θ) e₁) (from (ϕ₂ ₒ θ) e₂)
from θ (Lam (ψ \\ e)) =
  DeBruijn.Lam (from (ψ ++⊑ θ) e)
from θ (Let (pairᴿ (e₁ ↑ θ₁) ((ψ \\ e₂) ↑ θ₂) c)) =
  DeBruijn.Let (from (θ₁ ₒ θ) e₁) (from (ψ ++⊑ (θ₂ ₒ θ)) e₂)
from θ (Val v) =
  DeBruijn.Val v
from θ (Plus (pairᴿ (e₁ ↑ θ₁) (e₂ ↑ θ₂) cover)) =
  DeBruijn.Plus (from (θ₁ ₒ θ) e₁) (from (θ₂ ₒ θ) e₂)

-- TODO: prove into/from semantics preserving!
into-correct-Ref : (x : Ref τ Γ) (env : Env Γ) → lookup Top (project-Env (o-Ref x) env) ≡ lookup x env
into-correct-Ref Top (Cons v env) = refl
into-correct-Ref (Pop x) (Cons v env) = into-correct-Ref x env

into-correct :
  (e : DeBruijn.Expr Γ τ) (env : Env Γ) →
  let e' ↑ θ' = into e
  in eval e' θ' env ≡ DeBruijn.eval e env
into-correct (DeBruijn.Var x) env =
  into-correct-Ref x env
into-correct (DeBruijn.App e₁ e₂) env
  with into e₁  | into e₂  | into-correct e₁ env | into-correct e₂ env
...  | e₁' ↑ θ₁ | e₂' ↑ θ₂ | h₁                  | h₂
  with cop θ₁ θ₂
...  | coproduct _ ψ ϕ₁ ϕ₂ refl refl c =
    eval e₁' (ϕ₁ ₒ ψ) env (eval e₂' (ϕ₂ ₒ ψ) env)
  ≡⟨ cong₂ _$_ h₁ h₂ ⟩
    DeBruijn.eval e₁ env (DeBruijn.eval e₂ env)
  ∎
into-correct (DeBruijn.Lam e) env
  with into e  | into-correct e
...  | e' ↑ θ' | h
  with (_ ∷ []) ⊣ θ'
... | ⊣r ϕ₁ ϕ₂ (refl , refl) =
  extensionality _ _ λ v →
    h (Cons v env)
into-correct (DeBruijn.Let e₁ e₂) env
  with into e₁  | into e₂  | into-correct e₁ env | into-correct e₂ (Cons (DeBruijn.eval e₁ env) env)
...  | e₁' ↑ θ₁ | e₂' ↑ θ₂ | h₁                  | h₂
  with (_ ∷ []) ⊣ θ₂
... | ⊣r ψ θ₂' (refl , refl)
  with cop θ₁ θ₂'
...  | coproduct _ θ ϕ₁ ϕ₂ refl refl c =
    eval e₂' (ψ ++⊑ (ϕ₂ ₒ θ)) (Cons (eval e₁' (ϕ₁ ₒ θ) env) env)
  ≡⟨ cong (λ x → eval e₂' _ (Cons x env)) h₁ ⟩
    eval e₂' (ψ ++⊑ (ϕ₂ ₒ θ)) (Cons (DeBruijn.eval e₁ env) env)
  ≡⟨ h₂ ⟩
    DeBruijn.eval e₂ (Cons (DeBruijn.eval e₁ env) env)
  ∎
into-correct (DeBruijn.Val v) env =
  refl
into-correct (DeBruijn.Plus e₁ e₂) env
  with into e₁  | into e₂  | into-correct e₁ env | into-correct e₂ env
...  | e₁' ↑ θ₁ | e₂' ↑ θ₂ | h₁                  | h₂
  with cop θ₁ θ₂
...  | coproduct _ ψ ϕ₁ ϕ₂ refl refl c =
    eval e₁' (ϕ₁ ₒ ψ) env + eval e₂' (ϕ₂ ₒ ψ) env
  ≡⟨ cong₂ _+_ h₁ h₂ ⟩
    DeBruijn.eval e₁ env + DeBruijn.eval e₂ env
  ∎

from-correct-Var : (θ : (σ ∷ []) ⊑ Γ) (env : Env Γ) → lookup (ref-o θ) env ≡ lookup Top (project-Env θ env)
from-correct-Var (θ o') (Cons x env) = from-correct-Var θ env
from-correct-Var (θ os) (Cons x env) = refl

from-correct :
  ∀ {Γ' Γ τ} (e : Expr τ Γ') (env : Env Γ) (θ : Γ' ⊑ Γ) →
  let e' = from θ e
  in DeBruijn.eval e' env ≡ eval e θ env
from-correct Var env θ =
  from-correct-Var θ env
from-correct (App (pairᴿ (e₁ ↑ θ₁) (e₂ ↑ θ₂) _)) env θ =
  cong₂ _$_ (from-correct e₁ env (θ₁ ₒ θ)) (from-correct e₂ env (θ₂ ₒ θ))
from-correct (Lam (ψ \\ e)) env θ =
  extensionality _ _ λ v →
    from-correct e (Cons v env) (ψ ++⊑ θ)
from-correct (Let (pairᴿ (e₁ ↑ θ₁) ((ψ \\ e₂) ↑ θ₂) _)) env θ =
  trans
    (cong (λ x → DeBruijn.eval (from _ e₂) (Cons x env)) (from-correct e₁ env (θ₁ ₒ θ)))
    (from-correct e₂ (Cons (eval e₁ (θ₁ ₒ θ) env) env) (ψ ++⊑ (θ₂ ₒ θ)))
from-correct (Val v) env θ =
  refl
from-correct (Plus (pairᴿ (e₁ ↑ θ₁) (e₂ ↑ θ₂) _)) env θ =
  cong₂ _+_ (from-correct e₁ env (θ₁ ₒ θ)) (from-correct e₂ env (θ₂ ₒ θ))
