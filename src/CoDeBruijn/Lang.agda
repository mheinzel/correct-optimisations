-- using co-de-Bruijn representation
module CoDeBruijn.Lang where

open import Data.Unit
open import Data.Nat using (_+_)
open import Data.List using (List ; _∷_ ; [] ; _++_)
open import Data.Product
open import Function using (_∘_ ; _$_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; cong₂ ; sym ; trans)
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import Core
import DeBruijn.Lang as DeBruijn
open import OPE

-- This is needed because our notion of semantical equivalence is "same evaluation result",
-- and values include Agda functions.
-- We might want something different?
postulate
  extensionality :
    {S : Set} {T : S -> Set} (f g : (x : S) -> T x) ->
    ((x : S) -> f x ≡ g x) ->
    f ≡ g

data Cover : {Γ₁ Γ₂ Γ : Ctx} → Γ₁ ⊑ Γ → Γ₂ ⊑ Γ → Set where
  _c's : ∀ {Γ₁ Γ₂ Γ} → {τ : U} {θ₁ : Γ₁ ⊑ Γ} {θ₂ : Γ₂ ⊑ Γ} → Cover θ₁ θ₂ → Cover (_o' {τ} θ₁) (θ₂ os)
  _cs' : ∀ {Γ₁ Γ₂ Γ} → {τ : U} {θ₁ : Γ₁ ⊑ Γ} {θ₂ : Γ₂ ⊑ Γ} → Cover θ₁ θ₂ → Cover (_os {τ} θ₁) (θ₂ o')
  _css : ∀ {Γ₁ Γ₂ Γ} → {τ : U} {θ₁ : Γ₁ ⊑ Γ} {θ₂ : Γ₂ ⊑ Γ} → Cover θ₁ θ₂ → Cover (_os {τ} θ₁) (θ₂ os)
  czz  :                                                                   Cover oz           oz

cover-flip : {Γ₁ Γ₂ Γ : Ctx} {θ : Γ₁ ⊑ Γ} {ϕ : Γ₂ ⊑ Γ} → Cover θ ϕ → Cover ϕ θ
cover-flip (c c's) = cover-flip c cs'
cover-flip (c cs') = cover-flip c c's
cover-flip (c css) = cover-flip c css
cover-flip czz = czz

record _×R_ (S T : Scoped) (Γ : Ctx) : Set where
  constructor pair
  field
    outl  : S ⇑ Γ
    outr  : T ⇑ Γ
    cover : Cover (_⇑_.thinning outl) (_⇑_.thinning outr)

record _⊢_ (Γ' : Ctx) (T : Scoped) (Γ : Ctx) : Set where
  constructor _\\_
  field
    {bound} : Ctx
    thinning : bound ⊑ Γ'
    thing : T (bound ++ Γ)

map⊢ : ∀ {Γ₁ Γ₂ Γ} {T : Scoped} → Γ₁ ⊑ Γ₂ → (Γ₁ ⊢ T) Γ → (Γ₂ ⊢ T) Γ
map⊢ ϕ (θ \\ t) = (θ ₒ ϕ) \\ t

{- original definition
_\\R_ : {T : Scoped} (Γ' : Ctx) → T ⇑ (Γ' ++ Γ) → (Γ' ⊢ T) ⇑ Γ
Γ' \\R (t ↑ ψ)       with Γ' ⊣ ψ
Γ' \\R (t ↑ .(θ ++⊑ ϕ)) | ⊣r θ ϕ (refl , refl) = (θ \\ t) ↑ ϕ
-}

\\R-helper : ∀ {T Γ Γ' Γ''} {ψ : Γ'' ⊑ (Γ' ++ Γ)} → Γ' ⊣R ψ → T Γ'' → (Γ' ⊢ T) ⇑ Γ
\\R-helper (⊣r ϕ₁ ϕ₂ (refl , refl)) t = (ϕ₁ \\ t) ↑ ϕ₂

_\\R_ : ∀ {T Γ} (Γ' : Ctx) → T ⇑ (Γ' ++ Γ) → (Γ' ⊢ T) ⇑ Γ
Γ' \\R (t ↑ ψ) = \\R-helper (Γ' ⊣ ψ) t


data Expr : (σ : U) (Γ : Ctx) → Set where
  Var :
    ∀ {σ} →
    Expr σ (σ ∷ [])
  App :
    ∀ {σ τ Γ} →
    (Expr (σ ⇒ τ) ×R Expr σ) Γ →
    Expr τ Γ
  Lam :
    ∀ {σ τ Γ} →
    ((σ ∷ []) ⊢ Expr τ) Γ →
    Expr (σ ⇒ τ) Γ
  Let :
    ∀ {σ τ Γ} →
    (Expr σ ×R ((σ ∷ []) ⊢ Expr τ)) Γ →
    Expr τ Γ
  Val :
    ∀ {σ} →
    (v : ⟦ σ ⟧) →
    Expr σ []
  Plus :
    ∀ {Γ} →
    (Expr NAT ×R Expr NAT) Γ →
    Expr NAT Γ

eval : ∀ {Γ' Γ} → Expr τ Γ' → Γ' ⊑ Γ → Env Γ → ⟦ τ ⟧
eval Var ϕ env =
  lookup Top (project-Env ϕ env)
eval (App (pair (e₁ ↑ θ₁) (e₂ ↑ θ₂) cover)) ϕ env =
  eval e₁ (θ₁ ₒ ϕ) env
    (eval e₂ (θ₂ ₒ ϕ) env)
eval (Lam {σ} (θ \\ e)) ϕ env =
  λ v → eval e (θ ++⊑ ϕ) (Cons v env)
eval (Let (pair (e₁ ↑ θ₁) ((ψ \\ e₂) ↑ θ₂) c)) ϕ env =
  eval e₂ (ψ ++⊑ (θ₂ ₒ ϕ))
    (Cons (eval e₁ (θ₁ ₒ ϕ) env) env)
eval (Val v) ϕ env =
  v
eval (Plus (pair (e₁ ↑ θ₁) (e₂ ↑ θ₂) cover)) ϕ env =
    eval e₁ (θ₁ ₒ ϕ) env
  + eval e₂ (θ₂ ₒ ϕ) env

eval-binop : ∀ {Γ' Γ τ₁ τ₂ τ} → (eval-step : ⟦ τ₁ ⟧ → ⟦ τ₂ ⟧ → ⟦ τ ⟧) → (Expr τ₁ ×R Expr τ₂) Γ' → Γ' ⊑ Γ → Env Γ → ⟦ τ ⟧
eval-binop eval-step (pair (e₁ ↑ θ₁) (e₂ ↑ θ₂) c) ϕ env =
  eval-step (eval e₁ (θ₁ ₒ ϕ) env) (eval e₂ (θ₂ ₒ ϕ) env)

-- TODO: clean up, factor out?
lemma-eval :
  ∀ {Γ₁ Γ₂ Γ₃ τ} →
  (e : Expr τ Γ₁) (env : Env Γ₃) (θ : Γ₁ ⊑ Γ₂) (ϕ : Γ₂ ⊑ Γ₃) →
  eval e (θ ₒ ϕ) env ≡ eval e θ (project-Env ϕ env)
lemma-eval Var env θ ϕ = cong (lookup Top) (law-project-Env-ₒ θ ϕ env)
lemma-eval (App (pair (e₁ ↑ θ₁) (e₂ ↑ θ₂) c)) env θ ϕ =
  cong₂ _$_
    (trans (cong (λ x → eval e₁ x env) (law-ₒₒ θ₁ θ ϕ)) (lemma-eval e₁ env (θ₁ ₒ θ) ϕ))
    (trans (cong (λ x → eval e₂ x env) (law-ₒₒ θ₂ θ ϕ)) (lemma-eval e₂ env (θ₂ ₒ θ) ϕ))
lemma-eval (Lam (ψ \\ e)) env θ ϕ =
  extensionality _ _ λ v →
    let h = trans (cong (λ x → x ++⊑ (θ ₒ ϕ)) (sym (law-ₒoi ψ))) (law-commute-ₒ++⊑ ψ oi θ ϕ)
    in trans (cong (λ x → eval e x (Cons v env)) h) (lemma-eval e (Cons v env) (ψ ++⊑ θ) (ϕ os))
lemma-eval (Let (pair (e₁ ↑ θ₁) ((ψ \\ e₂) ↑ θ₂) c)) env θ ϕ =
  let h₁ = lemma-eval e₁ env (θ₁ ₒ θ) ϕ
      h₂ = lemma-eval e₂ (Cons (eval e₁ (θ₁ ₒ θ) (project-Env ϕ env)) env) (ψ ++⊑ (θ₂ ₒ θ)) (ϕ os)
      shuffle  = trans (cong₂ _++⊑_ (sym (law-ₒoi ψ)) (law-ₒₒ θ₂ θ ϕ)) (law-commute-ₒ++⊑ ψ oi (θ₂ ₒ θ) ϕ)
      H₁ = cong (λ x → Cons x (project-Env ϕ env)) (trans (cong (λ x → eval e₁ x env) (law-ₒₒ θ₁ θ ϕ)) h₁)
  in  trans
        (cong (λ x → eval e₂ _ (Cons x env)) (trans (cong (λ x → eval e₁ x env) (law-ₒₒ θ₁ θ ϕ)) h₁))
        (trans (cong (λ x → eval e₂ x _) shuffle) h₂)
lemma-eval (Val v) env θ ϕ = refl
lemma-eval (Plus (pair (e₁ ↑ θ₁) (e₂ ↑ θ₂) c)) env θ ϕ =
  cong₂ _+_
    (trans (cong (λ x → eval e₁ x env) (law-ₒₒ θ₁ θ ϕ)) (lemma-eval e₁ env (θ₁ ₒ θ) ϕ))
    (trans (cong (λ x → eval e₂ x env) (law-ₒₒ θ₂ θ ϕ)) (lemma-eval e₂ env (θ₂ ₒ θ) ϕ))

lemma-eval-Let :
  {Γₑ Γ : Ctx} (p : (Expr σ ×R ((σ ∷ []) ⊢ Expr τ)) Γ) (env : Env Γₑ) (θ : Γ ⊑ Γₑ) →
  let pair (e₁ ↑ θ₁) ((ψ \\ e₂) ↑ θ₂) c = p
  in  eval (Let p) θ env ≡ eval (App (pair ((Lam (ψ \\ e₂)) ↑ θ₂) (e₁ ↑ θ₁) (cover-flip c))) θ env
lemma-eval-Let p env θ = refl

-- CONVERSION

-- Just to avoid a huge chain of Σ-types.
record Coproduct {Γ₁ Γ₂ Γ : Ctx} (θ : Γ₁ ⊑ Γ) (ϕ : Γ₂ ⊑ Γ) : Set where
  constructor coproduct
  field
    Γ' : Ctx
    ψ  : Γ' ⊑ Γ
    θ' : Γ₁ ⊑ Γ'
    ϕ' : Γ₂ ⊑ Γ'
    pθ : θ ≡ (θ' ₒ ψ)
    pϕ : ϕ ≡ (ϕ' ₒ ψ)
    c  : Cover θ' ϕ'

cop : {Γ₁ Γ₂ Γ : Ctx} (θ : Γ₁ ⊑ Γ) (ϕ : Γ₂ ⊑ Γ) → Coproduct θ ϕ
cop (θ o') (ϕ o') =
  let coproduct _ ψ _ _ pθ pϕ c = cop θ ϕ
  in  coproduct _ (ψ o') _ _ (cong _o' pθ) (cong _o' pϕ) c
cop (θ o') (ϕ os) =
  let coproduct _ ψ _ _ pθ pϕ c = cop θ ϕ
  in  coproduct _ (ψ os) _ _ (cong _o' pθ) (cong _os pϕ) (c c's)
cop (θ os) (ϕ o') =
  let coproduct _ ψ _ _ pθ pϕ c = cop θ ϕ
  in  coproduct _ (ψ os) _ _ (cong _os pθ) (cong _o' pϕ) (c cs')
cop (θ os) (ϕ os) =
  let coproduct _ ψ _ _ pθ pϕ c = cop θ ϕ
  in  coproduct _ (ψ os) _ _ (cong _os pθ) (cong _os pϕ) (c css)
cop oz oz =
  coproduct _ oz _ _ refl refl czz

_,R_ : {S T : Scoped} {Γ : Ctx} → S ⇑ Γ → T ⇑ Γ → (S ×R T) ⇑ Γ
(s ↑ θ) ,R (t ↑ ϕ) =
  let coproduct _ ψ θ' ϕ' _ _ c = cop θ ϕ
  in pair (s ↑ θ') (t ↑ ϕ') c ↑ ψ


-- decide which variables are used or not
into : DeBruijn.Expr Γ σ → Expr σ ⇑ Γ
into (DeBruijn.Var {σ} x) =
  Var {σ} ↑ o-Ref x
into (DeBruijn.App e₁ e₂) =
  map⇑ App (into e₁ ,R into e₂)
into (DeBruijn.Lam e) =
  map⇑ Lam ((_ ∷ []) \\R into e)
into (DeBruijn.Let e₁ e₂) =
  map⇑ Let (into e₁ ,R ((_ ∷ []) \\R into e₂))
into (DeBruijn.Val v) =
  (Val v) ↑ oe
into (DeBruijn.Plus e₁ e₂) =
  map⇑ Plus (into e₁ ,R into e₂)

from : ∀ {Γ' Γ σ} → Γ' ⊑ Γ → Expr σ Γ' → DeBruijn.Expr Γ σ
from θ Var =
  DeBruijn.Var (ref-o θ)
from θ (App (pair (e₁ ↑ ϕ₁) (e₂ ↑ ϕ₂) cover)) =
  DeBruijn.App (from (ϕ₁ ₒ θ) e₁) (from (ϕ₂ ₒ θ) e₂)
from θ (Lam (ψ \\ e)) =
  DeBruijn.Lam (from (ψ ++⊑ θ) e)
from θ (Let (pair (e₁ ↑ θ₁) ((ψ \\ e₂) ↑ θ₂) c)) =
  DeBruijn.Let (from (θ₁ ₒ θ) e₁) (from (ψ ++⊑ (θ₂ ₒ θ)) e₂)
from θ (Val v) =
  DeBruijn.Val v
from θ (Plus (pair (e₁ ↑ θ₁) (e₂ ↑ θ₂) cover)) =
  DeBruijn.Plus (from (θ₁ ₒ θ) e₁) (from (θ₂ ₒ θ) e₂)

-- TODO: prove into/from semantics preserving!
-- may need to be more general?
conversion-correct :
  ∀ {Γₑ Γ τ} (e : DeBruijn.Expr Γ τ) (env : Env Γₑ) (θ : Γ ⊑ Γₑ) →
  let e' ↑ θ' = into e
  in DeBruijn.eval (from θ' e') (project-Env θ env) ≡ DeBruijn.eval e (project-Env θ env)
conversion-correct (DeBruijn.Var x) env θ = {!!}
conversion-correct (DeBruijn.App e₁ e₂) env θ =
  let e₁' ↑ θ₁ = into e₁
      e₂' ↑ θ₂ = into e₂
      coproduct _ _ _ _ p₁ p₂ _ = cop θ₁ θ₂
      pair (_ ↑ θ₁') (_ ↑ θ₂') c ↑ θ' = into e₁ ,R into e₂
  in cong₂ _$_
      (trans (cong (λ x → DeBruijn.eval (from x e₁') _) (sym p₁)) (conversion-correct e₁ env θ))
      (trans (cong (λ x → DeBruijn.eval (from x e₂') _) (sym p₂)) (conversion-correct e₂ env θ))
conversion-correct (DeBruijn.Lam e) env θ
  with into e  | conversion-correct e
...  | e' ↑ θ' | h
  with (_ ∷ []) ⊣ θ'
... | ⊣r ϕ₁ ϕ₂ (refl , refl) =
  let (ψ \\ e'') ↑ θ'' = (_ ∷ []) \\R into e
  in extensionality _ _ λ v →
    h (Cons v env) (θ os)
conversion-correct (DeBruijn.Let e₁ e₂) env θ = {!!}
conversion-correct (DeBruijn.Val v) env θ =
  refl
conversion-correct (DeBruijn.Plus e₁ e₂) env θ =
  let e₁' ↑ θ₁ = into e₁
      e₂' ↑ θ₂ = into e₂
      coproduct _ _ _ _ p₁ p₂ _ = cop θ₁ θ₂
      pair (_ ↑ θ₁') (_ ↑ θ₂') c ↑ θ' = into e₁ ,R into e₂
  in cong₂ _+_
      (trans (cong (λ x → DeBruijn.eval (from x e₁') _) (sym p₁)) (conversion-correct e₁ env θ))
      (trans (cong (λ x → DeBruijn.eval (from x e₂') _) (sym p₂)) (conversion-correct e₂ env θ))
