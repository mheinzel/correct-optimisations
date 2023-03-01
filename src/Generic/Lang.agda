{-# OPTIONS --sized-types #-}

module Generic.Lang where

open import Data.Product
open import Data.Nat using (_+_)
open import Data.List using (List ; _∷_ ; [])
open import Function using (_$_; _∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Size using (∞)

open import Generic.Syntax
open import Generic.Semantics
open import Data.Environment
open import Data.Var

open import Core hiding (lookup)
import DeBruijn.Lang as DeBruijn

-- This is needed because our notion of semantical equivalence is "same evaluation result",
-- and values include Agda functions.
-- We might want something different?
postulate
  -- extensionality : {A B : Set} → (f g : A → B) (H : (x : A) → f x ≡ g x) → f ≡ g
  extensionality :
    {S : Set} {T : S -> Set} (f g : (x : S) -> T x) ->
    ((x : S) -> f x ≡ g x) ->
    f ≡ g

data `Lang : Set where
  `App  : U → U → `Lang
  `Lam  : U → U → `Lang
  `Let  : U → U → `Lang
  `Val  : U → `Lang
  `Plus : `Lang

Lang : Desc U
Lang = `σ `Lang $ λ where
  (`App σ τ) → `X [] (σ ⇒ τ) (`X [] σ (`∎ τ))
  (`Lam σ τ) → `X (σ ∷ []) τ (`∎ (σ ⇒ τ))
  (`Let σ τ) → `X [] σ (`X (σ ∷ []) τ (`∎ τ))
  (`Val τ)   → `σ Core.⟦ τ ⟧ λ _ → `∎ τ
  `Plus      → `X [] NAT (`X [] NAT (`∎ NAT))

pattern App  e₁ e₂  = `App _ _ , e₁ , e₂ , refl
pattern Lam  e      = `Lam _ _ , e  , refl
pattern Let  e₁ e₂  = `Let _ _ , e₁ , e₂ , refl
pattern Val  v      = `Val _   , v  , refl
pattern Plus e₁ e₂  = `Plus    , e₁ , e₂ , refl

Expr : U ─Scoped
Expr = Tm Lang ∞

into-Var : ∀ {Γ τ} → Ref τ Γ → Var τ Γ
into-Var Top = z
into-Var (Pop x) = s (into-Var x)

-- Just to check that this is the same as our original language.
into : ∀ {Γ τ} → DeBruijn.Expr Γ τ → Expr τ Γ
into (DeBruijn.Var x)      = `var (into-Var x)
into (DeBruijn.App e₁ e₂)  = `con (App (into e₁) (into e₂))
into (DeBruijn.Lam e)      = `con (Lam (into e))
into (DeBruijn.Let e₁ e₂)  = `con (Let (into e₁) (into e₂))
into (DeBruijn.Val v)      = `con (Val v)
into (DeBruijn.Plus e₁ e₂) = `con (Plus (into e₁) (into e₂))


Value : U ─Scoped
Value τ Γ = Core.⟦ τ ⟧

th^Value : ∀ {τ} → Thinnable (Value τ)
th^Value v = λ _ → v

Eval : Semantics Lang Value Value
Semantics.th^𝓥 Eval = th^Value
Semantics.var Eval = λ v → v
Semantics.alg Eval = λ where
  (App v₁ v₂)  → v₁ v₂
  (Lam e)      → λ v → e identity (ε ∙ v)
  (Let v e)    → e identity (ε ∙ v)
  (Val v)      → v
  (Plus v₁ v₂) → v₁ + v₂

eval : ∀ {Γ Γ' σ s} → Tm Lang s σ Γ → (Γ ─Env) Value Γ' → Value σ Γ'
eval t env = Semantics.semantics Eval env t

DeBruijnExpr : U ─Scoped
DeBruijnExpr τ Γ = DeBruijn.Expr Γ τ  -- grrr

Ref-Var : ∀ {σ Γ} → Var σ Γ → Ref σ Γ
Ref-Var z = Top
Ref-Var (s x) = Pop (Ref-Var x)

-- Could also use Ref instead of Var, but then we'd need th^Ref
From : Semantics Lang Var DeBruijnExpr
Semantics.th^𝓥 From = th^Var
Semantics.var From = DeBruijn.Var ∘ Ref-Var
Semantics.alg From = λ where
  (App e₁ e₂)  → DeBruijn.App e₁ e₂
  (Lam e)      → DeBruijn.Lam (e (pack s) (ε ∙ z))
  (Let e₁ e₂)  → DeBruijn.Let e₁ (e₂ (pack s) (ε ∙ z))
  (Val v)      → DeBruijn.Val v
  (Plus e₁ e₂) → DeBruijn.Plus e₁ e₂

from : ∀ {Γ Γ' σ s} → (Γ ─Env) Var Γ' → Tm Lang s σ Γ → DeBruijn.Expr Γ' σ
from env t = Semantics.semantics From env t

env-into : ∀ {Γ' Γ} → Env Γ → (Γ ─Env) Value Γ'
env-into Nil = pack (λ ())
env-into (Cons v env) = env-into env ∙ v

env-from : ∀ {Γ' Γ} → (Γ ─Env) Value Γ' → Env Γ
env-from {Γ'} {[]} env = Nil
env-from {Γ'} {τ ∷ Γ} env = Cons (lookup env z) (env-from {Γ'} (pack (λ k → lookup env (s k))))

law-∙>> :
  (v : Value τ Γ) (env : (Γ ─Env) Value Γ) (k : Var σ (τ ∷ Γ)) →
  lookup ((ε ∙ v) >> env) k ≡ lookup (env ∙ v) k
law-∙>> {τ} {Γ} v env k with split (τ ∷ []) k
... | inj₁ k₁ = sym {!injectˡ->> (ε ∙ v) env k₁!}
... | inj₂ k₂ = refl


-- th^Env th^Value env identity ≡ env

-- env-into-correct :
--   env-into env ≡

into-correct :
  (e : DeBruijn.Expr Γ τ) (env : Env Γ) →
  eval {Γ' = Γ} (into e) (env-into env) ≡ DeBruijn.eval e env
into-correct (DeBruijn.Var x) env = {!!}
into-correct (DeBruijn.App e₁ e₂) env =
  cong₂ _$_ (into-correct e₁ env) (into-correct e₂ env)
into-correct (DeBruijn.Lam e) env =
  extensionality _ _ λ v →
      eval (into e) ((ε ∙ v) >> th^Env th^Value (env-into env) identity)
    ≡⟨ {!!} ⟩
      eval (into e) (env-into (Cons v env))
    ≡⟨ into-correct e (Cons v env) ⟩
      DeBruijn.eval e (Cons v env)
    ∎
into-correct (DeBruijn.Let e₁ e₂) env = {!!}
into-correct (DeBruijn.Val v) env = {!!}
into-correct (DeBruijn.Plus e₁ e₂) env = {!!}

-- TODO: How do I even match on the constructors now?
-- Kind of want to do induction on the description, not the term.
-- Need some helper, maybe Simulation?
from-correct :
  (e : Expr τ Γ) (env : (Γ ─Env) Value Γ) →
  DeBruijn.eval (from identity e) (env-from env) ≡ eval e env
from-correct e env = ?
