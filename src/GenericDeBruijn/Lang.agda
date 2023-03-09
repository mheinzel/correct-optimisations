{-# OPTIONS --allow-unsolved-metas #-}

module GenericDeBruijn.Lang where

open import Data.Product
open import Data.Nat using (_+_)
open import Data.List using (List ; _∷_ ; []; _++_)
open import Function using (_$_; _∘_; const)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import Generic.Syntax
open import Generic.DeBruijn.Syntax
open import Generic.DeBruijn.Semantics as Sem using (Semantics)
open import Generic.DeBruijn.Simulation as Sim using (Simulation)
open import Generic.DeBruijn.Fundamental as Fun using (Fundamental)
open import Data.Environment
open import Data.Var
open import Data.Relation
open import Data.Pred
open import Data.Unit using (⊤; tt)
open import Stdlib using (∀[_])

open import Core hiding (⟦_⟧)
open Core.Env {U} {Core.⟦_⟧}
open Core.Ref {U} {Core.⟦_⟧} hiding (lookup)
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

private
  variable
    σ τ : U
    Γ Γ' : Ctx

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
Expr = Tm Lang

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
th^Value v = const v

Eval : Semantics Lang Value Value
Semantics.th^𝓥 Eval = th^Value
Semantics.var Eval = λ v → v
Semantics.alg Eval = λ where
  (App v₁ v₂)  → v₁ v₂
  (Lam e)      → λ v → e identity (ε ∙ v)
  (Let v e)    → e identity (ε ∙ v)
  (Val v)      → v
  (Plus v₁ v₂) → v₁ + v₂

eval : ∀ {Γ Γ' σ} → Tm Lang σ Γ → (Γ ─Env) Value Γ' → Value σ Γ'
eval t env = Sem.semantics Eval env t

DeBruijnExpr : U ─Scoped
DeBruijnExpr τ Γ = DeBruijn.Expr Γ τ  -- grrr

Ref-Var : ∀ {σ Γ} → Var σ Γ → Ref σ Γ
Ref-Var z = Top
Ref-Var (s x) = Pop (Ref-Var x)

From : Semantics Lang Var DeBruijnExpr
Semantics.th^𝓥 From = th^Var
Semantics.var From = DeBruijn.Var ∘ Ref-Var
Semantics.alg From = λ where
  (App e₁ e₂)  → DeBruijn.App e₁ e₂
  (Lam e)      → DeBruijn.Lam (e (pack s) (ε ∙ z))
  (Let e₁ e₂)  → DeBruijn.Let e₁ (e₂ (pack s) (ε ∙ z))
  (Val v)      → DeBruijn.Val v
  (Plus e₁ e₂) → DeBruijn.Plus e₁ e₂

from : ∀ {Γ Γ' σ} → (Γ ─Env) Var Γ' → Tm Lang σ Γ → DeBruijn.Expr Γ' σ
from env t = Sem.semantics From env t

into-Env : ∀ {Γ' Γ} → Env Γ → (Γ ─Env) Value Γ'
into-Env Nil = pack (λ ())
into-Env (Cons v env) = into-Env env ∙ v

from-Env : ∀ {Γ' Γ} → (Γ ─Env) Value Γ' → Env Γ
from-Env {Γ'} {[]} env = Nil
from-Env {Γ'} {τ ∷ Γ} env = Cons (lookup env z) (from-Env {Γ'} (pack (λ k → lookup env (s k))))

pr^Env : ∀ {Γ Δ} → Thinning Γ Δ → Env Δ → Env Γ
pr^Env {[]} ρ env = Nil
pr^Env {τ ∷ Γ} ρ env = Cons (lookup {Δ = Γ} (into-Env env) (lookup ρ z) ) (pr^Env (pack (λ x → lookup ρ (s x))) env)

th^Env→ : {T : List U → Set} → Thinnable T → Thinnable (Env Stdlib.⇒ T)
th^Env→ t {Γ} f {Δ} ρ env = t (f (pr^Env ρ env)) ρ

-- This should be in the libary.
law-∙>> :
  {I : Set} {Δ Γ₁ Γ₂ : List I} {𝓥 : I ─Scoped} {σ τ : I}
  (ρ₁ : (Γ₁ ─Env) 𝓥 Δ)
  (ρ₂ : (Γ₂ ─Env) 𝓥 Δ)
  (v : 𝓥 σ Δ) →
  (k : Var τ (σ ∷ Γ₁ ++ Γ₂)) →
  lookup ((ρ₁ ∙ v) >> ρ₂) k ≡ lookup ((ρ₁ >> ρ₂) ∙ v) k
law-∙>> ρ₁ ρ₂ v z = refl
law-∙>> {Γ₁ = Γ₁} ρ₁ ρ₂ v (s k) with split Γ₁ k
... | inj₁ i = refl
... | inj₂ i = refl

law-into-Env-++ᴱ :
  ∀ {Δ Γ₁ Γ₂ τ}
  (env₁ : Env Γ₁) →
  (env₂ : Env Γ₂) →
  (k : Var τ (Γ₁ ++ Γ₂)) →
  lookup (into-Env {Δ} (env₁ ++ᴱ env₂)) k ≡ lookup {Δ = Δ} (into-Env env₁ >> into-Env env₂) k
law-into-Env-++ᴱ Nil env₂ k = refl
law-into-Env-++ᴱ (Cons _ env₁) env₂ z = refl
law-into-Env-++ᴱ (Cons v env₁) env₂ (s k) =
  trans
    (law-into-Env-++ᴱ env₁ env₂ k)
    (sym (law-∙>> (into-Env env₁) (into-Env env₂) v (s k)))

helper :
  ∀ {Δ Γ₁ Γ₂}
  (env₁ : Env Γ₁) (env₁' : (Γ₁ ─Env) Value Δ) →
  (env₂ : Env Γ₂) (env₂' : (Γ₂ ─Env) Value Δ) →
  ({σ : U} (x : Var σ Γ₁) → lookup {Δ = Δ} (into-Env env₁) x ≡ lookup env₁' x) →
  ({σ : U} (x : Var σ Γ₂) → lookup {Δ = Δ} (into-Env env₂) x ≡ lookup env₂' x) →
  ({σ : U} (x : Var σ (Γ₁ ++ Γ₂)) → lookup {Δ = Δ} (into-Env (env₁ ++ᴱ env₂)) x ≡ lookup (env₁' >> env₂') x)
helper {_} {Γ₁} {Γ₂} env₁ env₁' env₂ env₂' p₁ p₂ x with split Γ₁ x
... | inj₁ k = trans (law-into-Env-++ᴱ env₁ env₂ (injectˡ Γ₂ k))
                     (trans (injectˡ->> (into-Env env₁) (into-Env env₂) k) (p₁ k))
... | inj₂ k = trans (law-into-Env-++ᴱ env₁ env₂ (injectʳ Γ₁ k))
                     (trans (injectʳ->> (into-Env env₁) (into-Env env₂) k) (p₂ k))

into-Var-correct :
  ∀ {Δ Γ τ} (x : Ref τ Γ) (env : Env Γ) →
  lookup {Δ = Δ} (into-Env env) (into-Var x) ≡ Core.Ref.lookup x env
into-Var-correct Top     (Cons v env) = refl
into-Var-correct (Pop x) (Cons v env) = into-Var-correct x env

into-correct :
  ∀ {Δ Γ τ} (e : DeBruijn.Expr Γ τ) (env : Env Γ) (env' : (Γ ─Env) Value Δ) →
  (p : {σ : U} (x : Var σ Γ) → lookup {Δ = Δ} (into-Env env) x ≡ lookup env' x) →
  eval (into e) env' ≡ DeBruijn.eval e env
into-correct (DeBruijn.Var x) env env' p =
  trans (sym (p (into-Var x))) (into-Var-correct x env)
into-correct (DeBruijn.App e₁ e₂) env env' p =
  cong₂ _$_ (into-correct e₁ env env' p) (into-correct e₂ env env' p)
into-correct {Δ} (DeBruijn.Lam e) env env' p =
  extensionality _ _ λ v →
      eval (into e) ((ε ∙ v) >> th^Env th^Value env' identity)
    ≡⟨ into-correct {Δ} e (Cons v env) ((ε ∙ v) >> th^Env th^Value env' identity)
         (helper (Cons v Nil) (ε ∙ v) env env' (λ { z → refl }) p) ⟩
      DeBruijn.eval e (Cons v env)
    ∎
into-correct (DeBruijn.Let e₁ e₂) env env' p =
    eval (into e₂) ((ε ∙ eval (into e₁) env') >> th^Env th^Value env' identity)
  ≡⟨ into-correct e₂
       (Cons (DeBruijn.eval e₁ env) env)
       ((ε ∙ eval (into e₁) env') >> th^Env th^Value env' identity)
       (helper (Cons (DeBruijn.eval e₁ env) Nil) (ε ∙ eval (into e₁) env') env env'
         (λ { z → sym (into-correct e₁ env env' p) }) p) ⟩
    DeBruijn.eval e₂ (Cons (DeBruijn.eval e₁ env) env)
  ∎
into-correct (DeBruijn.Val v) env env' p =
  refl
into-correct (DeBruijn.Plus e₁ e₂) env env' p =
  cong₂ _+_ (into-correct e₁ env env' p) (into-correct e₂ env env' p)

-- TODO: I'm doing something wrong, I just don't get it.
rel-eval≡ : Rel DeBruijnExpr Value
rel-eval≡ = mkRel (λ σ {Γ} e v → (env : (Γ ─Env) Value []) → DeBruijn.eval e (from-Env env) ≡ v)

rel-lookup≡ : Rel Var Value
rel-lookup≡ = mkRel (λ σ {Γ} x v → (env : (Γ ─Env) Value []) → Core.Ref.lookup (Ref-Var x) (from-Env env) ≡ v)

From-correct : Simulation Lang From Eval rel-lookup≡ rel-eval≡
Simulation.thᴿ From-correct {Γ} {Δ} {τ} {k} {v} ρ r env =
    Core.Ref.lookup (Ref-Var (lookup ρ k)) (from-Env env)
  ≡⟨ {!!} ⟩
    Core.Ref.lookup (Ref-Var k) (from-Env {[]} (select ρ env))
  ≡⟨ r (select ρ env) ⟩
    v
  ∎
Simulation.varᴿ From-correct {τ} {Γ} {x} {v} r env = r env
Simulation.algᴿ From-correct {τ} {Γ} {Δ} {ρ} {env₁} (App e₁ e₂) rⱽ (refl , h₁ , h₂ , tt) env =
    DeBruijn.eval (from ρ e₁) (from-Env env) (DeBruijn.eval (from ρ e₂) (from-Env env))
  ≡⟨ cong₂ _$_ (h₁ env) (h₂ env) ⟩
    eval e₁ env₁ (eval e₂ env₁)
  ∎
Simulation.algᴿ From-correct {σ ⇒ τ} {Γ} {Δ} {ρ} {env₁} (Lam e) rⱽ (refl , h , tt) env =
  extensionality _ _ λ v →
      DeBruijn.eval (from ((ε ∙ z) >> th^Env th^Var ρ (pack s)) e) (Cons v (from-Env env))
    ≡⟨ {!!} ⟩  -- (? ∙ᴿ ?) (Cons v env)
      DeBruijn.eval (from ({!!} >> th^Env th^Var ρ identity) e) (from-Env env)
    ≡⟨ h identity {! εᴿ ∙ᴿ {!lookupᴿ rⱽ!} !} env ⟩
      eval e ((ε ∙ v) >> th^Env th^Value env₁ identity)
      -- eval e (? >> th^Env th^Value env₁ (pack s))
    ∎
Simulation.algᴿ From-correct {τ} {Γ} {Δ} {ρ} {env₁} (Let e₁ e₂) = {!!}
Simulation.algᴿ From-correct {τ} {Γ} {Δ} {ρ} {env₁} (Val v) = {!!}
Simulation.algᴿ From-correct {τ} {Γ} {Δ} {ρ} {env₁} (Plus e₁ e₂) = {!!}

from-correct : (e : Expr τ Γ) (env : (Γ ─Env) Value []) → DeBruijn.eval (from identity e) (from-Env env) ≡ eval e env
from-correct {τ} {Γ} e env =
  {! Sim.sim From-correct {Γ} {Γ} {{!ε!}} {!!} {! e !} env !}
