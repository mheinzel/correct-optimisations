-- using co-de-Bruijn representation
module CoDeBruijn.Lang where

open import Data.Nat using (_+_)
open import Data.List using (List ; _∷_ ; [])
open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; cong₂ ; sym)
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import Core
import DeBruijn.Lang as DeBruijn
open import OPE

-- aka Cover
data Union : (Γ₁ Γ₂ Γ : Ctx) → Set where
  done   :                               Union      []       []       []
  left   : ∀ {Γ₁ Γ₂ Γ} → Union Γ₁ Γ₂ Γ → Union (τ ∷ Γ₁)      Γ₂  (τ ∷ Γ)
  right  : ∀ {Γ₁ Γ₂ Γ} → Union Γ₁ Γ₂ Γ → Union      Γ₁  (τ ∷ Γ₂) (τ ∷ Γ)
  both   : ∀ {Γ₁ Γ₂ Γ} → Union Γ₁ Γ₂ Γ → Union (τ ∷ Γ₁) (τ ∷ Γ₂) (τ ∷ Γ)

o-Union₁ : ∀ {Γ₁ Γ₂ Γ} → Union Γ₁ Γ₂ Γ → Γ₁ ⊑ Γ
o-Union₁ done      = oz
o-Union₁ (left u)  = (o-Union₁ u) os
o-Union₁ (right u) = (o-Union₁ u) o'
o-Union₁ (both u)  = (o-Union₁ u) os

o-Union₂ : ∀ {Γ₁ Γ₂ Γ} → Union Γ₁ Γ₂ Γ → Γ₂ ⊑ Γ
o-Union₂ done      = oz
o-Union₂ (left u)  = (o-Union₂ u) o'
o-Union₂ (right u) = (o-Union₂ u) os
o-Union₂ (both u)  = (o-Union₂ u) os

law-Union-Γ₁[] : ∀ {Γ₁ Γ} → Union Γ₁ [] Γ → Γ₁ ≡ Γ
law-Union-Γ₁[] done = refl
law-Union-Γ₁[] (left {τ} u) = cong (τ ∷_) (law-Union-Γ₁[] u)

-- Another kind of "cover", a bit like `pop` for SubCtx
data Bind (τ : U) : Ctx → Ctx → Set where
  dead : Bind τ Γ Γ
  live : Bind τ (τ ∷ Γ) Γ

o-Bind : ∀ {Γ Γ'} → Bind σ Γ Γ' → Γ ⊑ (σ ∷ Γ')
o-Bind {σ} {Γ} {Γ'} dead = oi o'
o-Bind {σ} {Γ} {Γ'} live = oi os

data Expr : (σ : U) (Γ : Ctx) → Set where
  Var :
    ∀ {σ} →
    Expr σ (σ ∷ [])
  App :
    ∀ {σ τ Γ₁ Γ₂ Γ} →
    (u : Union Γ₁ Γ₂ Γ) →
    (e₁ : Expr (σ ⇒ τ) Γ₁) →
    (e₂ : Expr σ Γ₂) →
    Expr τ Γ
  Lam :
    ∀ {σ τ Γ₁ Γ} →
    (b : Bind σ Γ₁ Γ) →
    Expr τ Γ₁ →
    Expr (σ ⇒ τ) Γ
  Let :
    ∀ {σ τ Γ₁ Γ₂ Γ Γ₂'} →
    (b : Bind σ Γ₂ Γ₂') →
    (u : Union Γ₁ Γ₂' Γ) →
    (e₁ : Expr σ Γ₁) →
    (e₂ : Expr τ Γ₂) →
    Expr τ Γ
  Val :
    ∀ {σ} →
    (v : ⟦ σ ⟧) →
    Expr σ []
  Plus :
    ∀ {Γ₁ Γ₂ Γ} →
    (u : Union Γ₁ Γ₂ Γ) →
    (e₁ : Expr NAT Γ₁) →
    (e₂ : Expr NAT Γ₂) →
    Expr NAT Γ

eval : ∀ {Γ' Γ} → Expr τ Γ' → Γ' ⊑ Γ → Env Γ → ⟦ τ ⟧
eval Var ϕ env =
  lookup Top (project-Env ϕ env)
eval (App u e₁ e₂) ϕ env =
  eval e₁ (o-Union₁ u ₒ ϕ) env
    (eval e₂ (o-Union₂ u ₒ ϕ) env)
eval (Lam {σ} b e) ϕ env =
  λ v → eval e (o-Bind b ₒ ϕ os) (Cons v env)
eval (Let b u e₁ e₂) ϕ env =
  eval e₂ (o-Bind b ₒ (o-Union₂ u ₒ ϕ) os)
    (Cons (eval e₁ (o-Union₁ u ₒ ϕ) env) env)
eval (Val v) ϕ env = v
eval (Plus u e₁ e₂) ϕ env =
    eval e₁ (o-Union₁ u ₒ ϕ) env
  + eval e₂ (o-Union₂ u ₒ ϕ) env

-- CONVERSION

cover-Union : ∀ {Γ₁ Γ₂ Γ} → Γ₁ ⊑ Γ → Γ₂ ⊑ Γ → Union Γ₁ Γ₂ ⇑ Γ
cover-Union oz oz = done ↑ oz
cover-Union (θ₁ o') (θ₂ o') = let c ↑ θ = cover-Union θ₁ θ₂ in       c ↑ θ o'
cover-Union (θ₁ o') (θ₂ os) = let c ↑ θ = cover-Union θ₁ θ₂ in right c ↑ θ os
cover-Union (θ₁ os) (θ₂ o') = let c ↑ θ = cover-Union θ₁ θ₂ in left  c ↑ θ os
cover-Union (θ₁ os) (θ₂ os) = let c ↑ θ = cover-Union θ₁ θ₂ in both  c ↑ θ os

cover-Bind : ∀ {Γ' Γ σ} → Γ' ⊑ (σ ∷ Γ) → Bind σ Γ' ⇑ Γ
cover-Bind (θ o') = dead ↑ θ
cover-Bind (θ os) = live ↑ θ

-- decide which variables are used or not
into : DeBruijn.Expr Γ σ → Expr σ ⇑ Γ
into (DeBruijn.Var {σ} x) =
  Var {σ} ↑ o-Ref x
into (DeBruijn.App e₁ e₂) =
  let e₁' ↑ ope₁ = into e₁
      e₂' ↑ ope₂ = into e₂
      u   ↑ ope  = cover-Union ope₁ ope₂
  in App u e₁' e₂' ↑ ope
into (DeBruijn.Lam e) =
  let e' ↑ ope' = into e
      b  ↑ ope  = cover-Bind ope'
  in Lam b e' ↑ ope
into (DeBruijn.Let e₁ e₂) =
  let e₁' ↑ ope₁  = into e₁
      e₂' ↑ ope₂  = into e₂
      b   ↑ ope₂' = cover-Bind ope₂
      u   ↑ ope   = cover-Union ope₁ ope₂'
  in Let b u e₁' e₂' ↑ ope
into (DeBruijn.Val v) =
  (Val v) ↑ oe
into (DeBruijn.Plus e₁ e₂) =
  let e₁' ↑ ope₁ = into e₁
      e₂' ↑ ope₂ = into e₂
      u   ↑ ope  = cover-Union ope₁ ope₂
  in Plus u e₁' e₂' ↑ ope

from : ∀ {Γ' Γ σ} → Γ' ⊑ Γ → Expr σ Γ' → DeBruijn.Expr Γ σ
from ope Var =
  DeBruijn.Var (ref-o ope)
from ope (App u e₁ e₂) =
  DeBruijn.App (from (o-Union₁ u ₒ ope) e₁) (from (o-Union₂ u ₒ ope) e₂)
from ope (Lam b e) =
  DeBruijn.Lam (from (o-Bind b ₒ ope os) e)
from ope (Let b u e₁ e₂) =
  DeBruijn.Let
    (from (o-Union₁ u ₒ ope) e₁)
    (from (o-Bind b ₒ (o-Union₂ u ₒ ope) os) e₂)
from ope (Val v) =
  DeBruijn.Val v
from ope (Plus u e₁ e₂) =
  DeBruijn.Plus (from (o-Union₁ u ₒ ope) e₁) (from (o-Union₂ u ₒ ope) e₂)

-- TODO: prove into/from semantics preserving!
