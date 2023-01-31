-- using co-de-Bruijn representation
module LangCdB where

open import Data.Nat using (_+_)
open import Data.List using (List ; _∷_ ; [])
open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; cong₂ ; sym)
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import Lang hiding (Expr ; eval)
import Lang
open import OPE
open import SubCtx

-- aka Cover
data Union : (Γ₁ Γ₂ Γ : Ctx) → Set where
  done   :                               Union      []       []       []
  left   : ∀ {Γ₁ Γ₂ Γ} → Union Γ₁ Γ₂ Γ → Union (τ ∷ Γ₁)      Γ₂  (τ ∷ Γ)
  right  : ∀ {Γ₁ Γ₂ Γ} → Union Γ₁ Γ₂ Γ → Union      Γ₁  (τ ∷ Γ₂) (τ ∷ Γ)
  both   : ∀ {Γ₁ Γ₂ Γ} → Union Γ₁ Γ₂ Γ → Union (τ ∷ Γ₁) (τ ∷ Γ₂) (τ ∷ Γ)

ope-Union₁ : ∀ {Γ₁ Γ₂ Γ} → Union Γ₁ Γ₂ Γ → OPE Γ₁ Γ
ope-Union₁ done = Empty
ope-Union₁ (left u) = Keep _ (ope-Union₁ u)
ope-Union₁ (right u) = Drop _ (ope-Union₁ u)
ope-Union₁ (both u) = Keep _ (ope-Union₁ u)

ope-Union₂ : ∀ {Γ₁ Γ₂ Γ} → Union Γ₁ Γ₂ Γ → OPE Γ₂ Γ
ope-Union₂ done = Empty
ope-Union₂ (left u) = Drop _ (ope-Union₂ u)
ope-Union₂ (right u) = Keep _ (ope-Union₂ u)
ope-Union₂ (both u) = Keep _ (ope-Union₂ u)

-- Another kind of "cover", a bit like `pop` for SubCtx
data Bind (τ : U) : Ctx → Ctx → Set where
  dead : Bind τ Γ Γ
  live : Bind τ (τ ∷ Γ) Γ

ope-Bind : ∀ {Γ Γ'} → Bind σ Γ Γ' → OPE Γ (σ ∷ Γ')
ope-Bind {σ} {Γ} {Γ'} dead = Drop σ (ope-id Γ')
ope-Bind {σ} {Γ} {Γ'} live = Keep σ (ope-id Γ')

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

eval : ∀ {Γ' Γ} → Expr τ Γ' → OPE Γ' Γ → Env Γ → ⟦ τ ⟧
eval Var ope env =
  lookup Top (project-Env ope env)
eval (App u e₁ e₂) ope env =
  eval e₁ (ope-trans (ope-Union₁ u) ope) env
    (eval e₂ (ope-trans (ope-Union₂ u) ope) env)
eval (Lam {σ} b e) ope env =
  λ v → eval e (ope-trans (ope-Bind b) (Keep σ ope)) (Cons v env)
eval (Let b u e₁ e₂) ope env =
  eval e₂ (ope-trans (ope-Bind b) (Keep _ (ope-trans (ope-Union₂ u) ope)))
    (Cons (eval e₁ (ope-trans (ope-Union₁ u) ope) env) env)
eval (Val v) ope env = v
eval (Plus u e₁ e₂) ope env =
    eval e₁ (ope-trans (ope-Union₁ u) ope) env
  + eval e₂ (ope-trans (ope-Union₂ u) ope) env

-- CONVERSION

cover-Union : ∀ {Γ₁ Γ₂ Γ} → OPE Γ₁ Γ → OPE Γ₂ Γ → Union Γ₁ Γ₂ ⇑ Γ
cover-Union Empty Empty = done ↑ Empty
cover-Union (Drop τ ope₁) (Drop .τ ope₂) = let c ↑ ope = cover-Union ope₁ ope₂ in       c ↑ Drop τ ope
cover-Union (Drop τ ope₁) (Keep .τ ope₂) = let c ↑ ope = cover-Union ope₁ ope₂ in right c ↑ Keep τ ope
cover-Union (Keep τ ope₁) (Drop .τ ope₂) = let c ↑ ope = cover-Union ope₁ ope₂ in left  c ↑ Keep τ ope
cover-Union (Keep τ ope₁) (Keep .τ ope₂) = let c ↑ ope = cover-Union ope₁ ope₂ in both  c ↑ Keep τ ope

cover-Bind : ∀ {Γ' Γ σ} → OPE Γ' (σ ∷ Γ) → Bind σ Γ' ⇑ Γ
cover-Bind (Drop _ ope) = dead ↑ ope
cover-Bind (Keep _ ope) = live ↑ ope

-- decide which variables are used or not
into : Lang.Expr Γ σ → Expr σ ⇑ Γ
into (Var {σ} x) =
  Var {σ} ↑ ope-Ref x
into (App e₁ e₂) =
  let e₁' ↑ ope₁ = into e₁
      e₂' ↑ ope₂ = into e₂
      u   ↑ ope  = cover-Union ope₁ ope₂
  in App u e₁' e₂' ↑ ope
into (Lam e) =
  let e' ↑ ope' = into e
      b  ↑ ope  = cover-Bind ope'
  in Lam b e' ↑ ope
into (Let e₁ e₂) =
  let e₁' ↑ ope₁  = into e₁
      e₂' ↑ ope₂  = into e₂
      b   ↑ ope₂' = cover-Bind ope₂
      u   ↑ ope   = cover-Union ope₁ ope₂'
  in Let b u e₁' e₂' ↑ ope
into (Val v) =
  (Val v) ↑ ope-! _
into (Plus e₁ e₂) =
  let e₁' ↑ ope₁ = into e₁
      e₂' ↑ ope₂ = into e₂
      u   ↑ ope  = cover-Union ope₁ ope₂
  in Plus u e₁' e₂' ↑ ope

from : ∀ {Γ' Γ σ} → OPE Γ' Γ → Expr σ Γ' → Lang.Expr Γ σ
from ope Var =
  Var (ref-OPE ope)
from ope (App u e₁ e₂) =
  App (from (ope-trans (ope-Union₁ u) ope) e₁) (from (ope-trans (ope-Union₂ u) ope) e₂)
from ope (Lam b e) =
  Lam (from (ope-trans (ope-Bind b) (Keep _ ope)) e)
from ope (Let b u e₁ e₂) =
  Let
    (from (ope-trans (ope-Union₁ u) ope) e₁)
    (from (ope-trans (ope-Bind b) (Keep _ (ope-trans (ope-Union₂ u) ope))) e₂)
from ope (Val v) =
  Val v
from ope (Plus u e₁ e₂) =
  Plus (from (ope-trans (ope-Union₁ u) ope) e₁) (from (ope-trans (ope-Union₂ u) ope) e₂)
