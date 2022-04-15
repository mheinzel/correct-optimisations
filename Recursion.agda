-- Adapted from http://blog.ezyang.com/2010/06/well-founded-recursion-in-agda/
module Recursion where

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Sum
open import Data.Product

open import Lang
open import Subset

-- The definition from Relation.Binary makes us use levels, but we could switch?
Rel : Set → Set₁
Rel A = A → A → Set

module WF {A : Set} (_<_ : Rel A) where

  data Acc (x : A) : Set where
    acc : (∀ y → y < x → Acc y) → Acc x

  Well-founded : Set
  Well-founded = ∀ x → Acc x

data _<_ (m : ℕ) : ℕ → Set where
  <-base : m < suc m
  <-step : {n : ℕ} → m < n → m < suc n

s<s : ∀ {a b} → a < b → suc a < suc b
s<s <-base = <-base
s<s (<-step y) = <-step (s<s y)

0<s : ∀ {a} → zero < suc a
0<s {zero} = <-base
0<s {suc a} = <-step 0<s

_<?_ : (m n : ℕ) → m < n ⊎ n < suc m
zero <? zero = inj₂ <-base
zero <? suc n = inj₁ 0<s
suc m <? zero = inj₂ (<-step 0<s)
suc m <? suc n with m <? n
... | inj₁ p = inj₁ (s<s p)
... | inj₂ p = inj₂ (s<s p)

<-ℕ-wf : WF.Well-founded _<_
<-ℕ-wf x = WF.acc (aux x)
  where
    aux : ∀ x y → y < x → WF.Acc _<_ y
    --  : (x : _) → (∀ y → y < x → WF.Acc _<_ y)
    aux .(suc y) y <-base = <-ℕ-wf y
    aux .(suc x) y (<-step {x} y<x) = aux x y y<x

module Inverse-image-Well-founded { A B }
  -- Should actually used ≺, but I decided it looked to similar to < for comfort.
  (_<_ : Rel B)(f : A → B) where
  _⊰_ : Rel A
  x ⊰ y = f x < f y

  ii-acc : ∀ {x} → WF.Acc _<_ (f x) → WF.Acc _⊰_ x
  ii-acc (WF.acc g) = WF.acc (λ y fy<fx → ii-acc (g (f y) fy<fx))

  ii-wf : WF.Well-founded _<_ → WF.Well-founded _⊰_
  ii-wf wf x = ii-acc (wf (f x))

num-bindings' : Σ[ Δ ∈ Subset Γ ] Expr ⌊ Δ ⌋ σ → ℕ
num-bindings' (Δ , e) = num-bindings e

module <-num-bindings-Well-founded { Γ σ } where
  open Inverse-image-Well-founded {Σ[ Δ ∈ Subset Γ ] Expr ⌊ Δ ⌋ σ} _<_ num-bindings' public

  wf : WF.Well-founded _⊰_
  wf = ii-wf <-ℕ-wf

_<-bindings_ : (e₁ e₂ : Σ[ Δ ∈ Subset Γ ] Expr ⌊ Δ ⌋ σ) → Set
e₁ <-bindings e₂ = num-bindings' e₁ < num-bindings' e₂

<-bindings-wf : {Γ : Ctx} {σ : U} → WF.Well-founded (_<-bindings_ {Γ} {σ})
<-bindings-wf = wf
  where
    open <-num-bindings-Well-founded


-- just to play around with it
iter-while-decreasing' : (x : ℕ) (f : ℕ → ℕ) (g : WF.Acc _<_ x) → ℕ
iter-while-decreasing' x f (WF.acc g) with f x <? x
... | inj₁ p = iter-while-decreasing' (f x) f (g (f x) p)
... | inj₂ p = x

iter-while-decreasing : (x : ℕ) (f : ℕ → ℕ) → ℕ
iter-while-decreasing x f = iter-while-decreasing' x f (<-ℕ-wf x)
