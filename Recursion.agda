-- Adapted from http://blog.ezyang.com/2010/06/well-founded-recursion-in-agda/
module Recursion where

open import Data.Nat using (ℕ  ; zero ; suc)

open import Lang

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

module <-num-bindings-Well-founded { Γ σ } where
  open Inverse-image-Well-founded {Expr Γ σ} _<_ num-bindings public

  wf : WF.Well-founded _⊰_
  wf = ii-wf <-ℕ-wf
