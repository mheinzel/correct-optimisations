{-# OPTIONS --safe #-}

-- Based on:
-- Everybody's Got To Be Somewhere
-- (https://arxiv.org/abs/1807.04085)
module OPE where

open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_)
open import Data.List using (List; _∷_; []; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

private
  variable
    I : Set
    σ τ : I
    Γ Γ' Γ₁ Γ₂ Γ₃ Γ₄ : List I

infix 21 _o'
infix 21 _os

data _⊑_ {I : Set} : List I → List I → Set where
  _o' : {Γ₁ Γ₂ : List I} → Γ₁ ⊑ Γ₂ →      Γ₁  ⊑ (τ ∷ Γ₂)
  _os : {Γ₁ Γ₂ : List I} → Γ₁ ⊑ Γ₂ → (τ ∷ Γ₁) ⊑ (τ ∷ Γ₂)
  oz  : [] ⊑ []

oi : Γ ⊑ Γ
oi {Γ = []} = oz
oi {Γ = x ∷ Γ} = oi os

-- [] is an initial object.
oe : {Γ : List I} → [] ⊑ Γ
oe {Γ = []} = oz
oe {Γ = τ ∷ Γ} = oe o'

oe-unique : (θ : [] ⊑ Γ) → θ ≡ oe
oe-unique oz = refl
oe-unique (θ o') = cong _o' (oe-unique θ)

infixr 19 _ₒ_

_ₒ_ : Γ₁ ⊑ Γ₂ → Γ₂ ⊑ Γ₃ → Γ₁ ⊑ Γ₃
θ    ₒ ϕ o' = (θ ₒ ϕ) o'
θ o' ₒ ϕ os = (θ ₒ ϕ) o'
θ os ₒ ϕ os = (θ ₒ ϕ) os
oz   ₒ oz   = oz

law-ₒoi : (θ : Γ₁ ⊑ Γ₂) → θ ₒ oi ≡ θ
law-ₒoi oz     = refl
law-ₒoi (θ o') = cong (_o') (law-ₒoi θ)
law-ₒoi (θ os) = cong (_os) (law-ₒoi θ)

law-oiₒ : (θ : Γ₁ ⊑ Γ₂) → oi ₒ θ ≡ θ
law-oiₒ oz     = refl
law-oiₒ (θ o') = cong (_o') (law-oiₒ θ)
law-oiₒ (θ os) = cong (_os) (law-oiₒ θ)

law-ₒₒ :
  (θ : Γ₁ ⊑ Γ₂) (ϕ : Γ₂ ⊑ Γ₃) (ψ : Γ₃ ⊑ Γ₄) →
  θ ₒ (ϕ ₒ ψ) ≡ (θ ₒ ϕ) ₒ ψ
law-ₒₒ θ ϕ (ψ o') = cong _o' (law-ₒₒ θ ϕ ψ)
law-ₒₒ θ (ϕ o') (ψ os) = cong _o' (law-ₒₒ θ ϕ ψ)
law-ₒₒ (θ o') (ϕ os) (ψ os) = cong _o' (law-ₒₒ θ ϕ ψ)
law-ₒₒ (θ os) (ϕ os) (ψ os) = cong _os (law-ₒₒ θ ϕ ψ)
law-ₒₒ oz oz oz = refl

infixr 19 _++⊑_

_++⊑_ :
  {Γ₁ Γ₂ Γ₁' Γ₂' : List I} →
  Γ₁ ⊑ Γ₂ → Γ₁' ⊑ Γ₂' →
  (Γ₁ ++ Γ₁') ⊑ (Γ₂ ++ Γ₂')
(θ o') ++⊑ ϕ = (θ ++⊑ ϕ) o'
(θ os) ++⊑ ϕ = (θ ++⊑ ϕ) os
oz ++⊑ ϕ = ϕ

record _⊣R_ (Γ₁ : List I) (ψ : Γ ⊑ (Γ₁ ++ Γ₂)) : Set where
  constructor ⊣r
  field
    {Γ₁'} : List I
    {Γ₂'} : List I
    ϕ₁ : (Γ₁' ⊑ Γ₁)
    ϕ₂ : (Γ₂' ⊑ Γ₂)
    H : Σ (Γ ≡ Γ₁' ++ Γ₂') λ { refl → ψ ≡ ϕ₁ ++⊑ ϕ₂ }

_⊣_ : (Γ₁ : List I) (ψ : Γ ⊑ (Γ₁ ++ Γ₂)) → Γ₁ ⊣R ψ
[] ⊣ ψ = ⊣r oz ψ (refl , refl)
(τ ∷ Γ₁) ⊣ (ψ o')       with Γ₁ ⊣ ψ
(τ ∷ Γ₁) ⊣ (.(ϕ₁ ++⊑ ϕ₂) o') | ⊣r ϕ₁ ϕ₂ (refl , refl) = ⊣r (ϕ₁ o') ϕ₂ (refl , refl)
(τ ∷ Γ₁) ⊣ (ψ os)       with Γ₁ ⊣ ψ
(τ ∷ Γ₁) ⊣ (.(ϕ₁ ++⊑ ϕ₂) os) | ⊣r ϕ₁ ϕ₂ (refl , refl) = ⊣r (ϕ₁ os) ϕ₂ (refl , refl)

law-commute-ₒ++⊑ :
  {Γ₁ Γ₂ Γ₃ Γ₁' Γ₂' Γ₃' : List I} →
  (θ₁ : Γ₁ ⊑ Γ₂) (θ₂ : Γ₂ ⊑ Γ₃) (ϕ₁ : Γ₁' ⊑ Γ₂') (ϕ₂ : Γ₂' ⊑ Γ₃') →
  (θ₁ ₒ θ₂) ++⊑ (ϕ₁ ₒ ϕ₂) ≡ (θ₁ ++⊑ ϕ₁) ₒ (θ₂ ++⊑ ϕ₂)
law-commute-ₒ++⊑ θ₁ (θ₂ o') ϕ₁ ϕ₂ = cong _o' (law-commute-ₒ++⊑ θ₁ θ₂ ϕ₁ ϕ₂)
law-commute-ₒ++⊑ (θ₁ o') (θ₂ os) ϕ₁ ϕ₂ = cong _o' (law-commute-ₒ++⊑ θ₁ θ₂ ϕ₁ ϕ₂)
law-commute-ₒ++⊑ (θ₁ os) (θ₂ os) ϕ₁ ϕ₂ = cong _os (law-commute-ₒ++⊑ θ₁ θ₂ ϕ₁ ϕ₂)
law-commute-ₒ++⊑ oz oz ϕ₁ ϕ₂ = refl

-- THINGS WITH OPEs

_─Indexed : Set → Set₁
I ─Indexed = List I → Set

private
  variable
    S T : I ─Indexed

record _⇑_ (T : I ─Indexed) (scope : List I) : Set where
  constructor _↑_
  field
    {support} : List I
    thing : T support
    thinning : support ⊑ scope

map⇑ : (∀ {Γ'} → S Γ' → T Γ') → S ⇑ Γ → T ⇑ Γ
map⇑ f (s ↑ θ) = f s ↑ θ

mult⇑ : ((T ⇑_) ⇑_) Γ → T ⇑ Γ
mult⇑ ((t ↑ θ) ↑ ϕ) = t ↑ (θ ₒ ϕ)

thin⇑ : Γ₁ ⊑ Γ₂ → T ⇑ Γ₁ → T ⇑ Γ₂
thin⇑ ϕ (t ↑ θ) = t ↑ (θ ₒ ϕ)
