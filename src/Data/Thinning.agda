{-# OPTIONS --safe #-}

-- Based on:
-- Everybody's Got To Be Somewhere
-- (https://arxiv.org/abs/1807.04085)
module Data.Thinning where

open import Data.Empty using (⊥)
open import Data.Product using (Σ; _×_; _,_; Σ-syntax)
open import Data.List using (List; _∷_; []; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

private
  variable
    I : Set
    σ τ : I
    Γ Γ' Γ₁ Γ₂ Γ₃ Γ₄ Δ Δ₁ Δ₂ : List I

data _⊑_ {I : Set} : List I → List I → Set where
  o' : {Δ Γ : List I} → Δ ⊑ Γ →      Δ  ⊑ (τ ∷ Γ)
  os : {Δ Γ : List I} → Δ ⊑ Γ → (τ ∷ Δ) ⊑ (τ ∷ Γ)
  oz : [] ⊑ []

oi : Γ ⊑ Γ
oi {Γ = []} = oz
oi {Γ = x ∷ Γ} = os oi

-- [] is an initial object.
oe : {Γ : List I} → [] ⊑ Γ
oe {Γ = []} = oz
oe {Γ = τ ∷ Γ} = o' oe

oe-unique : (θ : [] ⊑ Γ) → θ ≡ oe
oe-unique oz = refl
oe-unique (o' θ) = cong o' (oe-unique θ)

infixr 19 _ₒ_

_ₒ_ : Γ₁ ⊑ Γ₂ → Γ₂ ⊑ Γ₃ → Γ₁ ⊑ Γ₃
θ    ₒ o' ϕ = o' (θ ₒ ϕ)
o' θ ₒ os ϕ = o' (θ ₒ ϕ)
os θ ₒ os ϕ = os (θ ₒ ϕ)
oz   ₒ oz   = oz

law-ₒoi : (θ : Δ ⊑ Γ) → θ ₒ oi ≡ θ
law-ₒoi oz     = refl
law-ₒoi (o' θ) = cong o' (law-ₒoi θ)
law-ₒoi (os θ) = cong os (law-ₒoi θ)

law-oiₒ : (θ : Δ ⊑ Γ) → oi ₒ θ ≡ θ
law-oiₒ oz     = refl
law-oiₒ (o' θ) = cong o' (law-oiₒ θ)
law-oiₒ (os θ) = cong os (law-oiₒ θ)

law-ₒₒ :
  (θ : Γ₁ ⊑ Γ₂) (ϕ : Γ₂ ⊑ Γ₃) (ψ : Γ₃ ⊑ Γ₄) →
  θ ₒ (ϕ ₒ ψ) ≡ (θ ₒ ϕ) ₒ ψ
law-ₒₒ θ      ϕ      (o' ψ) = cong o' (law-ₒₒ θ ϕ ψ)
law-ₒₒ θ      (o' ϕ) (os ψ) = cong o' (law-ₒₒ θ ϕ ψ)
law-ₒₒ (o' θ) (os ϕ) (os ψ) = cong o' (law-ₒₒ θ ϕ ψ)
law-ₒₒ (os θ) (os ϕ) (os ψ) = cong os (law-ₒₒ θ ϕ ψ)
law-ₒₒ oz oz oz = refl

infixr 19 _++⊑_

_++⊑_ :
  {Δ₁ Δ₂ Γ₁ Γ₂ : List I} →
  Δ₁ ⊑ Γ₁ → Δ₂ ⊑ Γ₂ → (Δ₁ ++ Δ₂) ⊑ (Γ₁ ++ Γ₂)
o' θ ++⊑ ϕ = o' (θ ++⊑ ϕ)
os θ ++⊑ ϕ = os (θ ++⊑ ϕ)
oz   ++⊑ ϕ = ϕ

record Split (Γ₁ : List I) (ψ : Δ ⊑ (Γ₁ ++ Γ₂)) : Set where
  constructor split
  field
    {used₁} : List I
    {used₂} : List I
    thinning₁ : (used₁ ⊑ Γ₁)
    thinning₂ : (used₂ ⊑ Γ₂)
    eq : Σ (Δ ≡ used₁ ++ used₂) λ { refl → ψ ≡ thinning₁ ++⊑ thinning₂ }

_⊣_ : (Γ₁ : List I) (ψ : Δ ⊑ (Γ₁ ++ Γ₂)) → Split Γ₁ ψ
[]       ⊣ ψ                                           = split oz ψ (refl , refl)
(τ ∷ Γ₁) ⊣ o' ψ            with Γ₁ ⊣ ψ
(τ ∷ Γ₁) ⊣ o' .(ϕ₁ ++⊑ ϕ₂) | split ϕ₁ ϕ₂ (refl , refl) = split (o' ϕ₁) ϕ₂ (refl , refl)
(τ ∷ Γ₁) ⊣ os ψ            with Γ₁ ⊣ ψ
(τ ∷ Γ₁) ⊣ os .(ϕ₁ ++⊑ ϕ₂) | split ϕ₁ ϕ₂ (refl , refl) = split (os ϕ₁) ϕ₂ (refl , refl)

law-commute-ₒ++⊑ :
  {Γ₁ Γ₂ Γ₃ Γ₁' Γ₂' Γ₃' : List I} →
  (θ₁ : Γ₁ ⊑ Γ₂) (θ₂ : Γ₂ ⊑ Γ₃) (ϕ₁ : Γ₁' ⊑ Γ₂') (ϕ₂ : Γ₂' ⊑ Γ₃') →
  (θ₁ ₒ θ₂) ++⊑ (ϕ₁ ₒ ϕ₂) ≡ (θ₁ ++⊑ ϕ₁) ₒ (θ₂ ++⊑ ϕ₂)
law-commute-ₒ++⊑ θ₁      (o' θ₂) ϕ₁ ϕ₂ = cong o' (law-commute-ₒ++⊑ θ₁ θ₂ ϕ₁ ϕ₂)
law-commute-ₒ++⊑ (o' θ₁) (os θ₂) ϕ₁ ϕ₂ = cong o' (law-commute-ₒ++⊑ θ₁ θ₂ ϕ₁ ϕ₂)
law-commute-ₒ++⊑ (os θ₁) (os θ₂) ϕ₁ ϕ₂ = cong os (law-commute-ₒ++⊑ θ₁ θ₂ ϕ₁ ϕ₂)
law-commute-ₒ++⊑ oz oz ϕ₁ ϕ₂ = refl

-- THINGS WITH THINNINGS

_─Indexed : Set → Set₁
I ─Indexed = List I → Set

private
  variable
    S T : I ─Indexed

record _⇑_ (T : I ─Indexed) (Γ : List I) : Set where
  constructor _↑_
  field
    {support} : List I
    thing : T support
    thinning : support ⊑ Γ

map⇑ : (∀ {Γ'} → S Γ' → T Γ') → S ⇑ Γ → T ⇑ Γ
map⇑ f (s ↑ θ) = f s ↑ θ

mult⇑ : ((T ⇑_) ⇑_) Γ → T ⇑ Γ
mult⇑ ((t ↑ θ) ↑ ϕ) = t ↑ (θ ₒ ϕ)

thin⇑ : Γ₁ ⊑ Γ₂ → T ⇑ Γ₁ → T ⇑ Γ₂
thin⇑ ϕ (t ↑ θ) = t ↑ (θ ₒ ϕ)

module From⊑ where
  open import Data.Var using (_─Scoped; Var; z; s)
  open import Data.Environment

  toEnv : Γ₁ ⊑ Γ₂ → (Γ₁ ─Env) Var Γ₂
  toEnv (o' θ) = s <$> toEnv θ
  toEnv (os θ) = (s <$> toEnv θ) ∙ z
  toEnv oz = ε

-- SYNTAX-RELATED OPERATIONS: UNION

∪-domain : {Δ₁ Δ₂ Γ : List I} (θ₁ : Δ₁ ⊑ Γ) (θ₂ : Δ₂ ⊑ Γ) → List I
∪-domain             (o' θ₁) (o' θ₂) = ∪-domain θ₁ θ₂
∪-domain {Γ = τ ∷ _} (o' θ₁) (os θ₂) = τ ∷ ∪-domain θ₁ θ₂
∪-domain {Γ = τ ∷ _} (os θ₁) (o' θ₂) = τ ∷ ∪-domain θ₁ θ₂
∪-domain {Γ = τ ∷ _} (os θ₁) (os θ₂) = τ ∷ ∪-domain θ₁ θ₂
∪-domain oz oz = []

_∪_ : (θ₁ : Δ₁ ⊑ Γ) (θ₂ : Δ₂ ⊑ Γ) → ∪-domain θ₁ θ₂ ⊑ Γ
o' θ₁ ∪ o' θ₂ = o' (θ₁ ∪ θ₂)
o' θ₁ ∪ os θ₂ = os (θ₁ ∪ θ₂)
os θ₁ ∪ o' θ₂ = os (θ₁ ∪ θ₂)
os θ₁ ∪ os θ₂ = os (θ₁ ∪ θ₂)
oz ∪ oz = oz

un-∪₁ : (θ₁ : Δ₁ ⊑ Γ) (θ₂ : Δ₂ ⊑ Γ) → Δ₁ ⊑ ∪-domain θ₁ θ₂
un-∪₁ (o' θ₁) (o' θ₂) = un-∪₁ θ₁ θ₂
un-∪₁ (o' θ₁) (os θ₂) = o' (un-∪₁ θ₁ θ₂)
un-∪₁ (os θ₁) (o' θ₂) = os (un-∪₁ θ₁ θ₂)
un-∪₁ (os θ₁) (os θ₂) = os (un-∪₁ θ₁ θ₂)
un-∪₁ oz oz = oz

un-∪₂ : (θ₁ : Δ₁ ⊑ Γ) (θ₂ : Δ₂ ⊑ Γ) → Δ₂ ⊑ ∪-domain θ₁ θ₂
un-∪₂ (o' θ₁) (o' θ₂) = un-∪₂ θ₁ θ₂
un-∪₂ (o' θ₁) (os θ₂) = os (un-∪₂ θ₁ θ₂)
un-∪₂ (os θ₁) (o' θ₂) = o' (un-∪₂ θ₁ θ₂)
un-∪₂ (os θ₁) (os θ₂) = os (un-∪₂ θ₁ θ₂)
un-∪₂ oz oz = oz

law-∪₁-inv : (θ₁ : Δ₁ ⊑ Γ) (θ₂ : Δ₂ ⊑ Γ) → un-∪₁ θ₁ θ₂ ₒ (θ₁ ∪ θ₂) ≡ θ₁
law-∪₁-inv (o' θ₁) (o' θ₂) = cong o' (law-∪₁-inv θ₁ θ₂)
law-∪₁-inv (o' θ₁) (os θ₂) = cong o' (law-∪₁-inv θ₁ θ₂)
law-∪₁-inv (os θ₁) (o' θ₂) = cong os (law-∪₁-inv θ₁ θ₂)
law-∪₁-inv (os θ₁) (os θ₂) = cong os (law-∪₁-inv θ₁ θ₂)
law-∪₁-inv oz oz = refl

law-∪₂-inv : (θ₁ : Δ₁ ⊑ Γ) (θ₂ : Δ₂ ⊑ Γ) → un-∪₂ θ₁ θ₂ ₒ (θ₁ ∪ θ₂) ≡ θ₂
law-∪₂-inv (o' θ₁) (o' θ₂) = cong o' (law-∪₂-inv θ₁ θ₂)
law-∪₂-inv (o' θ₁) (os θ₂) = cong os (law-∪₂-inv θ₁ θ₂)
law-∪₂-inv (os θ₁) (o' θ₂) = cong o' (law-∪₂-inv θ₁ θ₂)
law-∪₂-inv (os θ₁) (os θ₂) = cong os (law-∪₂-inv θ₁ θ₂)
law-∪₂-inv oz oz = refl

-- SYNTAX-RELATED OPERATIONS: POP

pop-domain : {Δ Γ : List I} → Δ ⊑ Γ → List I
pop-domain {Δ = Δ}     (o' θ) = Δ
pop-domain {Δ = _ ∷ Δ} (os θ) = Δ
pop-domain oz = []

pop : (θ : Δ ⊑ (σ ∷ Γ)) → pop-domain θ ⊑ Γ
pop (o' θ) = θ
pop (os θ) = θ

un-pop : (θ : Δ ⊑ (σ ∷ Γ)) → Δ ⊑ (σ ∷ pop-domain θ)
un-pop (o' θ) = o' oi
un-pop (os θ) = oi

law-pop-inv : (θ : Δ ⊑ (σ ∷ Γ)) → un-pop θ ₒ os (pop θ) ≡ θ
law-pop-inv (o' θ) = cong o' (law-oiₒ θ)
law-pop-inv (os θ) = cong os (law-oiₒ θ)
