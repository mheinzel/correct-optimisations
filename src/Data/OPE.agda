{-# OPTIONS --safe #-}

-- Based on:
-- Everybody's Got To Be Somewhere
-- (https://arxiv.org/abs/1807.04085)
module Data.OPE where

open import Data.Empty using (⊥)
open import Data.Product using (Σ; _×_; _,_; Σ-syntax)
open import Data.List using (List; _∷_; []; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

private
  variable
    I : Set
    σ τ : I
    Γ Γ' Γ₁ Γ₂ Γ₃ Γ₄ Δ Δ₁ Δ₂ : List I

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

record Split (Γ₁ : List I) (ψ : Γ ⊑ (Γ₁ ++ Γ₂)) : Set where
  constructor split
  field
    {used₁} : List I
    {used₂} : List I
    thinning₁ : (used₁ ⊑ Γ₁)
    thinning₂ : (used₂ ⊑ Γ₂)
    eq : Σ (Γ ≡ used₁ ++ used₂) λ { refl → ψ ≡ thinning₁ ++⊑ thinning₂ }

_⊣_ : (Γ₁ : List I) (ψ : Γ ⊑ (Γ₁ ++ Γ₂)) → Split Γ₁ ψ
[] ⊣ ψ = split oz ψ (refl , refl)
(τ ∷ Γ₁) ⊣ (ψ o')       with Γ₁ ⊣ ψ
(τ ∷ Γ₁) ⊣ (.(ϕ₁ ++⊑ ϕ₂) o') | split ϕ₁ ϕ₂ (refl , refl) = split (ϕ₁ o') ϕ₂ (refl , refl)
(τ ∷ Γ₁) ⊣ (ψ os)       with Γ₁ ⊣ ψ
(τ ∷ Γ₁) ⊣ (.(ϕ₁ ++⊑ ϕ₂) os) | split ϕ₁ ϕ₂ (refl , refl) = split (ϕ₁ os) ϕ₂ (refl , refl)

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

module From⊑ where
  open import Data.Var using (_─Scoped; Var; z; s)
  open import Data.Environment

  toEnv : Γ₁ ⊑ Γ₂ → (Γ₁ ─Env) Var Γ₂
  toEnv (θ o') = s <$> toEnv θ
  toEnv (θ os) = (s <$> toEnv θ) ∙ z
  toEnv oz = ε

-- A less powerful version of `cop`.
{-
∪-all : (θ₁ : Δ₁ ⊑ Γ) (θ₂ : Δ₂ ⊑ Γ) → Σ[ Δ ∈ List I ] (Δ₁ ⊑ Δ × Δ₂ ⊑ Δ × Δ ⊑ Γ)
∪-all (θ₁ o') (θ₂ o') = let _ , ϕ₁ , ϕ₂ , ϕ = ∪-all θ₁ θ₂ in _ , ϕ₁    , ϕ₂    , ϕ o'
∪-all (θ₁ o') (θ₂ os) = let _ , ϕ₁ , ϕ₂ , ϕ = ∪-all θ₁ θ₂ in _ , ϕ₁ o' , ϕ₂ os , ϕ os
∪-all (θ₁ os) (θ₂ o') = let _ , ϕ₁ , ϕ₂ , ϕ = ∪-all θ₁ θ₂ in _ , ϕ₁ os , ϕ₂ o' , ϕ os
∪-all (θ₁ os) (θ₂ os) = let _ , ϕ₁ , ϕ₂ , ϕ = ∪-all θ₁ θ₂ in _ , ϕ₁ os , ϕ₂ os , ϕ os
∪-all oz oz = [] , oz , oz , oz
-}

∪-domain : {Δ₁ Δ₂ Γ : List I} (θ₁ : Δ₁ ⊑ Γ) (θ₂ : Δ₂ ⊑ Γ) → List I
∪-domain (θ₁ o') (θ₂ o') = ∪-domain θ₁ θ₂
∪-domain {Γ = τ ∷ _} (θ₁ o') (θ₂ os) = τ ∷ ∪-domain θ₁ θ₂
∪-domain {Γ = τ ∷ _} (θ₁ os) (θ₂ o') = τ ∷ ∪-domain θ₁ θ₂
∪-domain {Γ = τ ∷ _} (θ₁ os) (θ₂ os) = τ ∷ ∪-domain θ₁ θ₂
∪-domain oz oz = []

-- aka un-∪₁
un-∪₁ : (θ₁ : Δ₁ ⊑ Γ) (θ₂ : Δ₂ ⊑ Γ) → Δ₁ ⊑ ∪-domain θ₁ θ₂
un-∪₁ (θ₁ o') (θ₂ o') = un-∪₁ θ₁ θ₂
un-∪₁ (θ₁ o') (θ₂ os) = un-∪₁ θ₁ θ₂ o'
un-∪₁ (θ₁ os) (θ₂ o') = un-∪₁ θ₁ θ₂ os
un-∪₁ (θ₁ os) (θ₂ os) = un-∪₁ θ₁ θ₂ os
un-∪₁ oz oz = oz

un-∪₂ : (θ₁ : Δ₁ ⊑ Γ) (θ₂ : Δ₂ ⊑ Γ) → Δ₂ ⊑ ∪-domain θ₁ θ₂
un-∪₂ (θ₁ o') (θ₂ o') = un-∪₂ θ₁ θ₂
un-∪₂ (θ₁ o') (θ₂ os) = un-∪₂ θ₁ θ₂ os
un-∪₂ (θ₁ os) (θ₂ o') = un-∪₂ θ₁ θ₂ o'
un-∪₂ (θ₁ os) (θ₂ os) = un-∪₂ θ₁ θ₂ os
un-∪₂ oz oz = oz

_∪_ : (θ₁ : Δ₁ ⊑ Γ) (θ₂ : Δ₂ ⊑ Γ) → ∪-domain θ₁ θ₂ ⊑ Γ
(θ₁ o') ∪ (θ₂ o') = (θ₁ ∪ θ₂) o'
(θ₁ o') ∪ (θ₂ os) = (θ₁ ∪ θ₂) os
(θ₁ os) ∪ (θ₂ o') = (θ₁ ∪ θ₂) os
(θ₁ os) ∪ (θ₂ os) = (θ₁ ∪ θ₂) os
oz ∪ oz = oz

law-∪₁-inv : (θ₁ : Δ₁ ⊑ Γ) (θ₂ : Δ₂ ⊑ Γ) → un-∪₁ θ₁ θ₂ ₒ (θ₁ ∪ θ₂) ≡ θ₁
law-∪₁-inv (θ₁ o') (θ₂ o') = cong _o' (law-∪₁-inv θ₁ θ₂)
law-∪₁-inv (θ₁ o') (θ₂ os) = cong _o' (law-∪₁-inv θ₁ θ₂)
law-∪₁-inv (θ₁ os) (θ₂ o') = cong _os (law-∪₁-inv θ₁ θ₂)
law-∪₁-inv (θ₁ os) (θ₂ os) = cong _os (law-∪₁-inv θ₁ θ₂)
law-∪₁-inv oz oz = refl

law-∪₂-inv : (θ₁ : Δ₁ ⊑ Γ) (θ₂ : Δ₂ ⊑ Γ) → un-∪₂ θ₁ θ₂ ₒ (θ₁ ∪ θ₂) ≡ θ₂
law-∪₂-inv (θ₁ o') (θ₂ o') = cong _o' (law-∪₂-inv θ₁ θ₂)
law-∪₂-inv (θ₁ o') (θ₂ os) = cong _os (law-∪₂-inv θ₁ θ₂)
law-∪₂-inv (θ₁ os) (θ₂ o') = cong _o' (law-∪₂-inv θ₁ θ₂)
law-∪₂-inv (θ₁ os) (θ₂ os) = cong _os (law-∪₂-inv θ₁ θ₂)
law-∪₂-inv oz oz = refl

pop-domain : {Δ Γ : List I} → Δ ⊑ Γ → List I
pop-domain {Δ = Δ} (θ o') = Δ
pop-domain {Δ = _ ∷ Δ} (θ os) = Δ
pop-domain oz = []

pop : (θ : Δ ⊑ (σ ∷ Γ)) → pop-domain θ ⊑ Γ
pop (θ o') = θ
pop (θ os) = θ

un-pop : (θ : Δ ⊑ (σ ∷ Γ)) → Δ ⊑ (σ ∷ pop-domain θ)
un-pop (θ o') = oi o'
un-pop (θ os) = oi

law-pop-inv : (θ : Δ ⊑ (σ ∷ Γ)) → un-pop θ ₒ pop θ os ≡ θ
law-pop-inv (θ o') = cong _o' (law-oiₒ θ)
law-pop-inv (θ os) = cong _os (law-oiₒ θ)
