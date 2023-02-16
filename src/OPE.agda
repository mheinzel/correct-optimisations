-- Trying shorter notation, as in Conor's paper
module OPE where

open import Data.Product
open import Data.List using (_∷_ ; [] ; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; cong₂ ; sym)

open import Core

infix 21 _o'
infix 21 _os

data _⊑_ : Ctx → Ctx → Set where
  _o' : {Γ₁ Γ₂ : Ctx} → Γ₁ ⊑ Γ₂ →      Γ₁  ⊑ (τ ∷ Γ₂)
  _os : {Γ₁ Γ₂ : Ctx} → Γ₁ ⊑ Γ₂ → (τ ∷ Γ₁) ⊑ (τ ∷ Γ₂)
  oz  : [] ⊑ []

-- θ ϕ ψ

oi : Γ ⊑ Γ
oi {[]} = oz
oi {x ∷ Γ} = oi os

-- [] is an initial object.
oe : {Γ : Ctx} → [] ⊑ Γ
oe {[]} = oz
oe {τ ∷ Γ} = oe o'

infixr 19 _ₒ_

_ₒ_ : ∀ {Γ₁ Γ₂ Γ₃} → Γ₁ ⊑ Γ₂ → Γ₂ ⊑ Γ₃ → Γ₁ ⊑ Γ₃
θ    ₒ ϕ o' = (θ ₒ ϕ) o'
θ o' ₒ ϕ os = (θ ₒ ϕ) o'
θ os ₒ ϕ os = (θ ₒ ϕ) os
oz   ₒ oz   = oz

law-ₒoi : ∀ {Γ₁ Γ₂} → (θ : Γ₁ ⊑ Γ₂) → θ ₒ oi ≡ θ
law-ₒoi oz     = refl
law-ₒoi (θ o') = cong (_o') (law-ₒoi θ)
law-ₒoi (θ os) = cong (_os) (law-ₒoi θ)

law-oiₒ : ∀ {Γ₁ Γ₂} → (θ : Γ₁ ⊑ Γ₂) → oi ₒ θ ≡ θ
law-oiₒ oz     = refl
law-oiₒ (θ o') = cong (_o') (law-oiₒ θ)
law-oiₒ (θ os) = cong (_os) (law-oiₒ θ)

law-ₒₒ :
  ∀ {Γ₁ Γ₂ Γ₃ Γ₄} →
  (θ : Γ₁ ⊑ Γ₂) (ϕ : Γ₂ ⊑ Γ₃) (ψ : Γ₃ ⊑ Γ₄) →
  θ ₒ (ϕ ₒ ψ) ≡ (θ ₒ ϕ) ₒ ψ
law-ₒₒ θ ϕ (ψ o') = cong _o' (law-ₒₒ θ ϕ ψ)
law-ₒₒ θ (ϕ o') (ψ os) = cong _o' (law-ₒₒ θ ϕ ψ)
law-ₒₒ (θ o') (ϕ os) (ψ os) = cong _o' (law-ₒₒ θ ϕ ψ)
law-ₒₒ (θ os) (ϕ os) (ψ os) = cong _os (law-ₒₒ θ ϕ ψ)
law-ₒₒ oz oz oz = refl

_++⊑_ : ∀ {Γ₁ Γ₂ Γ₁' Γ₂'} → Γ₁ ⊑ Γ₂ → Γ₁' ⊑ Γ₂' → (Γ₁ ++ Γ₁') ⊑ (Γ₂ ++ Γ₂')
(θ o') ++⊑ ϕ = (θ ++⊑ ϕ) o'
(θ os) ++⊑ ϕ = (θ ++⊑ ϕ) os
oz ++⊑ ϕ = ϕ

record _⊣R_ {Γ Γ₂ : Ctx} (Γ₁ : Ctx) (ψ : Γ ⊑ (Γ₁ ++ Γ₂)) : Set where
  constructor ⊣r
  field
    {Γ₁'} : Ctx
    {Γ₂'} : Ctx
    ϕ₁ : (Γ₁' ⊑ Γ₁)
    ϕ₂ : (Γ₂' ⊑ Γ₂)
    H : Σ (Γ ≡ Γ₁' ++ Γ₂') λ { refl → ψ ≡ ϕ₁ ++⊑ ϕ₂ }

_⊣_ : ∀ {Γ Γ₂} → (Γ₁ : Ctx) (ψ : Γ ⊑ (Γ₁ ++ Γ₂)) → Γ₁ ⊣R ψ
[] ⊣ ψ = ⊣r oz ψ (refl , refl)
(τ ∷ Γ₁) ⊣ (ψ o')       with Γ₁ ⊣ ψ
(τ ∷ Γ₁) ⊣ (.(ϕ₁ ++⊑ ϕ₂) o') | ⊣r ϕ₁ ϕ₂ (refl , refl) = ⊣r (ϕ₁ o') ϕ₂ (refl , refl)
(τ ∷ Γ₁) ⊣ (ψ os)       with Γ₁ ⊣ ψ
(τ ∷ Γ₁) ⊣ (.(ϕ₁ ++⊑ ϕ₂) os) | ⊣r ϕ₁ ϕ₂ (refl , refl) = ⊣r (ϕ₁ os) ϕ₂ (refl , refl)

law-commute-ₒ++⊑ :
  ∀ {Γ₁ Γ₂ Γ₃ Γ₁' Γ₂' Γ₃'} →
  (θ₁ : Γ₁ ⊑ Γ₂) (θ₂ : Γ₂ ⊑ Γ₃) (ϕ₁ : Γ₁' ⊑ Γ₂') (ϕ₂ : Γ₂' ⊑ Γ₃') →
  (θ₁ ₒ θ₂) ++⊑ (ϕ₁ ₒ ϕ₂) ≡ (θ₁ ++⊑ ϕ₁) ₒ (θ₂ ++⊑ ϕ₂)
law-commute-ₒ++⊑ θ₁ (θ₂ o') ϕ₁ ϕ₂ = cong _o' (law-commute-ₒ++⊑ θ₁ θ₂ ϕ₁ ϕ₂)
law-commute-ₒ++⊑ (θ₁ o') (θ₂ os) ϕ₁ ϕ₂ = cong _o' (law-commute-ₒ++⊑ θ₁ θ₂ ϕ₁ ϕ₂)
law-commute-ₒ++⊑ (θ₁ os) (θ₂ os) ϕ₁ ϕ₂ = cong _os (law-commute-ₒ++⊑ θ₁ θ₂ ϕ₁ ϕ₂)
law-commute-ₒ++⊑ oz oz ϕ₁ ϕ₂ = refl

-- OPEs from a singleton Ctx are isomorphic to Ref.
o-Ref : Ref τ Γ → (τ ∷ []) ⊑ Γ
o-Ref Top     = oe os
o-Ref (Pop x) = (o-Ref x) o'

ref-o : (τ ∷ []) ⊑ Γ → Ref τ Γ
ref-o (θ o') = Pop (ref-o θ)
ref-o (θ os) = Top

project-Env : ∀ {Γ₁ Γ₂} → Γ₁ ⊑ Γ₂ → Env Γ₂ → Env Γ₁
project-Env oz     env          = env
project-Env (θ os) (Cons v env) = Cons v (project-Env θ env)
project-Env (θ o') (Cons v env) = project-Env θ env

law-project-Env-ₒ :
  ∀ {Γ₁ Γ₂ Γ₃} (θ : Γ₁ ⊑ Γ₂) (ϕ : Γ₂ ⊑ Γ₃) (env : Env Γ₃) →
  project-Env (θ ₒ ϕ) env ≡ project-Env θ (project-Env ϕ env)
law-project-Env-ₒ θ (ϕ o') (Cons v env) = law-project-Env-ₒ θ ϕ env
law-project-Env-ₒ (θ o') (ϕ os) (Cons v env) = law-project-Env-ₒ θ ϕ env
law-project-Env-ₒ (θ os) (ϕ os) (Cons v env) = cong (Cons v) (law-project-Env-ₒ θ ϕ env)
law-project-Env-ₒ oz oz env = refl

law-project-Env-oi : (env : Env Γ) → project-Env oi env ≡ env
law-project-Env-oi Nil = refl
law-project-Env-oi (Cons x env) = cong (Cons x) (law-project-Env-oi env)


-- THINGS WITH OPEs

Scoped : Set₁
Scoped = Ctx → Set

record _⇑_ (T : Scoped) (scope : Ctx) : Set where
  constructor _↑_
  field
    {support} : Ctx
    thing : T support
    thinning : support ⊑ scope

-- Arrow with a dot above in Conor's notation.
_→F_ : Scoped → Scoped → Set
S →F T = ∀ {i} → S i → T i

map⇑ : {S T : Scoped} → (S →F T) → ((S ⇑_) →F (T ⇑_))
map⇑ f (s ↑ θ) = f s ↑ θ

thin⇑ : {T : Scoped} {Γ₁ Γ₂ : Ctx} → Γ₁ ⊑ Γ₂ → T ⇑ Γ₁ → T ⇑ Γ₂
thin⇑ ϕ (t ↑ θ) = t ↑ (θ ₒ ϕ)
