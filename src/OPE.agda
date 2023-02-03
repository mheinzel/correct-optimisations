-- Trying shorter notation, as in Conor's paper
module OPE where

open import Data.List using (_∷_ ; [])
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; cong₂ ; sym)

open import Lang

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
