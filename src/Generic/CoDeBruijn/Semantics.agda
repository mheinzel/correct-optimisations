module Generic.CoDeBruijn.Semantics where

open import Data.List.Base as L hiding (lookup ; [_])

open import Data.Var
open import Data.Var.Varlike using (VarLike; base)
open import Data.OPE
open import Data.Relevant using (_⊢_; _\\_)
open import Data.Relation
open import Relation.Unary
open import Data.Environment
open import Function using (flip)
open import Generic.Syntax
open import Generic.CoDeBruijn.Syntax

private
  variable
    I : Set
    σ : I
    Γ Δ : List I
    d : Desc I

module _ {d : Desc I} where
  _─Comp : List I → I ─Scoped → List I → Set
  (Γ ─Comp) 𝓒 Δ = ∀ {σ} → Tm d σ Γ → 𝓒 σ Δ

-- TODO: deduplicate with DeBruijn.Semantics!
record Semantics (d : Desc I) (𝓥 𝓒 : I ─Scoped) : Set where
 field
   th^𝓥 : Thinnable (𝓥 σ)
   var : ∀[ 𝓥 σ ⇒ 𝓒 σ ]
   alg : ∀[ ⟦ d ⟧ (Kripke 𝓥 𝓒) σ ⇒ 𝓒 σ ]

module _ {𝓥 𝓒 : I ─Scoped} (sm : Semantics d 𝓥 𝓒) where
 open Semantics sm

 {-# TERMINATING #-}
 semantics : (Γ ─Env) 𝓥 Δ → (Γ ─Comp) 𝓒 Δ
 body      : (Γ ─Env) 𝓥 Δ → ∀ Θ σ →
             Scope (Tm d) Θ σ Γ → Kripke 𝓥 𝓒 Θ σ Δ

 semantics ρ `var     = var (lookup ρ z) 
 semantics ρ (`con t) = alg (fmap d (body ρ) t)

 body ρ []       i t = semantics ρ t 
 body ρ (_ ∷ _) i (_\\_ {Γ'} ψ t) = λ σ vs → semantics (select (From⊑.toEnv ψ) vs >> th^Env th^𝓥 ρ σ) t

 closed : Tm d σ [] → 𝓒 σ []
 closed = semantics ε

 eval : VarLike 𝓥 → ∀[ Tm d σ ⇒ 𝓒 σ ]
 eval vl^𝓥 = semantics (base vl^𝓥)
