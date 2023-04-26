{-# OPTIONS --allow-unsolved-metas #-}  -- TODO: can we have Semantics?

module Generic.CoDeBruijn.Semantics where

open import Data.List.Base as L hiding (lookup ; [_])
open import Data.Product using (_,_)

open import Data.Var
open import Data.Var.Varlike using (VarLike; base)
open import Data.OPE
open import Data.Relevant using (pairᴿ; _⊢_; _\\_)
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

module _ {- {𝓥 𝓒 : I ─Scoped} (sm : Semantics d 𝓥 𝓒) -} where

 {-# TERMINATING #-}
 semantics :
   {𝓥 𝓒 : I ─Scoped} (sm : Semantics d 𝓥 𝓒) →
   (Γ ─Env) 𝓥 Δ →
   (Γ ─Comp) 𝓒 Δ
 body :
   {𝓥 𝓒 : I ─Scoped} (sm : Semantics d 𝓥 𝓒) →
   (Γ ─Env) 𝓥 Δ → ∀ Θ σ →
   Scope (Tm d) Θ σ Γ → Kripke 𝓥 𝓒 Θ σ Δ
 desc :
   {𝓥 𝓒 : I ─Scoped} {d' : Desc I} (sm : Semantics d 𝓥 𝓒) →
   (Γ ─Env) 𝓥 Δ →
   ⟦ d ⟧ (Scope (Tm d')) σ Γ →
   ⟦ d ⟧ (Kripke 𝓥 𝓒) σ Δ
   -- 𝓒 σ Δ

 semantics sm ρ `var     = Semantics.var sm (lookup ρ z) 
 semantics sm ρ (`con t) = Semantics.alg sm (desc sm ρ t)

 -- TODO: Not sure if this can work, even after reworking the signatures.
 desc {d = `σ A k} sm ρ (a , t) =
   a ,  desc {!!} ρ t 
 desc {d = `X Δ j d} {d' = d'} sm ρ (pairᴿ (t₁ ↑ θ₁) (t₂ ↑ θ₂) c) =
   pairᴿ (body {d = d'} {!!} ρ Δ j {!t₁!}  ↑ {!!}) {!!} {!!}
 desc {d = `∎ i} sm ρ t =
   {!!}

 body sm ρ []      i t        = semantics sm ρ t 
 body sm ρ (_ ∷ _) i (ψ \\ t) = λ σ vs → semantics sm (select (From⊑.toEnv ψ) vs >> th^Env (Semantics.th^𝓥 sm) ρ σ) t

 {-
 closed : Tm d σ [] → 𝓒 σ []
 closed = semantics ε

 eval : VarLike 𝓥 → ∀[ Tm d σ ⇒ 𝓒 σ ]
 eval vl^𝓥 = semantics (base vl^𝓥)
 -}
