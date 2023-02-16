-- Dead binding elimination, but in a single pass (equivalent to strongly live variable analysis)
-- Using co-de-Bruijn representation.
module CoDeBruijn.DeadBindingStrong where

open import Data.Nat using (_+_)
open import Data.List using (List ; _∷_ ; [] ; _++_)
open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; cong₂ ; sym ; trans)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Function using (_∘_ ; _$_)

open import Core
open import CoDeBruijn.Lang
open import OPE

-- This is needed because our notion of semantical equivalence is "same evaluation result",
-- and values include Agda functions.
-- We might want something different?
postulate
  -- extensionality : {A B : Set} → (f g : A → B) (H : (x : A) → f x ≡ g x) → f ≡ g
  extensionality :
    {S : Set} {T : S -> Set} (f g : (x : S) -> T x) ->
    ((x : S) -> f x ≡ g x) ->
    f ≡ g

let-? : ∀ {σ τ Γ} → (Expr σ ×R ((σ ∷ []) ⊢ Expr τ)) Γ → Expr τ ⇑ Γ
let-? (pair (e₁ ↑ θ₁) (((oz o') \\ e₂) ↑ θ₂) c) = e₂ ↑ θ₂  -- remove binding
let-? (pair (e₁ ↑ θ₁) (((oz os) \\ e₂) ↑ θ₂) c) = Let (pair (e₁ ↑ θ₁) (((oz os) \\ e₂) ↑ θ₂) c) ↑ oi


-- Also remove bindings that are tagged live in the input Expr,
-- but where the body is revealed to not use the top variable after the recursive call.
dbe : Expr τ Γ → Expr τ ⇑ Γ
dbe Var =
  Var ↑ oz os
dbe (App (pair (e₁ ↑ ϕ₁) (e₂ ↑ ϕ₂) cover)) =
  map⇑ App (thin⇑ ϕ₁ (dbe e₁) ,R thin⇑ ϕ₂ (dbe e₂))
  -- let e₁' ↑ θ₁ = dbe e₁
  --     e₂' ↑ θ₂ = dbe e₂
  --     p ↑ ψ = (e₁' ↑ (θ₁ ₒ ϕ₁)) ,R (e₂' ↑ (θ₂ ₒ ϕ₂))
  -- in App p ↑ ψ
dbe (Lam {σ} (_\\_ {bound = Γ'} ψ e)) =
  map⇑ (Lam ∘ map⊢ ψ) (Γ' \\R dbe e)
  -- let (ϕ \\ e') ↑ θ = Γ' \\R dbe e
  -- in Lam ((ϕ ₒ ψ) \\ e') ↑ θ
dbe (Let {σ} (pair (e₁ ↑ ϕ₁) (_\\_ {bound = Γ'} ψ e₂ ↑ ϕ₂) c)) =
  let p ↑ θ = thin⇑ ϕ₁ (dbe e₁) ,R thin⇑ ϕ₂ (map⇑ (map⊢ ψ) (Γ' \\R dbe e₂))
  in thin⇑ θ (let-? p)
  -- let e₁' ↑ θ₁  = dbe e₁
  --     (ψ' \\ e₂') ↑ θ₂ = Γ' \\R dbe e₂
  --     p ↑ θ = (e₁' ↑ (θ₁ ₒ ϕ₁)) ,R (((ψ' ₒ ψ) \\ e₂') ↑ (θ₂ ₒ ϕ₂))
  --     p' ↑ θ? = let-? p
  -- in p' ↑ (θ? ₒ θ)
dbe (Val v) =
  Val v ↑ oz
dbe (Plus (pair (e₁ ↑ ϕ₁) (e₂ ↑ ϕ₂) cover)) =
  map⇑ Plus (thin⇑ ϕ₁ (dbe e₁) ,R thin⇑ ϕ₂ (dbe e₂))
  -- let e₁' ↑ θ₁ = dbe e₁
  --     e₂' ↑ θ₂ = dbe e₂
  --     p ↑ ψ = (e₁' ↑ (θ₁ ₒ ϕ₁)) ,R (e₂' ↑ (θ₂ ₒ ϕ₂))
  -- in App p ↑ ψ

-- IDEA: We could show that this is a fixpoint? dbe (dbe e) ≡ dbe e

-- TODO: implicit args?
helper-assoc :
  ∀ {Γ Γ₁ Γ₂ Γ' Γ''} →
  (θ₁  : Γ  ⊑ Γ₁) →
  (θ₁' : Γ₁ ⊑ Γ') →
  (θ₂  : Γ  ⊑ Γ₂) →
  (θ₂' : Γ₂ ⊑ Γ') →
  (θ   : Γ' ⊑ Γ'') →
  θ₁ ₒ θ₁' ≡ θ₂ ₒ θ₂' →
  θ₁ ₒ θ₁' ₒ θ ≡ θ₂ ₒ θ₂' ₒ θ
helper-assoc θ₁ θ₁' θ₂ θ₂' θ h =
    θ₁ ₒ θ₁' ₒ θ
  ≡⟨ law-ₒₒ _ _ _ ⟩
    (θ₁ ₒ θ₁') ₒ θ
  ≡⟨  cong (_ₒ θ) h ⟩
    (θ₂ ₒ θ₂') ₒ θ
  ≡⟨ sym (law-ₒₒ _ _ _) ⟩
    θ₂ ₒ θ₂' ₒ θ
  ∎

-- TODO: prove semantics preserving!
dbe-correct :
  {Γₑ : Ctx} (e : Expr τ Γ) (env : Env Γₑ) (θ : Γ ⊑ Γₑ) →
  let e' ↑ θ' = dbe e
  in eval e' (θ' ₒ θ) env ≡ eval e θ env

dbe-correct Var env θ =
  cong (λ x → lookup Top (project-Env x env)) (law-oiₒ θ)

dbe-correct (App (pair (e₁ ↑ ϕ₁) (e₂ ↑ ϕ₂) cover)) env θ
  with dbe e₁   | dbe e₂   | dbe-correct e₁ env (ϕ₁ ₒ θ) | dbe-correct e₂ env (ϕ₂ ₒ θ) 
...  | e₁' ↑ θ₁ | e₂' ↑ θ₂ | h₁                          | h₂
  with cop (θ₁ ₒ ϕ₁) (θ₂ ₒ ϕ₂) 
...  | coproduct Γ' ψ θ₁' θ₂' p₁ p₂ c =
    eval e₁' (θ₁' ₒ ψ ₒ θ) env
      (eval e₂' (θ₂' ₒ ψ ₒ θ) env)
  ≡⟨ cong (λ x → eval e₁' _ _ (eval e₂' x env)) (helper-assoc _ _ _ _ _ (sym p₂)) ⟩
    eval e₁' (θ₁' ₒ ψ ₒ θ) env
      (eval e₂' (θ₂ ₒ ϕ₂ ₒ θ) env)
  ≡⟨ cong (λ x → eval e₁' x env _) (helper-assoc _ _ _ _ _ (sym p₁)) ⟩
    eval e₁' (θ₁ ₒ ϕ₁ ₒ θ) env
      (eval e₂' (θ₂ ₒ ϕ₂ ₒ θ) env)
  ≡⟨ cong₂ _$_ h₁ h₂ ⟩
    eval e₁ (ϕ₁ ₒ θ) env
      (eval e₂ (ϕ₂ ₒ θ) env)
  ∎

dbe-correct (Lam (_\\_ {bound = Γ'} ψ e)) env θ with dbe e   | dbe-correct e
dbe-correct (Lam (_\\_ {bound = Γ'} ψ e)) env θ    | e' ↑ θ' | h with Γ' ⊣ θ'
dbe-correct (Lam (_\\_ {bound = Γ'} ψ e)) env θ    | e' ↑ θ' | h    | ⊣r ϕ₁ ϕ₂ (refl , refl) =
  extensionality _ _ λ v →
      eval e' ((ϕ₁ ₒ ψ) ++⊑ (ϕ₂ ₒ θ)) (Cons v env)
    ≡⟨ cong (λ x → eval e' x (Cons v env)) (law-commute-ₒ++⊑ ϕ₁ ψ ϕ₂ θ) ⟩
      eval e' ((ϕ₁ ++⊑ ϕ₂) ₒ (ψ ++⊑ θ)) (Cons v env)
    ≡⟨ h (Cons v env) (ψ ++⊑ θ) ⟩
      eval e (ψ ++⊑ θ) (Cons v env)
    ∎

{-
dbe-correct (Let u e₁ e₂) env θ = {!!}
dbe-correct (Val v) env θ = {!!}
dbe-correct (Plus u e₁ e₂) env θ = {!!}
-}
