-- Strongly Live variable analysis
--
-- Based on Live.agda.
module DeBruijn.StronglyLive where

open import Data.Nat using (_+_)
open import Data.List using (List ; _∷_ ; [])
open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; cong₂)
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import Core
open import DeBruijn.Lang
open import DeBruijn.SubCtx

-- Free variables from declaration of a binding are only live, if the body uses the binding.
combine : SubCtx Γ → SubCtx (σ ∷ Γ) → SubCtx Γ
combine Δ₁ (Drop Δ₂) = Δ₂
combine Δ₁ (Keep Δ₂) = Δ₁ ∪ Δ₂

-- TODO: bind implicit variables explicitly in an order that makes pattern matching on them nicer?
-- IDEA: in Let, add explicit KeepBinding/RemBinding field to match on instead of Δ₂?
data LiveExpr {Γ : Ctx} : (Δ Δ' : SubCtx Γ) → (σ : U) → Set where
  Var :
    (x : Ref σ ⌊ Δ ⌋) →
    LiveExpr Δ (sing Δ x) σ
  App :
    LiveExpr Δ Δ₁ (σ ⇒ τ) →
    LiveExpr Δ Δ₂ σ →
    LiveExpr Δ (Δ₁ ∪ Δ₂) τ
  Lam :
    LiveExpr {σ ∷ Γ} (Keep Δ) Δ₁ τ →
    LiveExpr Δ (pop Δ₁) (σ ⇒ τ)
  Let :
    LiveExpr Δ Δ₁ σ →
    LiveExpr {σ ∷ Γ} (Keep Δ) Δ₂ τ →
    LiveExpr Δ (combine Δ₁ Δ₂) τ
  Val :
    ⟦ σ ⟧ →
    LiveExpr Δ ∅ σ
  Plus :
    LiveExpr Δ Δ₁ NAT →
    LiveExpr Δ Δ₂ NAT →
    LiveExpr Δ (Δ₁ ∪ Δ₂) NAT

-- forget the information about variable usage
forget : LiveExpr Δ Δ' σ → Expr ⌊ Δ ⌋ σ
forget (Var x) = Var x
forget (App e₁ e₂) = App (forget e₁) (forget e₂)
forget (Lam e₁) = Lam (forget e₁)
forget (Let e₁ e₂) = Let (forget e₁) (forget e₂)
forget (Val v) = Val v
forget (Plus e₁ e₂) = Plus (forget e₁) (forget e₂)

-- decide which variables are used or not
analyse : ∀ Δ → Expr ⌊ Δ ⌋ σ → Σ[ Δ' ∈ SubCtx Γ ] LiveExpr Δ Δ' σ
analyse Δ (Var x) = sing Δ x , Var x
analyse Δ (App e₁ e₂) with analyse Δ e₁ | analyse Δ e₂
... | Δ₁ , le₁ | Δ₂ , le₂ = (Δ₁ ∪ Δ₂) , App le₁ le₂
analyse Δ (Lam e₁) with analyse (Keep Δ) e₁
... | Δ' , le₁ = pop Δ' , Lam le₁
analyse Δ (Let e₁ e₂) with analyse Δ e₁ | analyse (Keep Δ) e₂
... | Δ₁ , le₁ | Δ₂ , le₂ = combine Δ₁ Δ₂ , Let le₁ le₂
analyse Δ (Val v) = ∅ , Val v
analyse Δ (Plus e₁ e₂) with analyse Δ e₁ | analyse Δ e₂
... | Δ₁ , le₁ | Δ₂ , le₂ = (Δ₁ ∪ Δ₂) , Plus le₁ le₂

Δ'⊆Δ : LiveExpr Δ Δ' σ → Δ' ⊆ Δ
Δ'⊆Δ {Γ} {Δ} (Var x) = sing⊆ Γ Δ x
Δ'⊆Δ {Γ} {Δ} (App {Δ₁ = Δ₁} {Δ₂ = Δ₂} e₁ e₂) = ∪⊆ Γ Δ₁ Δ₂ Δ (Δ'⊆Δ e₁) (Δ'⊆Δ e₂)
Δ'⊆Δ {Γ} {Δ} (Lam e₁) = Δ'⊆Δ e₁
Δ'⊆Δ {Γ} {Δ} (Let {Δ₁ = Δ₁} {Δ₂ = Drop Δ₂} e₁ e₂) = Δ'⊆Δ e₂
Δ'⊆Δ {Γ} {Δ} (Let {Δ₁ = Δ₁} {Δ₂ = Keep Δ₂} e₁ e₂) = ∪⊆ Γ Δ₁ Δ₂ Δ (Δ'⊆Δ e₁) (Δ'⊆Δ e₂)
Δ'⊆Δ {Γ} {Δ} (Val v) = ∅⊆ Γ Δ
Δ'⊆Δ {Γ} {Δ} (Plus {Δ₁ = Δ₁} {Δ₂ = Δ₂} e₁ e₂) = ∪⊆ Γ Δ₁ Δ₂ Δ (Δ'⊆Δ e₁) (Δ'⊆Δ e₂)

-- forget ∘ analyse ≡ id
analyse-preserves : (e : Expr ⌊ Δ ⌋ σ) → forget (proj₂ (analyse Δ e)) ≡ e
analyse-preserves (Var x) = refl
analyse-preserves (App e₁ e₂) = cong₂ App (analyse-preserves e₁) (analyse-preserves e₂)
analyse-preserves (Lam e₁) = cong Lam (analyse-preserves e₁)
analyse-preserves (Let e₁ e₂) = cong₂ Let (analyse-preserves e₁) (analyse-preserves e₂)
analyse-preserves (Val v) = refl
analyse-preserves (Plus e₁ e₂) = cong₂ Plus (analyse-preserves e₁) (analyse-preserves e₂)

-- Now let's try to define a semantics for LiveExpr...
lookupLive : (Δ Δᵤ : SubCtx Γ) (x : Ref σ ⌊ Δ ⌋) → Env ⌊ Δᵤ ⌋ → .(sing Δ x ⊆ Δᵤ) → ⟦ σ ⟧
lookupLive (Drop Δ) (Drop Δᵤ) x env H = lookupLive Δ Δᵤ x env H
lookupLive (Drop Δ) (Keep Δᵤ) x (Cons v env) H = lookupLive Δ Δᵤ x env H
lookupLive (Keep Δ) (Drop Δᵤ) (Pop x) env H = lookupLive Δ Δᵤ x env H
lookupLive (Keep Δ) (Keep Δᵤ) Top (Cons v env) H = v
lookupLive (Keep Δ) (Keep Δᵤ) (Pop x) (Cons v env) H = lookupLive Δ Δᵤ x env H

evalLive : ∀ Δᵤ → LiveExpr Δ Δ' τ → Env ⌊ Δᵤ ⌋ → .(Δ' ⊆ Δᵤ) → ⟦ τ ⟧
evalLive {Γ} {Δ} Δᵤ (Var x) env H =
  lookupLive Δ Δᵤ x env H
evalLive Δᵤ (App {Δ₁ = Δ₁} {Δ₂ = Δ₂} e₁ e₂) env H =
  (evalLive Δᵤ e₁ env (⊆-trans Δ₁ (Δ₁ ∪ Δ₂) Δᵤ (⊆∪₁ Δ₁ Δ₂) H))
    (evalLive Δᵤ e₂ env (⊆-trans Δ₂ (Δ₁ ∪ Δ₂) Δᵤ (⊆∪₂ Δ₁ Δ₂) H))
evalLive Δᵤ (Lam e₁) env H =
  λ v → evalLive (Keep Δᵤ) e₁ (Cons v env) H
evalLive Δᵤ (Let {Δ = Δ} {Δ₁ = Δ₁} {Δ₂ = Drop Δ₂} e₁ e₂) env H =
  evalLive (Drop Δᵤ) e₂ env H
evalLive Δᵤ (Let {Δ = Δ} {Δ₁ = Δ₁} {Δ₂ = Keep Δ₂} e₁ e₂) env H =
  evalLive (Keep Δᵤ) e₂
    (Cons (evalLive Δᵤ e₁ env (⊆∪₁-trans Δ₁ Δ₂ Δᵤ H)) env)
    (⊆∪₂-trans Δ₁ Δ₂ Δᵤ H)
evalLive Δᵤ (Val v) env H =
  v
evalLive Δᵤ (Plus {Δ} {Δ₁} {Δ₂} e₁ e₂) env H =
    evalLive Δᵤ e₁ env (⊆∪₁-trans Δ₁ Δ₂ Δᵤ H)
 +  evalLive Δᵤ e₂ env (⊆∪₂-trans Δ₁ Δ₂ Δᵤ H)

lookupLive-correct : (x : Ref σ ⌊ Δ ⌋) (Δᵤ : SubCtx Γ) (env : Env ⌊ Δ ⌋) → .(H' : sing Δ x ⊆ Δᵤ) → .(H : Δᵤ ⊆ Δ) →
  lookupLive Δ Δᵤ x (prjEnv Δᵤ Δ H env) H' ≡ lookup x env
lookupLive-correct {σ} {[]} {Empty} () Δᵤ Nil H' H
lookupLive-correct {σ} {τ ∷ Γ} {Drop Δ} x (Drop Δᵤ) env H' H = lookupLive-correct x Δᵤ env H' H
lookupLive-correct {.τ} {τ ∷ Γ} {Keep Δ} Top (Keep Δᵤ) (Cons v env) H' H = refl
lookupLive-correct {σ} {τ ∷ Γ} {Keep Δ} (Pop x) (Drop Δᵤ) (Cons v env) H' H = lookupLive-correct x Δᵤ env H' H
lookupLive-correct {σ} {τ ∷ Γ} {Keep Δ} (Pop x) (Keep Δᵤ) (Cons v env) H' H = lookupLive-correct x Δᵤ env H' H

-- evalLive ≡ eval ∘ forget
evalLive-correct :
  (e : LiveExpr Δ Δ' σ) (Δᵤ : SubCtx Γ) (env : Env ⌊ Δ ⌋) →
  .(H' : Δ' ⊆ Δᵤ) → .(H : Δᵤ ⊆ Δ) →
  evalLive Δᵤ e (prjEnv Δᵤ Δ H env) H' ≡ eval (forget e) env
evalLive-correct (Var x) Δᵤ env H' H =
  lookupLive-correct x Δᵤ env H' H
evalLive-correct (App {Δ₁ = Δ₁} {Δ₂ = Δ₂} e₁ e₂) Δᵤ env H' H =
  cong₂ (λ v → v)
    (evalLive-correct e₁ Δᵤ env (⊆∪₁-trans Δ₁ Δ₂ Δᵤ H') H)
    (evalLive-correct e₂ Δᵤ env (⊆∪₂-trans Δ₁ Δ₂ Δᵤ H') H)
evalLive-correct (Lam {Δ = Δ} e₁) Δᵤ env H' H =
  extensionality _ _ λ v →
    evalLive-correct e₁ (Keep Δᵤ) (Cons v env) H' H
evalLive-correct (Let {Δ₁ = Δ₁} {Δ₂ = Drop Δ₂} e₁ e₂) Δᵤ env H' H =
  evalLive-correct e₂ (Drop Δᵤ) (Cons (eval (forget e₁) env) env) H' H
evalLive-correct (Let {Δ = Δ} {Δ₁ = Δ₁} {Δ₂ = Keep Δ₂} e₁ e₂) Δᵤ env H' H =
    evalLive (Keep Δᵤ) e₂ (Cons (evalLive Δᵤ e₁ (prjEnv Δᵤ Δ H env) _) (prjEnv Δᵤ Δ H env)) _
  ≡⟨ evalLive-correct e₂ (Keep Δᵤ) (Cons (evalLive Δᵤ e₁ (prjEnv Δᵤ Δ H env) _) env) _ _ ⟩
    eval (forget e₂) (Cons (evalLive Δᵤ e₁ (prjEnv Δᵤ Δ H env) _) env)
  ≡⟨ cong (λ v → eval (forget e₂) (Cons v env)) (evalLive-correct e₁ Δᵤ env _ _) ⟩
    eval (forget e₂) (Cons (eval (forget e₁) env) env)
  ∎
evalLive-correct (Val v) Δᵤ env H' H = refl
evalLive-correct (Plus {Δ} {Δ₁} {Δ₂} e₁ e₂) Δᵤ env H' H =
  cong₂ _+_
    (evalLive-correct e₁ Δᵤ env (⊆∪₁-trans Δ₁ Δ₂ Δᵤ H') H)
    (evalLive-correct e₂ Δᵤ env (⊆∪₂-trans Δ₁ Δ₂ Δᵤ H') H)
