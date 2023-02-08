-- Dead Binding Elimination using strongly live variable analysis
--
-- Based on DBE.agda.
module DeBruijn.DeadBindingStrong where

open import Data.Nat using (_+_)
open import Data.List using (List ; _∷_ ; [])
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; trans ; cong ; cong₂ ; sym)
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import Core
open import DeBruijn.Lang
open import DeBruijn.SubCtx
open import DeBruijn.StronglyLive

sing-ref : (Δ : SubCtx Γ) (x : Ref σ ⌊ Δ ⌋) → Ref σ ⌊ sing Δ x ⌋
sing-ref {[]} Empty ()
sing-ref {τ ∷ Γ} (Drop Δ) x = sing-ref Δ x
sing-ref {τ ∷ Γ} (Keep Δ) Top = Top
sing-ref {τ ∷ Γ} (Keep Δ) (Pop x) = sing-ref Δ x

-- IDEA: it might make sense to generalise this further:
-- dbe' : LiveExpr Δ Δ' σ → (Δᵤ : SubCtx Γ) → .(H : Δ' ⊆ Δᵤ) → Expr ⌊ Δᵤ ⌋ σ
--
dbe : LiveExpr Δ Δ' σ → Expr ⌊ Δ' ⌋ σ
dbe {Γ} {Δ} (Var x) =
  Var (sing-ref Δ x)
dbe (App {Δ = Δ} {Δ₁ = Δ₁} {Δ₂ = Δ₂} e₁ e₂) =
  App (injExpr₁ Δ₁ Δ₂ (dbe e₁)) (injExpr₂ Δ₁ Δ₂ (dbe e₂))
dbe (Lam {Δ = Δ} {Δ₁ = Δ₁} e₁) =
  Lam (renameExpr Δ₁ (Keep (pop Δ₁)) (⊆-refl (pop Δ₁)) (dbe e₁))
dbe (Let {Δ₁ = Δ₁} {Δ₂ = Drop Δ₂} e₁ e₂) =
  dbe e₂
dbe (Let {Δ₁ = Δ₁} {Δ₂ = Keep Δ₂} e₁ e₂) =
  Let
    (injExpr₁ Δ₁ Δ₂ (dbe e₁))
    (renameExpr (Keep Δ₂) (Keep (Δ₁ ∪ Δ₂)) (⊆∪₂ Δ₁ Δ₂) (dbe e₂))
dbe (Val v) =
  Val v
dbe (Plus {Δ} {Δ₁} {Δ₂} e₁ e₂) =
  Plus (injExpr₁ Δ₁ Δ₂ (dbe e₁)) (injExpr₂ Δ₁ Δ₂ (dbe e₂))

sing-ref-correct : (x : Ref σ ⌊ Δ ⌋) (Δᵤ : SubCtx Γ) → (env : Env ⌊ Δᵤ ⌋) → .(H : sing Δ x ⊆ Δᵤ) →
  lookup (renameVar (sing Δ x) Δᵤ H (sing-ref Δ x)) env ≡ lookupLive Δ Δᵤ x env H
sing-ref-correct {Δ = Drop Δ} x (Drop Δᵤ) env H = sing-ref-correct x Δᵤ env H
sing-ref-correct {Δ = Drop Δ} x (Keep Δᵤ) (Cons v env) H = sing-ref-correct x Δᵤ env H
sing-ref-correct {Δ = Keep Δ} (Pop x) (Drop Δᵤ) env H = sing-ref-correct x Δᵤ env H
sing-ref-correct {Δ = Keep Δ} Top (Keep Δᵤ) (Cons v env) H = refl
sing-ref-correct {Δ = Keep Δ} (Pop x) (Keep Δᵤ) (Cons v env) H = sing-ref-correct x Δᵤ env H

-- eval ∘ dbe ≡ evalLive
dbe-correct :
  (e : LiveExpr Δ Δ' σ) (Δᵤ : SubCtx Γ) (env : Env ⌊ Δᵤ ⌋) →
  .(H : Δ' ⊆ Δᵤ) →
  eval (renameExpr Δ' Δᵤ H (dbe e)) env ≡ evalLive Δᵤ e env H
dbe-correct (Var x) Δᵤ env H =
  sing-ref-correct x Δᵤ env H
dbe-correct (App {Δ = Δ} {Δ₁ = Δ₁} {Δ₂ = Δ₂} e₁ e₂) Δᵤ env H
  rewrite renameExpr-trans Δ₁ (Δ₁ ∪ Δ₂) Δᵤ (⊆∪₁ Δ₁ Δ₂) H (dbe e₁)
  rewrite renameExpr-trans Δ₂ (Δ₁ ∪ Δ₂) Δᵤ (⊆∪₂ Δ₁ Δ₂) H (dbe e₂) =
  cong₂ (λ v → v)
    (dbe-correct e₁ Δᵤ env _)
    (dbe-correct e₂ Δᵤ env _)
dbe-correct (Lam {Δ₁ = Δ₁} e₁) Δᵤ env H =
  extensionality _ _ λ v →
      eval (renameExpr (Keep (pop Δ₁)) (Keep Δᵤ) _ (renameExpr Δ₁ (Keep (pop Δ₁)) _ (dbe e₁))) (Cons v env)
    ≡⟨ cong (λ x → eval x (Cons v env)) (renameExpr-trans Δ₁ (Keep (pop Δ₁)) (Keep Δᵤ) _ H (dbe e₁)) ⟩
      eval (renameExpr Δ₁ (Keep Δᵤ) _ (dbe e₁)) (Cons v env)
    ≡⟨ dbe-correct e₁ (Keep Δᵤ) (Cons v env) H ⟩
      evalLive (Keep Δᵤ) e₁ (Cons v env) _
    ∎
dbe-correct (Let {Δ = Δ} {Δ₁ = Δ₁} {Δ₂ = Drop Δ₂} e₁ e₂) Δᵤ env H =
    eval (renameExpr Δ₂ Δᵤ _ (dbe e₂)) env
  ≡⟨ renameExpr-preserves Δ₂ Δᵤ _ (dbe e₂) env ⟩
     eval (dbe e₂) (prjEnv Δ₂ Δᵤ _ env)
  ≡⟨ sym (renameExpr-preserves (Drop Δ₂) (Drop Δᵤ) _ (dbe e₂) env) ⟩
     eval (renameExpr (Drop Δ₂) (Drop Δᵤ) _ (dbe e₂)) env
  ≡⟨ dbe-correct e₂ (Drop Δᵤ) env _ ⟩
    evalLive (Drop Δᵤ) e₂ env _
  ∎
dbe-correct (Let {Δ₁ = Δ₁} {Δ₂ = Keep Δ₂} e₁ e₂) Δᵤ env H =
    eval
      (renameExpr (Keep (Δ₁ ∪ Δ₂)) (Keep Δᵤ) _ (renameExpr (Keep Δ₂) (Keep (Δ₁ ∪ Δ₂)) _ (dbe e₂)))
      (Cons (eval (renameExpr (Δ₁ ∪ Δ₂) Δᵤ _ (injExpr₁ Δ₁ Δ₂ (dbe e₁))) env) env)
  ≡⟨ cong (λ e → eval e _)
      (renameExpr-trans (Keep Δ₂) (Keep (Δ₁ ∪ Δ₂)) (Keep Δᵤ) (⊆∪₂ Δ₁ Δ₂) H (dbe e₂)) ⟩
    eval
      (renameExpr (Keep Δ₂) (Keep Δᵤ) _ (dbe e₂))
      (Cons (eval (renameExpr (Δ₁ ∪ Δ₂) Δᵤ _ (injExpr₁ Δ₁ Δ₂ (dbe e₁))) env) env)
  ≡⟨ cong (λ e → eval (renameExpr (Keep Δ₂) (Keep Δᵤ) (⊆∪₂-trans Δ₁ Δ₂ Δᵤ H) (dbe e₂)) (Cons (eval e env) env))
      (renameExpr-trans Δ₁ (Δ₁ ∪ Δ₂) Δᵤ (⊆∪₁ Δ₁ Δ₂) H (dbe e₁)) ⟩
    eval
      (renameExpr (Keep Δ₂) (Keep Δᵤ) _ (dbe e₂))
      (Cons (eval (renameExpr Δ₁ Δᵤ _ (dbe e₁)) env) env)
  ≡⟨ cong (λ v → eval (renameExpr (Keep Δ₂) (Keep Δᵤ) (⊆∪₂-trans Δ₁ Δ₂ Δᵤ H) (dbe e₂)) (Cons v env))
      (dbe-correct e₁ Δᵤ env _) ⟩
    eval
      (renameExpr (Keep Δ₂) (Keep Δᵤ) _ (dbe e₂))
      (Cons (evalLive Δᵤ e₁ env _) env)
  ≡⟨ dbe-correct e₂ (Keep Δᵤ) (Cons (evalLive Δᵤ e₁ env _) env) _ ⟩
    evalLive (Keep Δᵤ) e₂ (Cons (evalLive Δᵤ e₁ env _) env) _
  ∎
dbe-correct (Val v) Δᵤ env H = refl
dbe-correct (Plus {Δ} {Δ₁} {Δ₂} e₁ e₂) Δᵤ env H
  rewrite renameExpr-trans Δ₁ (Δ₁ ∪ Δ₂) Δᵤ (⊆∪₁ Δ₁ Δ₂) H (dbe e₁)
  rewrite renameExpr-trans Δ₂ (Δ₁ ∪ Δ₂) Δᵤ (⊆∪₂ Δ₁ Δ₂) H (dbe e₂) =
  cong₂ _+_
    (dbe-correct e₁ Δᵤ env _)
    (dbe-correct e₂ Δᵤ env _)

optimise : (Δ : SubCtx Γ) → Expr ⌊ Δ ⌋ σ → Σ[ Δ' ∈ SubCtx Γ ] (Expr ⌊ Δ' ⌋ σ)
optimise Δ e = let Δ' , e' = analyse Δ e in Δ' , dbe e'

optimise-correct : (Δ : SubCtx Γ) (e : Expr ⌊ Δ ⌋ σ) (env : Env ⌊ Δ ⌋) →
  let Δ' , e' = optimise Δ e
      H = Δ'⊆Δ (proj₂ (analyse Δ e))
  in eval e' (prjEnv Δ' Δ H env) ≡ eval e env
optimise-correct {Γ} Δ e env =
  let Δ' , le = analyse Δ e
      H = Δ'⊆Δ le
  in
    eval (dbe le) (prjEnv Δ' Δ H env)
  ≡⟨ cong (λ e → eval e (prjEnv Δ' Δ H env)) (sym (renameExpr-id Δ' (dbe le))) ⟩
    eval (renameExpr Δ' Δ' (⊆-refl Δ') (dbe le)) (prjEnv Δ' Δ H env)
  ≡⟨ dbe-correct le Δ' (prjEnv Δ' Δ H env) (⊆-refl Δ') ⟩  -- eval ∘ dbe ≡ evalLive
    evalLive Δ' le (prjEnv Δ' Δ H env) (⊆-refl Δ')
  ≡⟨ evalLive-correct le Δ' env (⊆-refl Δ') H ⟩  -- evalLive ≡ eval ∘ forget
    eval (forget le) env
  ≡⟨ cong (λ e → eval e env) (analyse-preserves {Γ} {Δ} e) ⟩  -- forget ∘ analyse ≡ id
    eval e env
  ∎


module Iteration where
  import DeBruijn.DeadBinding as DBE

  -- TODO: how feasible is this?
  optimise-converges : (Δ : SubCtx Γ) (e : Expr ⌊ Δ ⌋ σ) → DBE.optimise Δ e ≡ optimise Δ e
  optimise-converges Δ e = {!!}
