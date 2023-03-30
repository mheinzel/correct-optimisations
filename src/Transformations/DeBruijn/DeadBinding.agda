-- Dead Binding Elimination (simple)
module Transformations.DeBruijn.DeadBinding where

open import Data.Nat using (_+_; ℕ)
open import Data.List using (List ; _∷_ ; [])
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; cong₂ ; sym)
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import Language.Core
open Language.Core.Env {U} {⟦_⟧}
open Language.Core.Ref {U} {⟦_⟧}
open import Language.DeBruijn
open import Transformations.Recursion
open import Transformations.DeBruijn.SubCtx
open import Transformations.DeBruijn.Live

private
  variable
    σ τ : U
    Γ : Ctx
    Δ Δ' : SubCtx Γ

sing-ref : (Δ : SubCtx Γ) (x : Ref σ ⌊ Δ ⌋) → Ref σ ⌊ sing Δ x ⌋
sing-ref {[]} Empty ()
sing-ref {τ ∷ Γ} (Drop Δ) x = sing-ref Δ x
sing-ref {τ ∷ Γ} (Keep Δ) Top = Top
sing-ref {τ ∷ Γ} (Keep Δ) (Pop x) = sing-ref Δ x

-- IDEA: it might make sense to generalise this further:
-- dbe' : LiveExpr Δ Δ' σ → (Δᵤ : SubCtx Γ) → .(H : Δ' ⊆ Δᵤ) → Expr σ ⌊ Δᵤ ⌋
--
dbe : LiveExpr Δ Δ' σ → Expr σ ⌊ Δ' ⌋
dbe {Γ} {Δ} (Var x) =
  Var (sing-ref Δ x)
dbe (App {Δ = Δ} {Δ₁ = Δ₁} {Δ₂ = Δ₂} e₁ e₂) =
  App (injExpr₁ Δ₁ Δ₂ (dbe e₁)) (injExpr₂ Δ₁ Δ₂ (dbe e₂))
dbe (Lam {Δ = Δ} {Δ₁ = Δ₁} e₁) =
  Lam (renameExpr Δ₁ (Keep (pop Δ₁)) (⊆-refl (pop Δ₁)) (dbe e₁))
dbe (Let {Δ₁ = Δ₁} {Δ₂ = Drop Δ₂} e₁ e₂) =
  injExpr₂ Δ₁ Δ₂ (dbe e₂)
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
    eval (renameExpr (Δ₁ ∪ Δ₂) Δᵤ _ (injExpr₂ Δ₁ Δ₂ (dbe e₂))) env
  ≡⟨ cong (λ e → eval e env) (renameExpr-trans Δ₂ (Δ₁ ∪ Δ₂) Δᵤ (⊆∪₂ Δ₁ Δ₂) H (dbe e₂)) ⟩
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

optimise : (Δ : SubCtx Γ) → Expr σ ⌊ Δ ⌋ → Σ[ Δ' ∈ SubCtx Γ ] (Expr σ ⌊ Δ' ⌋)
optimise Δ e = let Δ' , e' = analyse Δ e in Δ' , dbe e'

optimise-correct : (Δ : SubCtx Γ) (e : Expr σ ⌊ Δ ⌋) (env : Env ⌊ Δ ⌋) →
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
  ≡⟨ cong (λ e → eval e env) (analyse-preserves {Δ = Δ} e) ⟩  -- forget ∘ analyse ≡ id
    eval e env
  ∎


num-bindings' : Σ[ Δ ∈ SubCtx Γ ] Expr σ ⌊ Δ ⌋ → ℕ
num-bindings' (Δ , e) = num-bindings e

module <-num-bindings-Well-founded { Γ σ } where
  open Inverse-image-Well-founded {Σ[ Δ ∈ SubCtx Γ ] Expr σ ⌊ Δ ⌋} _<_ num-bindings' public

  wf : WF.Well-founded _⊰_
  wf = ii-wf <-ℕ-wf

_<-bindings_ : (e₁ e₂ : Σ[ Δ ∈ SubCtx Γ ] Expr σ ⌊ Δ ⌋) → Set
e₁ <-bindings e₂ = num-bindings' e₁ < num-bindings' e₂

<-bindings-wf : {Γ : Ctx} {σ : U} → WF.Well-founded (_<-bindings_ {Γ} {σ})
<-bindings-wf = wf
  where
    open <-num-bindings-Well-founded


mutual
  -- Keep optimising as long as the number of bindings decreases.
  -- This is not structurally recursive, but we have a Well-Foundedness proof.
  fix-optimise-wf : (Δ : SubCtx Γ) (e : Expr σ ⌊ Δ ⌋) → WF.Acc _<-bindings_ (Δ , e) →
    Σ[ Δ' ∈ SubCtx Γ ] ((Δ' ⊆ Δ) × Expr σ ⌊ Δ' ⌋)
  fix-optimise-wf {Γ} Δ e accu =
    let Δ' , e' = optimise Δ e
        H = Δ'⊆Δ (proj₂ (analyse Δ e))
    in fix-optimise-wf-helper Δ Δ' e e' H accu

  -- Without the helper, there were issues with the with-abstraction using a
  -- result of the let-binding.
  fix-optimise-wf-helper :
    (Δ Δ' : SubCtx Γ) (e : Expr σ ⌊ Δ ⌋) (e' : Expr σ ⌊ Δ' ⌋) →
    (H' : Δ' ⊆ Δ) → WF.Acc _<-bindings_ (Δ , e) →
    Σ[ Δ'' ∈ SubCtx Γ ] ((Δ'' ⊆ Δ) × Expr σ ⌊ Δ'' ⌋)
  fix-optimise-wf-helper Δ Δ' e e' H' (WF.acc g) with num-bindings e' <? num-bindings e
  ... | inj₂ p = Δ' , (H' , e')
  ... | inj₁ p = let Δ'' , (H'' , e'') = fix-optimise-wf Δ' e' (g (Δ' , e') p)
                 in Δ'' , (⊆-trans Δ'' Δ' Δ H'' H') , e''

fix-optimise : (Δ : SubCtx Γ) → Expr σ ⌊ Δ ⌋ → Σ[ Δ' ∈ SubCtx Γ ] ((Δ' ⊆ Δ) × Expr σ ⌊ Δ' ⌋)
fix-optimise {Γ} Δ e = fix-optimise-wf Δ e (<-bindings-wf (Δ , e))

mutual
  -- Not pretty, but it works.
  fix-optimise-wf-correct : (Δ : SubCtx Γ) (e : Expr σ ⌊ Δ ⌋) (env : Env ⌊ Δ ⌋) (accu : WF.Acc _<-bindings_ (Δ , e)) →
    let Δ'' , (H'' , e'') = fix-optimise-wf Δ e accu
    in eval e'' (prjEnv Δ'' Δ H'' env) ≡ eval e env
  fix-optimise-wf-correct Δ e env accu =
    let Δ' , e' = optimise Δ e
        H' = Δ'⊆Δ (proj₂ (analyse Δ e))
        Δ'' , (H'' , e'') = fix-optimise-wf-helper Δ Δ' e e' H' accu
    in eval e'' (prjEnv Δ'' Δ H'' env)
     ≡⟨ fix-optimise-wf-helper-correct Δ Δ' e e' env H' accu ⟩
       eval e' (prjEnv Δ' Δ H' env)
     ≡⟨ optimise-correct Δ e env ⟩
       eval e env
     ∎

  fix-optimise-wf-helper-correct :
    (Δ Δ' : SubCtx Γ) (e : Expr σ ⌊ Δ ⌋) (e' : Expr σ ⌊ Δ' ⌋) (env : Env ⌊ Δ ⌋) →
    (H' : Δ' ⊆ Δ) (accu : WF.Acc _<-bindings_ (Δ , e)) →
    let Δ'' , (H'' , e'') = fix-optimise-wf-helper Δ Δ' e e' H' accu
    in eval e'' (prjEnv Δ'' Δ H'' env) ≡ eval e' (prjEnv Δ' Δ H' env)
  fix-optimise-wf-helper-correct Δ Δ' e e' env H' (WF.acc g) with num-bindings e' <? num-bindings e
  ... | inj₂ p = refl
  ... | inj₁ p = let Δ'' , (H'' , e'') = fix-optimise-wf Δ' e' (g (Δ' , e') p)
                 in eval e'' (prjEnv Δ'' Δ (⊆-trans Δ'' Δ' Δ H'' H') env)
                  ≡⟨ cong (eval e'') (sym (prjEnv-trans Δ'' Δ' Δ H'' H' env)) ⟩
                    eval e'' (prjEnv Δ'' Δ' H'' (prjEnv Δ' Δ H' env))
                  ≡⟨ fix-optimise-wf-correct Δ' e' (prjEnv Δ' Δ H' env) (g (Δ' , e') p) ⟩
                    eval e' (prjEnv Δ' Δ H' env)
                  ∎

fix-optimise-correct : (Δ : SubCtx Γ) (e : Expr σ ⌊ Δ ⌋) (env : Env ⌊ Δ ⌋) →
  let Δ' , (H' , e') = fix-optimise Δ e
  in eval e' (prjEnv Δ' Δ H' env) ≡ eval e env
fix-optimise-correct Δ e env = fix-optimise-wf-correct Δ e env (<-bindings-wf (Δ , e))
