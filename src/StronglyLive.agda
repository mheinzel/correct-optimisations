-- Strongly Live variable analysis
--
-- Based on Live.agda.
module StronglyLive where

open import Data.Nat using (_+_)
open import Data.List using (List ; _∷_ ; [])
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; trans ; cong ; cong₂ ; sym)
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import Lang
open import SubCtx
open import Recursion

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

-- dead binding elimination

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
  import Live

  -- TODO: how feasible is this?
  optimise-converges : (Δ : SubCtx Γ) (e : Expr ⌊ Δ ⌋ σ) → Live.optimise Δ e ≡ optimise Δ e
  optimise-converges Δ e = {!!}
