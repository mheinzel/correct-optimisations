\begin{code}[hide]
-- Live variable analysis
module Live where

open import Data.Nat using (_+_)
open import Data.List using (List ; _∷_ ; [])
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; trans ; cong ; cong₂ ; sym)
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import Lang
open import Subset
open import Recursion
\end{code}

\newcommand{\CodeLiveExpr}{%
\begin{code}
-- TODO: bind implicit variables explicitly in an order that makes pattern matching on them nicer?
-- IDEA: in Let, add explicit KeepBinding/RemBinding field to match on instead of Δ₂?
data LiveExpr {Γ : Ctx} : (Δ Δ' : Subset Γ) → (σ : U) → Set where
  Val : ⟦ σ ⟧ → LiveExpr Δ ∅ σ
  Plus : LiveExpr Δ Δ₁ NAT → LiveExpr Δ Δ₂ NAT → LiveExpr Δ (Δ₁ ∪ Δ₂) NAT
  Let : LiveExpr Δ Δ₁ σ → LiveExpr {σ ∷ Γ} (Keep Δ) Δ₂ τ → LiveExpr Δ (Δ₁ ∪ pop Δ₂) τ
  Var : (x : Ref σ ⌊ Δ ⌋) → LiveExpr Δ (Δ [ x ]) σ
\end{code}}

\begin{code}[hide]
-- forget the information about variable usage
forget : LiveExpr Δ Δ' σ → Expr ⌊ Δ ⌋ σ
forget (Val v) = Val v
forget (Plus e₁ e₂) = Plus (forget e₁) (forget e₂)
forget (Let e₁ e₂) = Let (forget e₁) (forget e₂)
forget (Var x) = Var x

-- decide which variables are used or not
analyse : (Δ : Subset Γ) → Expr ⌊ Δ ⌋ σ → Σ[ Δ' ∈ Subset Γ ] LiveExpr Δ Δ' σ
analyse {Γ} Δ (Val v) = ∅ , Val v
analyse {Γ} Δ (Plus e₁ e₂) with analyse Δ e₁ | analyse Δ e₂
... | Δ₁ , le₁ | Δ₂ , le₂ = (Δ₁ ∪ Δ₂) , Plus le₁ le₂
analyse {Γ} Δ (Let e₁ e₂) with analyse Δ e₁ | analyse (Keep Δ) e₂
... | Δ₁ , le₁ | Δ₂ , le₂ = (Δ₁ ∪ pop Δ₂) , Let le₁ le₂
analyse {Γ} Δ (Var x) = (Δ [ x ]) , Var x

Δ'⊆Δ : LiveExpr Δ Δ' σ → Δ' ⊆ Δ
Δ'⊆Δ {Γ} {Δ} (Val v) = ∅⊆ Γ Δ
Δ'⊆Δ {Γ} {Δ} (Plus {Δ₁ = Δ₁} {Δ₂ = Δ₂} e₁ e₂) = ∪⊆ Γ Δ₁ Δ₂ Δ (Δ'⊆Δ e₁) (Δ'⊆Δ e₂)
Δ'⊆Δ {Γ} {Δ} (Let {Δ₁ = Δ₁} {Δ₂ = Δ₂} e₁ e₂) = ∪⊆ Γ Δ₁ (pop Δ₂) Δ (Δ'⊆Δ e₁) (Δ'⊆Δ e₂)
Δ'⊆Δ {Γ} {Δ} (Var x) = [x]⊆ Γ Δ x

-- forget . analyse = id
analyse-preserves : (e : Expr ⌊ Δ ⌋ σ) → forget (proj₂ (analyse Δ e)) ≡ e
analyse-preserves (Val v) = refl
analyse-preserves (Plus e₁ e₂) = cong₂ Plus (analyse-preserves e₁) (analyse-preserves e₂)
analyse-preserves (Let e₁ e₂) = cong₂ Let (analyse-preserves e₁) (analyse-preserves e₂)
analyse-preserves (Var x) = refl

-- Now let's try to define a semantics for LiveExpr...
lookupLive : (Δ Δᵤ : Subset Γ) (x : Ref σ ⌊ Δ ⌋) → Env ⌊ Δᵤ ⌋ → .((Δ [ x ]) ⊆ Δᵤ) → ⟦ σ ⟧
lookupLive {[]} Empty Δᵤ () env H
lookupLive {τ ∷ Γ} (Drop Δ) (Drop Δᵤ) x env H = lookupLive Δ Δᵤ x env H
lookupLive {τ ∷ Γ} (Drop Δ) (Keep Δᵤ) x (Cons v env) H = lookupLive Δ Δᵤ x env H
lookupLive {τ ∷ Γ} (Keep Δ) (Drop Δᵤ) (Pop x) env H = lookupLive Δ Δᵤ x env H
lookupLive {τ ∷ Γ} (Keep Δ) (Keep Δᵤ) Top (Cons v env) H = v
lookupLive {τ ∷ Γ} (Keep Δ) (Keep Δᵤ) (Pop x) (Cons v env) H = lookupLive Δ Δᵤ x env H

evalLive : (Δᵤ : Subset Γ) → LiveExpr Δ Δ' τ → Env ⌊ Δᵤ ⌋ → .(Δ' ⊆ Δᵤ) → ⟦ τ ⟧
evalLive Δᵤ (Val v) env H = v
evalLive Δᵤ (Plus {Δ} {Δ₁} {Δ₂} e₁ e₂) env H =
    evalLive Δᵤ e₁ env (⊆-trans Δ₁ (Δ₁ ∪ Δ₂) Δᵤ (⊆∪₁ Δ₁ Δ₂) H)
  + evalLive Δᵤ e₂ env (⊆-trans Δ₂ (Δ₁ ∪ Δ₂) Δᵤ (⊆∪₂ Δ₁ Δ₂) H)
evalLive Δᵤ (Let {Δ = Δ} {Δ₁ = Δ₁} {Δ₂ = Drop Δ₂} e₁ e₂) env H =
  evalLive (Drop Δᵤ) e₂ env (⊆-trans Δ₂ (Δ₁ ∪ Δ₂) Δᵤ (⊆∪₂ Δ₁ Δ₂) H)
evalLive Δᵤ (Let {Δ = Δ} {Δ₁ = Δ₁} {Δ₂ = Keep Δ₂} e₁ e₂) env H =
  evalLive (Keep Δᵤ) e₂
    (Cons (evalLive Δᵤ e₁ env (⊆-trans Δ₁ (Δ₁ ∪ Δ₂) Δᵤ (⊆∪₁ Δ₁ Δ₂) H)) env)
    (⊆-trans Δ₂ (Δ₁ ∪ Δ₂) Δᵤ (⊆∪₂ Δ₁ Δ₂) H)
evalLive {Γ} {Δ} Δᵤ (Var x) env H = lookupLive Δ Δᵤ x env H

lookupLive-correct : (x : Ref σ ⌊ Δ ⌋) (Δᵤ : Subset Γ) (env : Env ⌊ Δ ⌋) → .(H' : (Δ [ x ]) ⊆ Δᵤ) → .(H : Δᵤ ⊆ Δ) →
  lookupLive Δ Δᵤ x (prjEnv Δᵤ Δ H env) H' ≡ lookup x env
lookupLive-correct {σ} {[]} {Empty} () Δᵤ Nil H' H
lookupLive-correct {σ} {τ ∷ Γ} {Drop Δ} x (Drop Δᵤ) env H' H = lookupLive-correct x Δᵤ env H' H
lookupLive-correct {.τ} {τ ∷ Γ} {Keep Δ} Top (Keep Δᵤ) (Cons v env) H' H = refl
lookupLive-correct {σ} {τ ∷ Γ} {Keep Δ} (Pop x) (Drop Δᵤ) (Cons v env) H' H = lookupLive-correct x Δᵤ env H' H
lookupLive-correct {σ} {τ ∷ Γ} {Keep Δ} (Pop x) (Keep Δᵤ) (Cons v env) H' H = lookupLive-correct x Δᵤ env H' H

-- evalLive = eval . forget
evalLive-correct : (e : LiveExpr Δ Δ' σ) (Δᵤ : Subset Γ) (env : Env ⌊ Δ ⌋) → .(H' : Δ' ⊆ Δᵤ) → .(H : Δᵤ ⊆ Δ) →
  evalLive Δᵤ e (prjEnv Δᵤ Δ H env) H' ≡ eval (forget e) env
evalLive-correct (Val v) Δᵤ env H' H = refl
evalLive-correct (Plus {Δ} {Δ₁} {Δ₂} e₁ e₂) Δᵤ env H' H =
  cong₂ _+_
    (evalLive-correct e₁ Δᵤ env (⊆-trans Δ₁ (Δ₁ ∪ Δ₂) Δᵤ (⊆∪₁ Δ₁ Δ₂) H') H)
    (evalLive-correct e₂ Δᵤ env (⊆-trans Δ₂ (Δ₁ ∪ Δ₂) Δᵤ (⊆∪₂ Δ₁ Δ₂) H') H)
evalLive-correct (Let {Δ₁ = Δ₁} {Δ₂ = Drop Δ₂} e₁ e₂) Δᵤ env H' H =
  evalLive-correct e₂ (Drop Δᵤ) (Cons (eval (forget e₁) env) env) (⊆-trans Δ₂ (Δ₁ ∪ Δ₂) Δᵤ (⊆∪₂ Δ₁ Δ₂) H') H
evalLive-correct (Let {Δ = Δ} {Δ₁ = Δ₁} {Δ₂ = Keep Δ₂} e₁ e₂) Δᵤ env H' H =
    evalLive (Keep Δᵤ) e₂ (Cons (evalLive Δᵤ e₁ (prjEnv Δᵤ Δ H env) _) (prjEnv Δᵤ Δ H env)) _
  ≡⟨ evalLive-correct e₂ (Keep Δᵤ) (Cons (evalLive Δᵤ e₁ (prjEnv Δᵤ Δ H env) _) env) _ _ ⟩
    eval (forget e₂) (Cons (evalLive Δᵤ e₁ (prjEnv Δᵤ Δ H env) _) env)
  ≡⟨ cong (λ v → eval (forget e₂) (Cons v env)) (evalLive-correct e₁ Δᵤ env _ _) ⟩
    eval (forget e₂) (Cons (eval (forget e₁) env) env)
  ∎
evalLive-correct (Var x) Δᵤ env H' H =
  lookupLive-correct x Δᵤ env H' H

-- dead binding elimination
restrictedRef : (Δ : Subset Γ) (x : Ref σ ⌊ Δ ⌋) → Ref σ ⌊ Δ [ x ] ⌋
restrictedRef {[]} Empty ()
restrictedRef {τ ∷ Γ} (Drop Δ) x = restrictedRef Δ x
restrictedRef {τ ∷ Γ} (Keep Δ) Top = Top
restrictedRef {τ ∷ Γ} (Keep Δ) (Pop x) = restrictedRef Δ x

dbe : LiveExpr Δ Δ' σ → Expr ⌊ Δ' ⌋ σ
dbe (Val v) = Val v
dbe (Plus {Δ} {Δ₁} {Δ₂} e₁ e₂) = Plus (injExpr₁ Δ₁ Δ₂ (dbe e₁)) (injExpr₂ Δ₁ Δ₂ (dbe e₂))
dbe (Let {Δ₁ = Δ₁} {Δ₂ = Drop Δ₂} e₁ e₂) = injExpr₂ Δ₁ Δ₂ (dbe e₂)
dbe (Let {Δ₁ = Δ₁} {Δ₂ = Keep Δ₂} e₁ e₂) =
  Let
    (injExpr₁ Δ₁ Δ₂ (dbe e₁))
    (renameExpr (Keep Δ₂) (Keep (Δ₁ ∪ Δ₂)) (⊆∪₂ Δ₁ Δ₂) (dbe e₂))
dbe {Γ} {Δ} (Var x) = Var (restrictedRef Δ x)

-- eval . dbe ≡ evalLive
dbe-correct : (e : LiveExpr Δ Δ' σ) (Δᵤ : Subset Γ) → .(H : Δ' ⊆ Δᵤ) → (env : Env ⌊ Δᵤ ⌋) →
  eval (renameExpr Δ' Δᵤ H (dbe e)) env ≡ evalLive Δᵤ e env H
dbe-correct (Val v) Δᵤ H env = refl
dbe-correct (Plus {Δ} {Δ₁} {Δ₂} e₁ e₂) Δᵤ H env
  rewrite renameExpr-trans Δ₁ (Δ₁ ∪ Δ₂) Δᵤ (⊆∪₁ Δ₁ Δ₂) H (dbe e₁)
  rewrite renameExpr-trans Δ₂ (Δ₁ ∪ Δ₂) Δᵤ (⊆∪₂ Δ₁ Δ₂) H (dbe e₂) =
  cong₂ _+_
    (dbe-correct e₁ Δᵤ _ env)
    (dbe-correct e₂ Δᵤ _ env)
dbe-correct (Let {Δ = Δ} {Δ₁ = Δ₁} {Δ₂ = Drop Δ₂} e₁ e₂) Δᵤ H env =
    eval (renameExpr (Δ₁ ∪ Δ₂) Δᵤ _ (injExpr₂ Δ₁ Δ₂ (dbe e₂))) env
  ≡⟨ cong (λ e → eval e env) (renameExpr-trans Δ₂ (Δ₁ ∪ Δ₂) Δᵤ (⊆∪₂ Δ₁ Δ₂) H (dbe e₂)) ⟩
    eval (renameExpr Δ₂ Δᵤ _ (dbe e₂)) env
  ≡⟨ renameExpr-preserves Δ₂ Δᵤ _ (dbe e₂) env ⟩
    eval (dbe e₂) (prjEnv Δ₂ Δᵤ _ env)
  ≡⟨ sym (renameExpr-preserves (Drop Δ₂) (Drop Δᵤ) _ (dbe e₂) env) ⟩
    eval (renameExpr (Drop Δ₂) (Drop Δᵤ) _ (dbe e₂)) env
  ≡⟨ dbe-correct e₂ (Drop Δᵤ) _ env ⟩
    evalLive (Drop Δᵤ) e₂ env _
  ∎
dbe-correct (Let {Δ₁ = Δ₁} {Δ₂ = Keep Δ₂} e₁ e₂) Δᵤ H env =
    eval
      (renameExpr (Keep (Δ₁ ∪ Δ₂)) (Keep Δᵤ) _ (renameExpr (Keep Δ₂) (Keep (Δ₁ ∪ Δ₂)) _ (dbe e₂)))
      (Cons (eval (renameExpr (Δ₁ ∪ Δ₂) Δᵤ _ (injExpr₁ Δ₁ Δ₂ (dbe e₁))) env) env)
  ≡⟨ cong (λ e → eval e _)
      (renameExpr-trans (Keep Δ₂) (Keep (Δ₁ ∪ Δ₂)) (Keep Δᵤ) (⊆∪₂ Δ₁ Δ₂) H (dbe e₂)) ⟩
    eval
      (renameExpr (Keep Δ₂) (Keep Δᵤ) _ (dbe e₂))
      (Cons (eval (renameExpr (Δ₁ ∪ Δ₂) Δᵤ _ (injExpr₁ Δ₁ Δ₂ (dbe e₁))) env) env)
  ≡⟨ cong (λ e → eval (renameExpr (Keep Δ₂) (Keep Δᵤ) (⊆-trans Δ₂ (Δ₁ ∪ Δ₂) Δᵤ (⊆∪₂ Δ₁ Δ₂) H) (dbe e₂)) (Cons (eval e env) env))
      (renameExpr-trans Δ₁ (Δ₁ ∪ Δ₂) Δᵤ (⊆∪₁ Δ₁ Δ₂) H (dbe e₁)) ⟩
    eval
      (renameExpr (Keep Δ₂) (Keep Δᵤ) _ (dbe e₂))
      (Cons (eval (renameExpr Δ₁ Δᵤ _ (dbe e₁)) env) env)
  ≡⟨ cong (λ v → eval (renameExpr (Keep Δ₂) (Keep Δᵤ) (⊆-trans Δ₂ (Δ₁ ∪ Δ₂) Δᵤ (⊆∪₂ Δ₁ Δ₂) H) (dbe e₂)) (Cons v env))
      (dbe-correct e₁ Δᵤ _ env) ⟩
    eval
      (renameExpr (Keep Δ₂) (Keep Δᵤ) _ (dbe e₂))
      (Cons (evalLive Δᵤ e₁ env _) env)
  ≡⟨ dbe-correct e₂ (Keep Δᵤ) _ (Cons (evalLive Δᵤ e₁ env _) env) ⟩
    evalLive (Keep Δᵤ) e₂ (Cons (evalLive Δᵤ e₁ env _) env) _
  ∎
dbe-correct (Var x) Δᵤ H env =
  lemma-lookupLive x Δᵤ H env
  where
    lemma-lookupLive : (x : Ref σ ⌊ Δ ⌋) (Δᵤ : Subset Γ) → .(H : (Δ [ x ]) ⊆ Δᵤ) → (env : Env ⌊ Δᵤ ⌋) →
      lookup (renameVar (Δ [ x ]) Δᵤ H (restrictedRef Δ x)) env ≡ lookupLive Δ Δᵤ x env H
    lemma-lookupLive {σ} {[]} {Empty} () Δᵤ H env
    lemma-lookupLive {σ} {τ ∷ Γ} {Drop Δ} x (Drop Δᵤ) H env = lemma-lookupLive x Δᵤ H env
    lemma-lookupLive {σ} {τ ∷ Γ} {Drop Δ} x (Keep Δᵤ) H (Cons v env) = lemma-lookupLive x Δᵤ H env
    lemma-lookupLive {σ} {τ ∷ Γ} {Keep Δ} (Pop x) (Drop Δᵤ) H env = lemma-lookupLive x Δᵤ H env
    lemma-lookupLive {.τ} {τ ∷ Γ} {Keep Δ} Top (Keep Δᵤ) H (Cons v env) = refl
    lemma-lookupLive {σ} {τ ∷ Γ} {Keep Δ} (Pop x) (Keep Δᵤ) H (Cons v env) = lemma-lookupLive x Δᵤ H env

optimize : (Δ : Subset Γ) → Expr ⌊ Δ ⌋ σ → Σ[ Δ' ∈ Subset Γ ] (Expr ⌊ Δ' ⌋ σ)
optimize Δ e = let Δ' , e' = analyse Δ e in Δ' , dbe e'

optimize-correct : (Δ : Subset Γ) (e : Expr ⌊ Δ ⌋ σ) (env : Env ⌊ Δ ⌋) →
  let Δ' , e' = optimize Δ e
      H = Δ'⊆Δ (proj₂ (analyse Δ e))
  in eval e' (prjEnv Δ' Δ H env) ≡ eval e env
optimize-correct {Γ} Δ e env =
  let Δ' , le = analyse Δ e
      H = Δ'⊆Δ le
  in
    eval (dbe le) (prjEnv Δ' Δ H env)
  ≡⟨ cong (λ e → eval e (prjEnv Δ' Δ H env)) (sym (renameExpr-id Δ' (dbe le))) ⟩
    eval (renameExpr Δ' Δ' (⊆-refl Δ') (dbe le)) (prjEnv Δ' Δ H env)
  ≡⟨ dbe-correct le Δ' (⊆-refl Δ') (prjEnv Δ' Δ H env) ⟩  -- eval . dbe ≡ evalLive
    evalLive Δ' le (prjEnv Δ' Δ H env) (⊆-refl Δ')
  ≡⟨ evalLive-correct le Δ' env (⊆-refl Δ') H ⟩  -- evalLive ≡ eval . forget
    eval (forget le) env
  ≡⟨ cong (λ e → eval e env) (analyse-preserves {Γ} {Δ} e) ⟩  -- forget . analyse ≡ id
    eval e env
  ∎

mutual
  -- Keep optimizing as long as the number of bindings decreases.
  -- This is not structurally recursive, but we have a Well-Foundedness proof.
  fix-optimize-wf : (Δ : Subset Γ) (e : Expr ⌊ Δ ⌋ σ) → WF.Acc _<-bindings_ (Δ , e) →
    Σ[ Δ' ∈ Subset Γ ] ((Δ' ⊆ Δ) × Expr ⌊ Δ' ⌋ σ)
  fix-optimize-wf {Γ} Δ e accu =
    let Δ' , e' = optimize Δ e
        H = Δ'⊆Δ (proj₂ (analyse Δ e))
    in fix-optimize-wf-helper Δ Δ' e e' H accu

  -- Without the helper, there were issues with the with-abstraction using a
  -- result of the let-binding.
  fix-optimize-wf-helper :
    (Δ Δ' : Subset Γ) (e : Expr ⌊ Δ ⌋ σ) (e' : Expr ⌊ Δ' ⌋ σ) →
    (H' : Δ' ⊆ Δ) → WF.Acc _<-bindings_ (Δ , e) →
    Σ[ Δ'' ∈ Subset Γ ] ((Δ'' ⊆ Δ) × Expr ⌊ Δ'' ⌋ σ)
  fix-optimize-wf-helper Δ Δ' e e' H' (WF.acc g) with num-bindings e' <? num-bindings e
  ... | inj₂ p = Δ' , (H' , e')
  ... | inj₁ p = let Δ'' , (H'' , e'') = fix-optimize-wf Δ' e' (g (Δ' , e') p)
                 in Δ'' , (⊆-trans Δ'' Δ' Δ H'' H') , e''

fix-optimize : (Δ : Subset Γ) → Expr ⌊ Δ ⌋ σ → Σ[ Δ' ∈ Subset Γ ] ((Δ' ⊆ Δ) × Expr ⌊ Δ' ⌋ σ)
fix-optimize {Γ} Δ e = fix-optimize-wf Δ e (<-bindings-wf (Δ , e))

mutual
  -- Not pretty, but it works.
  fix-optimize-wf-correct : (Δ : Subset Γ) (e : Expr ⌊ Δ ⌋ σ) (env : Env ⌊ Δ ⌋) (accu : WF.Acc _<-bindings_ (Δ , e)) →
    let Δ'' , (H'' , e'') = fix-optimize-wf Δ e accu
    in eval e'' (prjEnv Δ'' Δ H'' env) ≡ eval e env
  fix-optimize-wf-correct Δ e env accu =
    let Δ' , e' = optimize Δ e
        H' = Δ'⊆Δ (proj₂ (analyse Δ e))
        Δ'' , (H'' , e'') = fix-optimize-wf-helper Δ Δ' e e' H' accu
    in eval e'' (prjEnv Δ'' Δ H'' env)
     ≡⟨ fix-optimize-wf-helper-correct Δ Δ' e e' env H' accu ⟩
       eval e' (prjEnv Δ' Δ H' env)
     ≡⟨ optimize-correct Δ e env ⟩
       eval e env
     ∎

  fix-optimize-wf-helper-correct :
    (Δ Δ' : Subset Γ) (e : Expr ⌊ Δ ⌋ σ) (e' : Expr ⌊ Δ' ⌋ σ) (env : Env ⌊ Δ ⌋) →
    (H' : Δ' ⊆ Δ) (accu : WF.Acc _<-bindings_ (Δ , e)) →
    let Δ'' , (H'' , e'') = fix-optimize-wf-helper Δ Δ' e e' H' accu
    in eval e'' (prjEnv Δ'' Δ H'' env) ≡ eval e' (prjEnv Δ' Δ H' env)
  fix-optimize-wf-helper-correct Δ Δ' e e' env H' (WF.acc g) with num-bindings e' <? num-bindings e
  ... | inj₂ p = refl
  ... | inj₁ p = let Δ'' , (H'' , e'') = fix-optimize-wf Δ' e' (g (Δ' , e') p)
                 in eval e'' (prjEnv Δ'' Δ (⊆-trans Δ'' Δ' Δ H'' H') env)
                  ≡⟨ cong (eval e'') (sym (prjEnv-trans Δ'' Δ' Δ H'' H' env)) ⟩
                    eval e'' (prjEnv Δ'' Δ' H'' (prjEnv Δ' Δ H' env))
                  ≡⟨ fix-optimize-wf-correct Δ' e' (prjEnv Δ' Δ H' env) (g (Δ' , e') p) ⟩
                    eval e' (prjEnv Δ' Δ H' env)
                  ∎

fix-optimize-correct : (Δ : Subset Γ) (e : Expr ⌊ Δ ⌋ σ) (env : Env ⌊ Δ ⌋) →
  let Δ' , (H' , e') = fix-optimize Δ e
  in eval e' (prjEnv Δ' Δ H' env) ≡ eval e env
fix-optimize-correct Δ e env = fix-optimize-wf-correct Δ e env (<-bindings-wf (Δ , e))
\end{code}
