\begin{code}[hide]
-- Live variable analysis
module Live where

open import Data.Nat using (_+_ ; _≡ᵇ_)
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
data LiveExpr {Γ : Ctx} : (Δ Δ' : Subset Γ) → (σ : U) → Set where
  Val : ⟦ σ ⟧ → LiveExpr Δ ∅ σ
  Plus : ∀ {Δ Δ₁ Δ₂} → LiveExpr Δ Δ₁ NAT → LiveExpr Δ Δ₂ NAT → LiveExpr Δ (Δ₁ ∪ Δ₂) NAT
  Let : ∀ {Δ Δ₁ Δ₂} → (decl : LiveExpr Δ Δ₁ σ) → (body : LiveExpr {σ ∷ Γ} (Keep Δ) Δ₂ τ) → LiveExpr Δ (Δ₁ ∪ (pop Δ₂)) τ
  Var : (i : Ref σ ⌊ Δ ⌋) → LiveExpr Δ (Δ [ i ]) σ
\end{code}}

\begin{code}[hide]
-- forget the information about variable usage
forget : LiveExpr Δ Δ' σ → Expr ⌊ Δ ⌋ σ
forget (Val x) = Val x
forget (Plus e₁ e₂) = Plus (forget e₁) (forget e₂)
forget (Let e₁ e₂) = Let (forget e₁) (forget e₂)
forget (Var i) = Var i

-- decide which variables are used or not
analyse : (Δ : Subset Γ) → Expr ⌊ Δ ⌋ σ → Σ[ Δ' ∈ Subset Γ ] ((Δ' ⊆ Δ) × LiveExpr Δ Δ' σ)
analyse {Γ} Δ (Val x) = ∅ , (∅⊆ Γ Δ , Val x)
analyse {Γ} Δ (Plus e₁ e₂) with analyse Δ e₁ | analyse Δ e₂
... | Δ₁ , (H₁ , le₁) | Δ₂ , (H₂ , le₂) = (Δ₁ ∪ Δ₂) , (∪⊆ Γ Δ₁ Δ₂ Δ H₁ H₂ , Plus le₁ le₂)
analyse {Γ} Δ (Let e₁ e₂) with analyse Δ e₁ | analyse (Keep Δ) e₂
... | Δ₁ , (H₁ , le₁) | Δ₂ , (H₂ , le₂) = (Δ₁ ∪ (pop Δ₂)) , (∪⊆ Γ Δ₁ (pop Δ₂) Δ H₁ H₂ , Let le₁ le₂)
analyse {Γ} Δ (Var i) = (Δ [ i ]) , ([i]⊆ Γ Δ i , Var i)

-- forget . analyse = id
analyse-preserves : (e : Expr ⌊ Δ ⌋ σ) → forget (proj₂ (proj₂ (analyse Δ e))) ≡ e
analyse-preserves (Val x) = refl
analyse-preserves (Plus e₁ e₂) = cong₂ Plus (analyse-preserves e₁) (analyse-preserves e₂)
analyse-preserves (Let e₁ e₂) = cong₂ Let (analyse-preserves e₁) (analyse-preserves e₂)
analyse-preserves (Var i) = refl

-- Now let's try to define a semantics for LiveExpr...
lookupLive : (Δ Δᵤ : Subset Γ) (i : Ref σ ⌊ Δ ⌋) → Env ⌊ Δᵤ ⌋ → .((Δ [ i ]) ⊆ Δᵤ) → ⟦ σ ⟧
lookupLive {[]} Empty Δᵤ () env H
lookupLive {τ ∷ Γ} (Drop Δ) (Drop Δᵤ) i env H = lookupLive Δ Δᵤ i env H
lookupLive {τ ∷ Γ} (Drop Δ) (Keep Δᵤ) i (Cons x env) H = lookupLive Δ Δᵤ i env H
lookupLive {τ ∷ Γ} (Keep Δ) (Drop Δᵤ) (Pop i) env H = lookupLive Δ Δᵤ i env H
lookupLive {τ ∷ Γ} (Keep Δ) (Keep Δᵤ) Top (Cons x env) H = x
lookupLive {τ ∷ Γ} (Keep Δ) (Keep Δᵤ) (Pop i) (Cons x env) H = lookupLive Δ Δᵤ i env H

evalLive : (Δᵤ : Subset Γ) → LiveExpr Δ Δ' τ → Env ⌊ Δᵤ ⌋ → .(Δ' ⊆ Δᵤ) → ⟦ τ ⟧
evalLive Δᵤ (Val x) env H = x
evalLive Δᵤ (Plus {Δ} {Δ₁} {Δ₂} e₁ e₂) env H =
    evalLive Δᵤ e₁ env (⊆-trans Δ₁ (Δ₁ ∪ Δ₂) Δᵤ (⊆∪₁ Δ₁ Δ₂) H)
  + evalLive Δᵤ e₂ env (⊆-trans Δ₂ (Δ₁ ∪ Δ₂) Δᵤ (⊆∪₂ Δ₁ Δ₂) H)
evalLive Δᵤ (Let {σ} {τ} {Δ} {Δ₁} {Drop Δ₂} e₁ e₂) env H =
  evalLive (Drop Δᵤ) e₂ env (⊆-trans Δ₂ (Δ₁ ∪ Δ₂) Δᵤ (⊆∪₂ Δ₁ Δ₂) H)
evalLive Δᵤ (Let {_} {_} {Δ} {Δ₁} {Keep Δ₂} e₁ e₂) env H =
  evalLive (Keep Δᵤ) e₂
    (Cons (evalLive Δᵤ e₁ env (⊆-trans Δ₁ (Δ₁ ∪ Δ₂) Δᵤ (⊆∪₁ Δ₁ Δ₂) H)) env)
    (⊆-trans Δ₂ (Δ₁ ∪ Δ₂) Δᵤ (⊆∪₂ Δ₁ Δ₂) H)
evalLive {Γ} {Δ} Δᵤ (Var i) env H = lookupLive Δ Δᵤ i env H

lookupLive-correct : (i : Ref σ ⌊ Δ ⌋) (Δᵤ : Subset Γ) (env : Env ⌊ Δ ⌋) → .(H' : (Δ [ i ]) ⊆ Δᵤ) → .(H : Δᵤ ⊆ Δ) →
  lookupLive Δ Δᵤ i (prjEnv Δᵤ Δ H env) H' ≡ lookup i env
lookupLive-correct {σ} {[]} {Empty} () Δᵤ Nil H' H
lookupLive-correct {σ} {τ ∷ Γ} {Drop Δ} i (Drop Δᵤ) env H' H = lookupLive-correct i Δᵤ env H' H
lookupLive-correct {.τ} {τ ∷ Γ} {Keep Δ} Top (Keep Δᵤ) (Cons x env) H' H = refl
lookupLive-correct {σ} {τ ∷ Γ} {Keep Δ} (Pop i) (Drop Δᵤ) (Cons x env) H' H = lookupLive-correct i Δᵤ env H' H
lookupLive-correct {σ} {τ ∷ Γ} {Keep Δ} (Pop i) (Keep Δᵤ) (Cons x env) H' H = lookupLive-correct i Δᵤ env H' H

-- evalLive = eval . forget
evalLive-correct : (e : LiveExpr Δ Δ' σ) (Δᵤ : Subset Γ) (env : Env ⌊ Δ ⌋) → .(H' : Δ' ⊆ Δᵤ) → .(H : Δᵤ ⊆ Δ) →
  evalLive Δᵤ e (prjEnv Δᵤ Δ H env) H' ≡ eval (forget e) env
evalLive-correct (Val x) Δᵤ env H' H = refl
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
  ≡⟨ cong (λ x → eval (forget e₂) (Cons x env)) (evalLive-correct e₁ Δᵤ env _ _) ⟩
    eval (forget e₂) (Cons (eval (forget e₁) env) env)
  ∎
evalLive-correct (Var i) Δᵤ env H' H =
  lookupLive-correct i Δᵤ env H' H

-- dead binding elimination
restrictedRef : (Δ : Subset Γ) (i : Ref σ ⌊ Δ ⌋) → Ref σ ⌊ Δ [ i ] ⌋
restrictedRef {[]} Empty ()
restrictedRef {τ ∷ Γ} (Drop Δ) i = restrictedRef Δ i
restrictedRef {τ ∷ Γ} (Keep Δ) Top = Top
restrictedRef {τ ∷ Γ} (Keep Δ) (Pop i) = restrictedRef Δ i

dbe : LiveExpr Δ Δ' σ → Expr ⌊ Δ' ⌋ σ
dbe (Val x) = Val x
dbe (Plus {Δ} {Δ₁} {Δ₂} e₁ e₂) = Plus (injExpr₁ Δ₁ Δ₂ (dbe e₁)) (injExpr₂ Δ₁ Δ₂ (dbe e₂))
dbe (Let {Δ₁ = Δ₁} {Δ₂ = Drop Δ₂} e₁ e₂) = injExpr₂ Δ₁ Δ₂ (dbe e₂)
dbe (Let {Δ₁ = Δ₁} {Δ₂ = Keep Δ₂} e₁ e₂) =
  Let
    (injExpr₁ Δ₁ Δ₂ (dbe e₁))
    (renameExpr (Keep Δ₂) (Keep (Δ₁ ∪ Δ₂)) (⊆∪₂ Δ₁ Δ₂) (dbe e₂))
dbe {Γ} {Δ} (Var i) = Var (restrictedRef Δ i)

-- eval . dbe ≡ evalLive
dbe-correct : (e : LiveExpr Δ Δ' σ) (Δᵤ : Subset Γ) → .(H : Δ' ⊆ Δᵤ) → (env : Env ⌊ Δᵤ ⌋) →
  eval (renameExpr Δ' Δᵤ H (dbe e)) env ≡ evalLive Δᵤ e env H
dbe-correct (Val x) Δᵤ H env = refl
dbe-correct (Plus {Δ} {Δ₁} {Δ₂} e₁ e₂) Δᵤ H env
  rewrite renameExpr-trans Δ₁ (Δ₁ ∪ Δ₂) Δᵤ (⊆∪₁ Δ₁ Δ₂) H (dbe e₁)
  rewrite renameExpr-trans Δ₂ (Δ₁ ∪ Δ₂) Δᵤ (⊆∪₂ Δ₁ Δ₂) H (dbe e₂) =
  cong₂ _+_
    (dbe-correct e₁ Δᵤ _ env)
    (dbe-correct e₂ Δᵤ _ env)
dbe-correct {Γ} (Let {σ} {τ} {Δ} {Δ₁} {Drop Δ₂} e₁ e₂) Δᵤ H env =
    eval (renameExpr (Δ₁ ∪ Δ₂) Δᵤ _ (injExpr₂ Δ₁ Δ₂ (dbe e₂))) env
  ≡⟨ cong (λ e → eval e env) (renameExpr-trans Δ₂ (Δ₁ ∪ Δ₂) Δᵤ (⊆∪₂ Δ₁ Δ₂) H (dbe e₂)) ⟩
    eval (renameExpr Δ₂ Δᵤ _ (dbe e₂)) env
  ≡⟨ renameExpr-preserves Δ₂ Δᵤ _ (dbe e₂) env ⟩
    eval (dbe e₂) (prjEnv Δ₂ Δᵤ _ env)
  ≡⟨ sym (renameExpr-preserves (Drop Δ₂) (Drop Δᵤ) _ (dbe e₂) env) ⟩
    eval (renameExpr (Drop Δ₂) (Drop Δᵤ) _ (dbe e₂)) env
  ≡⟨ dbe-correct {σ ∷ Γ} {Keep Δ} {Drop Δ₂} e₂ (Drop Δᵤ) _ env ⟩
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
  ≡⟨ cong (λ x → eval (renameExpr (Keep Δ₂) (Keep Δᵤ) (⊆-trans Δ₂ (Δ₁ ∪ Δ₂) Δᵤ (⊆∪₂ Δ₁ Δ₂) H) (dbe e₂)) (Cons x env))
      (dbe-correct e₁ Δᵤ _ env) ⟩
    eval
      (renameExpr (Keep Δ₂) (Keep Δᵤ) _ (dbe e₂))
      (Cons (evalLive Δᵤ e₁ env _) env)
  ≡⟨ dbe-correct e₂ (Keep Δᵤ) _ (Cons (evalLive Δᵤ e₁ env _) env) ⟩
    evalLive (Keep Δᵤ) e₂ (Cons (evalLive Δᵤ e₁ env _) env) _
  ∎
dbe-correct (Var i) Δᵤ H env =
  lemma-lookupLive i Δᵤ H env
  where
    lemma-lookupLive : (i : Ref σ ⌊ Δ ⌋) (Δᵤ : Subset Γ) → .(H : (Δ [ i ]) ⊆ Δᵤ) → (env : Env ⌊ Δᵤ ⌋) →
      lookup (renameVar (Δ [ i ]) Δᵤ H (restrictedRef Δ i)) env ≡ lookupLive Δ Δᵤ i env H
    lemma-lookupLive {σ} {[]} {Empty} () Δᵤ H env
    lemma-lookupLive {σ} {τ ∷ Γ} {Drop Δ} i (Drop Δᵤ) H env = lemma-lookupLive i Δᵤ H env
    lemma-lookupLive {σ} {τ ∷ Γ} {Drop Δ} i (Keep Δᵤ) H (Cons x env) = lemma-lookupLive i Δᵤ H env
    lemma-lookupLive {σ} {τ ∷ Γ} {Keep Δ} (Pop i) (Drop Δᵤ) H env = lemma-lookupLive i Δᵤ H env
    lemma-lookupLive {.τ} {τ ∷ Γ} {Keep Δ} Top (Keep Δᵤ) H (Cons x env) = refl
    lemma-lookupLive {σ} {τ ∷ Γ} {Keep Δ} (Pop i) (Keep Δᵤ) H (Cons x env) = lemma-lookupLive i Δᵤ H env

optimize : (Δ : Subset Γ) → Expr ⌊ Δ ⌋ σ → Σ[ Δ' ∈ Subset Γ ] ((Δ' ⊆ Δ) × Expr ⌊ Δ' ⌋ σ)
optimize Δ e = let (Δ' , (H , e')) = analyse Δ e in Δ' , (H , dbe e')

optimize-correct : (Δ : Subset Γ) (e : Expr ⌊ Δ ⌋ σ) (env : Env ⌊ Δ ⌋) →
  let Δ' , (H , e') = optimize Δ e
  in eval e' (prjEnv Δ' Δ H env) ≡ eval e env
optimize-correct {Γ} Δ e env =
  let Δ' , (H , le) = analyse Δ e
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
    let Δ' , (H' , e') = optimize Δ e
    in fix-optimize-wf-helper Δ Δ' e e' H' accu

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
    let Δ' , (H' , e') = optimize Δ e
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
