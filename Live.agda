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

data LiveExpr (Γ : Ctx) : (Δ : Subset Γ) → (σ : U) → Set where
  Val : ⟦ σ ⟧ → LiveExpr Γ ∅ σ
  Plus : ∀ {Δ₁ Δ₂} → LiveExpr Γ Δ₁ NAT → LiveExpr Γ Δ₂ NAT → LiveExpr Γ (Δ₁ ∪ Δ₂) NAT
  Eq : ∀ {Δ₁ Δ₂} → LiveExpr Γ Δ₁ NAT → LiveExpr Γ Δ₂ NAT → LiveExpr Γ (Δ₁ ∪ Δ₂) BOOL
  Let : ∀ {Δ₁ Δ₂} → (decl : LiveExpr Γ Δ₁ σ) → (body : LiveExpr (σ ∷ Γ) Δ₂ τ) → LiveExpr Γ (Δ₁ ∪ (pop Δ₂)) τ
  Var : (i : Ref σ Γ) → LiveExpr Γ [ i ] σ

-- forget the information about variable usage
forget : LiveExpr Γ Δ σ → Expr Γ σ
forget (Val x) = Val x
forget (Plus e₁ e₂) = Plus (forget e₁) (forget e₂)
forget (Eq e₁ e₂) = Eq (forget e₁) (forget e₂)
forget (Let e₁ e₂) = Let (forget e₁) (forget e₂)
forget (Var i) = Var i

-- decide which variables are used or not
analyse : Expr Γ σ → Σ[ Δ ∈ Subset Γ ] LiveExpr Γ Δ σ
analyse (Val x) = ∅ , (Val x)
analyse (Plus e₁ e₂) with analyse e₁ | analyse e₂
... | Δ₁ , le₁ | Δ₂ , le₂ = (Δ₁ ∪ Δ₂) , (Plus le₁ le₂)
analyse (Eq e₁ e₂) with analyse e₁ | analyse e₂
... | Δ₁ , le₁ | Δ₂ , le₂ = (Δ₁ ∪ Δ₂) , (Eq le₁ le₂)
analyse (Let e₁ e₂) with analyse e₁ | analyse e₂
... | Δ₁ , le₁ | Δ₂ , le₂ = (Δ₁ ∪ (pop Δ₂)) , (Let le₁ le₂)
analyse (Var x) = [ x ] , (Var x)

-- Now let's try to define a semantics for LiveExpr...
lookup-sub : (Δ : Subset Γ) (i : Ref σ Γ) → Env ⌊ Δ ⌋ → .([ i ] ⊆ Δ) → ⟦ σ ⟧
lookup-sub (Keep Δ) Top (Cons x env) p = x
lookup-sub (Keep Δ) (Pop i) (Cons x env) p = lookup-sub Δ i env p
lookup-sub (Drop Δ) (Pop i) env p = lookup-sub Δ i env p

evalLive : (Δᵤ : Subset Γ) → LiveExpr Γ Δ τ → Env ⌊ Δᵤ ⌋ → .(Δ ⊆ Δᵤ) → ⟦ τ ⟧
evalLive Δᵤ (Val x) env H = x
evalLive Δᵤ (Plus {Δ₁} {Δ₂} e₁ e₂) env H =
    evalLive Δᵤ e₁ env (⊆trans Δ₁ (Δ₁ ∪ Δ₂) Δᵤ (∪sub₁ Δ₁ Δ₂) H)
  + evalLive Δᵤ e₂ env (⊆trans Δ₂ (Δ₁ ∪ Δ₂) Δᵤ (∪sub₂ Δ₁ Δ₂) H)
evalLive Δᵤ (Eq {Δ₁} {Δ₂} e₁ e₂) env H =
     evalLive Δᵤ e₁ env (⊆trans Δ₁ (Δ₁ ∪ Δ₂) Δᵤ (∪sub₁ Δ₁ Δ₂) H)
  ≡ᵇ evalLive Δᵤ e₂ env (⊆trans Δ₂ (Δ₁ ∪ Δ₂) Δᵤ (∪sub₂ Δ₁ Δ₂) H)
evalLive {Γ} Δᵤ (Let {σ} {τ} {Δ₁} {Drop Δ₂} e₁ e₂) env H =
  evalLive {σ ∷ Γ} (Drop Δᵤ) e₂ env
    (⊆trans Δ₂ (Δ₁ ∪ Δ₂) Δᵤ (∪sub₂ Δ₁ Δ₂) H)
evalLive Δᵤ (Let {_} {_} {Δ₁} {Keep Δ₂} e₁ e₂) env H =
  evalLive (Keep Δᵤ) e₂
    (Cons (evalLive Δᵤ e₁ env (⊆trans Δ₁ (Δ₁ ∪ Δ₂) Δᵤ (∪sub₁ Δ₁ Δ₂) H)) env)
    (⊆trans Δ₂ (Δ₁ ∪ Δ₂) Δᵤ (∪sub₂ Δ₁ Δ₂) H)
evalLive Δᵤ (Var i) env H = lookup-sub Δᵤ i env H

-- forget . analyse = id
analyse-preserves : (e : Expr Γ σ) → forget (proj₂ (analyse e)) ≡ e
analyse-preserves (Val x) = refl
analyse-preserves (Plus e₁ e₂) = cong₂ Plus (analyse-preserves e₁) (analyse-preserves e₂)
analyse-preserves (Eq e₁ e₂) = cong₂ Eq (analyse-preserves e₁) (analyse-preserves e₂)
analyse-preserves (Let e₁ e₂) = cong₂ Let (analyse-preserves e₁) (analyse-preserves e₂)
analyse-preserves (Var x) = refl

-- evalLive = eval . forget
evalLive-correct : (e : LiveExpr Γ Δ σ) (Δᵤ : Subset Γ) (env : Env Γ) → .(H : Δ ⊆ Δᵤ) →
  evalLive Δᵤ e (prjEnv Δᵤ env) H ≡ eval (forget e) env
evalLive-correct (Val x) Δᵤ env H = refl
evalLive-correct (Plus {Δ₁} {Δ₂} e₁ e₂) Δᵤ env H =
  cong₂ _+_
    (evalLive-correct e₁ Δᵤ env (⊆trans Δ₁ (Δ₁ ∪ Δ₂) Δᵤ (∪sub₁ Δ₁ Δ₂) H))
    (evalLive-correct e₂ Δᵤ env ( ⊆trans Δ₂ (Δ₁ ∪ Δ₂) Δᵤ (∪sub₂ Δ₁ Δ₂) H))
evalLive-correct (Eq {Δ₁} {Δ₂} e₁ e₂) Δᵤ env H =
  cong₂ _≡ᵇ_
    (evalLive-correct e₁ Δᵤ env (⊆trans Δ₁ (Δ₁ ∪ Δ₂) Δᵤ (∪sub₁ Δ₁ Δ₂) H))
    (evalLive-correct e₂ Δᵤ env ( ⊆trans Δ₂ (Δ₁ ∪ Δ₂) Δᵤ (∪sub₂ Δ₁ Δ₂) H))
evalLive-correct (Let {Δ₁ = Δ₁} {Δ₂ = Drop Δ₂} e₁ e₂) Δᵤ env H =
  evalLive-correct e₂ (Drop Δᵤ) (Cons (eval (forget e₁) env) env) _
evalLive-correct (Let {Δ₁ = Δ₁} {Δ₂ = Keep Δ₂} e₁ e₂) Δᵤ env H =
    evalLive (Keep Δᵤ) e₂ (Cons (evalLive Δᵤ e₁ (prjEnv Δᵤ env) _) (prjEnv Δᵤ env)) _
  ≡⟨ evalLive-correct e₂ (Keep Δᵤ) (Cons (evalLive Δᵤ e₁ (prjEnv Δᵤ env) _) env) _ ⟩
    eval (forget e₂) (Cons (evalLive Δᵤ e₁ (prjEnv Δᵤ env) _) env)
  ≡⟨ cong (λ x → eval (forget e₂) (Cons x env)) (evalLive-correct e₁ Δᵤ env _) ⟩
    eval (forget e₂) (Cons (eval (forget e₁) env) env)
  ∎
evalLive-correct (Var i) Δᵤ env H = lookup-sub-correct i Δᵤ env H
  where
    lookup-sub-correct : (i : Ref σ Γ) (Δᵤ : Subset Γ) (env : Env Γ) → .(H : [ i ] ⊆ Δᵤ) →
      lookup-sub Δᵤ i (prjEnv Δᵤ env) H ≡ lookup i env
    lookup-sub-correct Top (Keep Δᵤ) (Cons x env) H = refl
    lookup-sub-correct (Pop i) (Drop Δᵤ) (Cons x env) H = lookup-sub-correct i Δᵤ env H
    lookup-sub-correct (Pop i) (Keep Δᵤ) (Cons x env) H = lookup-sub-correct i Δᵤ env H

-- dead binding elimination
dbe : LiveExpr Γ Δ σ → Expr ⌊ Δ ⌋ σ
dbe (Val x) = Val x
dbe (Plus {Δ₁} {Δ₂} e₁ e₂) = Plus (injExpr₁ Δ₁ Δ₂ (dbe e₁)) (injExpr₂ Δ₁ Δ₂ (dbe e₂))
dbe (Eq {Δ₁} {Δ₂} e₁ e₂) = Eq ((injExpr₁ Δ₁ Δ₂ (dbe e₁))) ((injExpr₂ Δ₁ Δ₂ (dbe e₂)))
dbe (Let {Δ₁ = Δ₁} {Δ₂ = Drop Δ₂} e₁ e₂) = injExpr₂ Δ₁ Δ₂ (dbe e₂)
dbe (Let {Δ₁ = Δ₁} {Δ₂ = Keep Δ₂} e₁ e₂) =
  Let
    (injExpr₁ Δ₁ Δ₂ (dbe e₁))
    (renameExpr (Keep Δ₂) (Keep (Δ₁ ∪ Δ₂)) (∪sub₂ Δ₁ Δ₂) (dbe e₂))
dbe (Var i) = Var (restrictedRef i)

-- eval . dbe ≡ evalLive
dbe-correct : (e : LiveExpr Γ Δ σ) (Δᵤ : Subset Γ) → .(H : Δ ⊆ Δᵤ) → (env : Env ⌊ Δᵤ ⌋) →
   eval (renameExpr Δ Δᵤ H (dbe e)) env ≡ evalLive Δᵤ e env H
dbe-correct (Val x) Δᵤ H env = refl
dbe-correct (Plus {Δ₁} {Δ₂} e₁ e₂) Δᵤ H env
  rewrite renameExpr-trans Δ₁ (Δ₁ ∪ Δ₂) Δᵤ (∪sub₁ Δ₁ Δ₂) H (dbe e₁)
  rewrite renameExpr-trans Δ₂ (Δ₁ ∪ Δ₂) Δᵤ (∪sub₂ Δ₁ Δ₂) H (dbe e₂) =
  cong₂ _+_
    (dbe-correct e₁ Δᵤ _ env)
    (dbe-correct e₂ Δᵤ _ env)
dbe-correct (Eq {Δ₁} {Δ₂} e₁ e₂) Δᵤ H env
  rewrite renameExpr-trans Δ₁ (Δ₁ ∪ Δ₂) Δᵤ (∪sub₁ Δ₁ Δ₂) H (dbe e₁)
  rewrite renameExpr-trans Δ₂ (Δ₁ ∪ Δ₂) Δᵤ (∪sub₂ Δ₁ Δ₂) H (dbe e₂) =
  cong₂ _≡ᵇ_
    (dbe-correct e₁ Δᵤ _ env)
    (dbe-correct e₂ Δᵤ _ env)
dbe-correct {Γ} (Let {σ} {τ} {Δ₁} {Drop Δ₂} e₁ e₂) Δᵤ H env =
    eval (renameExpr (Δ₁ ∪ Δ₂) Δᵤ _ (injExpr₂ Δ₁ Δ₂ (dbe e₂))) env
  ≡⟨ cong (λ e → eval e env) (renameExpr-trans Δ₂ (Δ₁ ∪ Δ₂) Δᵤ (∪sub₂ Δ₁ Δ₂) H (dbe e₂)) ⟩
    eval (renameExpr Δ₂ Δᵤ _ (dbe e₂)) env
  ≡⟨ renameExpr-preserves Δ₂ Δᵤ _ (dbe e₂) env ⟩
    eval (dbe e₂) (prjEnv' Δ₂ Δᵤ _ env)
  ≡⟨ sym (renameExpr-preserves (Drop Δ₂) (Drop Δᵤ) _ (dbe e₂) env) ⟩
    eval (renameExpr (Drop Δ₂) (Drop Δᵤ) _ (dbe e₂)) env
  ≡⟨ dbe-correct {σ ∷ Γ} {Drop Δ₂} e₂ (Drop Δᵤ) _ env ⟩
    evalLive (Drop Δᵤ) e₂ env _
  ∎
dbe-correct (Let {_} {_} {Δ₁} {Keep Δ₂} e₁ e₂) Δᵤ H env =
    eval
      (renameExpr (Keep (Δ₁ ∪ Δ₂)) (Keep Δᵤ) _ (renameExpr (Keep Δ₂) (Keep (Δ₁ ∪ Δ₂)) _ (dbe e₂)))
      (Cons (eval (renameExpr (Δ₁ ∪ Δ₂) Δᵤ _ (injExpr₁ Δ₁ Δ₂ (dbe e₁))) env) env)
  ≡⟨ cong (λ e → eval e _)
      (renameExpr-trans (Keep Δ₂) (Keep (Δ₁ ∪ Δ₂)) (Keep Δᵤ) (∪sub₂ Δ₁ Δ₂) H (dbe e₂)) ⟩
    eval
      (renameExpr (Keep Δ₂) (Keep Δᵤ) _ (dbe e₂))
      (Cons (eval (renameExpr (Δ₁ ∪ Δ₂) Δᵤ _ (injExpr₁ Δ₁ Δ₂ (dbe e₁))) env) env)
  ≡⟨ cong (λ e → eval (renameExpr (Keep Δ₂) (Keep Δᵤ) (⊆trans Δ₂ (Δ₁ ∪ Δ₂) Δᵤ (∪sub₂ Δ₁ Δ₂) H) (dbe e₂)) (Cons (eval e env) env))
      (renameExpr-trans Δ₁ (Δ₁ ∪ Δ₂) Δᵤ (∪sub₁ Δ₁ Δ₂) H (dbe e₁)) ⟩
    eval
      (renameExpr (Keep Δ₂) (Keep Δᵤ) _ (dbe e₂))
      (Cons (eval (renameExpr Δ₁ Δᵤ _ (dbe e₁)) env) env)
  ≡⟨ cong (λ x → eval (renameExpr (Keep Δ₂) (Keep Δᵤ) (⊆trans Δ₂ (Δ₁ ∪ Δ₂) Δᵤ (∪sub₂ Δ₁ Δ₂) H) (dbe e₂)) (Cons x env))
      (dbe-correct e₁ Δᵤ _ env) ⟩
    eval
      (renameExpr (Keep Δ₂) (Keep Δᵤ) _ (dbe e₂))
      (Cons (evalLive Δᵤ e₁ env _) env)
  ≡⟨ dbe-correct e₂ (Keep Δᵤ) _ (Cons (evalLive Δᵤ e₁ env _) env) ⟩
    evalLive (Keep Δᵤ) e₂ (Cons (evalLive Δᵤ e₁ env _) env) _
  ∎
dbe-correct (Var i) Δᵤ H env = lemma-lookup-sub i Δᵤ H env
  where
    lemma-lookup-sub : (i : Ref σ Γ) (Δᵤ : Subset Γ) → .(H : [ i ] ⊆ Δᵤ) → (env : Env ⌊ Δᵤ ⌋) →
      lookup (renameVar [ i ] Δᵤ H (restrictedRef i)) env ≡ lookup-sub Δᵤ i env H
    lemma-lookup-sub Top (Keep Δᵤ) H (Cons x env) = refl
    lemma-lookup-sub (Pop i) (Drop Δᵤ) H env = lemma-lookup-sub i Δᵤ H env
    lemma-lookup-sub (Pop i) (Keep Δᵤ) H (Cons x env) = lemma-lookup-sub i Δᵤ H env

optimize : Expr Γ σ → Σ[ Δ ∈ Subset Γ ] Expr ⌊ Δ ⌋ σ
optimize e with analyse e
... | Δ , e' = Δ , dbe e'

optimize-correct : (e : Expr Γ σ) (env : Env Γ) →
  let Δ , e' = optimize e
  in eval e' (prjEnv Δ env) ≡ eval e env
optimize-correct {Γ} e env =
  let Δ , le = analyse e
  in
    eval (dbe le) (prjEnv Δ env)
  ≡⟨ cong (λ e → eval e (prjEnv Δ env)) (sym (renameExpr-id Δ (dbe le))) ⟩
    eval (renameExpr Δ Δ (⊆refl Δ) (dbe le)) (prjEnv Δ env)
  ≡⟨ dbe-correct le Δ (⊆refl Δ) (prjEnv Δ env) ⟩  -- eval . dbe ≡ evalLive
    evalLive Δ le (prjEnv Δ env) (⊆refl Δ)
  ≡⟨ evalLive-correct le Δ env (⊆refl Δ) ⟩  -- evalLive ≡ eval . forget
    eval (forget le) env
  ≡⟨ cong (λ e →  eval e env) (analyse-preserves e) ⟩  -- forget . analyse ≡ id
    eval e env
  ∎

fix-optimize-wf : (e : Expr [] σ) → WF.Acc _<-bindings_ e → Expr [] σ
fix-optimize-wf e (WF.acc g) with analyse e 
... | Empty , le with num-bindings (dbe le) <? num-bindings e
...                 | inj₁ p = fix-optimize-wf (dbe le) (g (dbe le) p)
...                 | inj₂ p = dbe le

fix-optimize : Expr [] σ → Expr [] σ
fix-optimize e = fix-optimize-wf e (<-bindings-wf e)
