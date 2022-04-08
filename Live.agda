-- Live variable analysis
module Live where

open import Data.Nat using (_+_ ; _≡ᵇ_)
open import Data.Bool renaming (true to True ; false to False)
open import Data.List using (List ; _∷_ ; [])
open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; trans ; cong ; cong₂ ; sym)

open import Lang
open import Subset

data LiveExpr (Γ : Ctx) : (Δ : Subset Γ) → (σ : U) → Set where
  Val : ⟦ σ ⟧ → LiveExpr Γ ∅ σ
  Plus : ∀ {Δ₁ Δ₂} → LiveExpr Γ Δ₁ NAT → LiveExpr Γ Δ₂ NAT → LiveExpr Γ (Δ₁ ∪ Δ₂) NAT
  Eq : ∀ {Δ₁ Δ₂} → LiveExpr Γ Δ₁ NAT → LiveExpr Γ Δ₂ NAT → LiveExpr Γ (Δ₁ ∪ Δ₂) BOOL
  Let : ∀ {Δ₁ Δ₂} → (decl : LiveExpr Γ Δ₁ σ) → (body : LiveExpr (σ ∷ Γ) Δ₂ τ) → LiveExpr Γ (Δ₁ ∪ (pop Δ₂)) τ
  Var : (i : Ref σ Γ) → LiveExpr Γ [ i ] σ

-- forget the information about variable usage
forget : LiveExpr Γ Δ σ → Expr Γ σ
forget (Val x) = Val x
forget (Plus le₁ le₂) = Plus (forget le₁) (forget le₂)
forget (Eq le₁ le₂) = Eq (forget le₁) (forget le₂)
forget (Let le₁ le₂) = Let (forget le₁) (forget le₂)
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

-- TODO is this generality worthwhile? It can help avoid some of the
-- problems with composing environment projections in evalLive (and
-- the corresponding correctness proofs)
evalLive : (Δᵤ : Subset Γ) → LiveExpr Γ Δ τ → Env ⌊ Δᵤ ⌋ → .(Δ ⊆ Δᵤ) → ⟦ τ ⟧
evalLive Δᵤ (Val x) env H = x
evalLive {Γ} Δᵤ (Plus {Δ₁} {Δ₂} le₁ le₂) env H =
    evalLive Δᵤ le₁ env (⊆trans Δ₁ (Δ₁ ∪ Δ₂) Δᵤ (∪sub₁ Δ₁ Δ₂) H) 
  + evalLive Δᵤ le₂ env (⊆trans Δ₂ (Δ₁ ∪ Δ₂) Δᵤ (∪sub₂ Δ₁ Δ₂) H) 
evalLive Δᵤ (Eq {Δ₁} {Δ₂} le₁ le₂) env H =
     evalLive Δᵤ le₁ env (⊆trans Δ₁ (Δ₁ ∪ Δ₂) Δᵤ (∪sub₁ Δ₁ Δ₂) H) 
  ≡ᵇ evalLive Δᵤ le₂ env (⊆trans Δ₂ (Δ₁ ∪ Δ₂) Δᵤ (∪sub₂ Δ₁ Δ₂) H) 
evalLive {Γ} Δᵤ (Let {σ} {τ} {Δ₁} {Drop Δ₂} le₁ le₂) env H =
  evalLive {σ ∷ Γ} (Drop Δᵤ) le₂ env
    (⊆trans Δ₂ (Δ₁ ∪ Δ₂) Δᵤ (∪sub₂ Δ₁ Δ₂) H)
evalLive Δᵤ (Let {_} {_} {Δ₁} {Keep Δ₂} le₁ le₂) env H =
  evalLive (Keep Δᵤ) le₂
    (Cons (evalLive Δᵤ le₁ env (⊆trans Δ₁ (Δ₁ ∪ Δ₂) Δᵤ (∪sub₁ Δ₁ Δ₂) H)) env)
    (⊆trans Δ₂ (Δ₁ ∪ Δ₂) Δᵤ (∪sub₂ Δ₁ Δ₂) H)
evalLive Δᵤ (Var i) env H = lookup-sub Δᵤ i env H

-- forget . analyse = id
analyse-preserves : (e : Expr Γ σ) → forget (proj₂ (analyse e)) ≡ e
analyse-preserves (Val x) = refl
analyse-preserves (Plus e₁ e₂) = cong₂ Plus (analyse-preserves e₁) (analyse-preserves e₂)
analyse-preserves (Eq e₁ e₂) = cong₂ Eq (analyse-preserves e₁) (analyse-preserves e₂)
analyse-preserves (Let e₁ e₂) = cong₂ Let (analyse-preserves e₁) (analyse-preserves e₂)
analyse-preserves (Var x) = refl

-- TODO
-- evalLive = eval . forget
-- TODO: generalize (all Γ)?
evalLive-correct : (e : LiveExpr Γ Δ σ) (env : Env Γ) →
  evalLive (all Γ) e (env-of-all env) (subset-⊆ Γ Δ) ≡ eval (forget e) env
evalLive-correct (Val x) env = refl
evalLive-correct (Plus e₁ e₂) env =
  cong₂ _+_ (evalLive-correct e₁ env) (evalLive-correct e₂ env)
evalLive-correct (Eq e₁ e₂) env =
  cong₂ _≡ᵇ_ (evalLive-correct e₁ env) (evalLive-correct e₂ env)
evalLive-correct {Γ} (Let {_} {_} {Δ₁} {Drop Δ₂} e₁ e₂) env =
  let H = ?
  in
  evalLive (Drop (all Γ)) e₂ (env-of-all env) _
  ≡⟨ {!!} ⟩
  evalLive (Keep (all Γ)) e₂ (Cons (eval (forget e₁) env) (env-of-all env)) _
  ≡⟨ evalLive-correct e₂ (Cons (eval (forget e₁) env) env) ⟩
  eval (forget e₂) (Cons (eval (forget e₁) env) env)
  ∎
  where
    open Relation.Binary.PropositionalEquality.≡-Reasoning
evalLive-correct {Γ} (Let {_} {_} {Δ₁} {Keep Δ₂} e₁ e₂) env =
  evalLive (Keep (all Γ)) e₂ (Cons (evalLive (all Γ) e₁ (env-of-all env) _) (env-of-all env)) _
  ≡⟨ evalLive-correct e₂ (Cons (evalLive (all Γ) e₁ (env-of-all env) (subset-⊆ Γ Δ₁)) env) ⟩
  eval (forget e₂) (Cons (evalLive (all Γ) e₁ (env-of-all env) _) env)
  ≡⟨ cong (λ x → eval (forget e₂) (Cons x env)) (evalLive-correct e₁ env) ⟩
  eval (forget e₂) (Cons (eval (forget e₁) env) env)
  ∎
  where
    open Relation.Binary.PropositionalEquality.≡-Reasoning
evalLive-correct (Var i) env = lookup-sub-correct i env
  where
    lookup-sub-correct : (i : Ref σ Γ) (env : Env Γ) →
      lookup-sub (all Γ) i (env-of-all env) (subset-⊆ Γ [ i ]) ≡ lookup i env
    lookup-sub-correct Top (Cons x env) = refl
    lookup-sub-correct (Pop i) (Cons x env) = lookup-sub-correct i env

-- dead binding elimination
dbe : LiveExpr Γ Δ σ → Expr ⌊ Δ ⌋ σ
dbe (Val x) = Val x
dbe (Plus {Δ₁} {Δ₂} le₁ le₂) = Plus (inj₁ Δ₁ Δ₂ (dbe le₁)) (inj₂ Δ₁ Δ₂ (dbe le₂))
dbe (Eq {Δ₁} {Δ₂} le₁ le₂) = Eq ((inj₁ Δ₁ Δ₂ (dbe le₁))) ((inj₂ Δ₁ Δ₂ (dbe le₂)))
dbe (Let {Δ₁ = Δ₁} {Δ₂ = Drop Δ₂} le₁ le₂) = inj₂ Δ₁ Δ₂ (dbe le₂)
dbe (Let {Δ₁ = Δ₁} {Δ₂ = Keep Δ₂} le₁ le₂) =
  Let (inj₁ Δ₁ Δ₂ (dbe le₁)) (renameExpr (Keep Δ₂) (Keep (Δ₁ ∪ Δ₂)) (∪sub₂ Δ₁ Δ₂) (dbe le₂))
dbe (Var Top) = Var Top
dbe (Var (Pop i)) = dbe (Var i)

-- eval . dbe ≡ evalLive
dbe-correct : (e : LiveExpr Γ Δ σ) (Δᵤ : Subset Γ) → .(H : Δ ⊆ Δᵤ) → (env : Env ⌊ Δᵤ ⌋) →
   eval (renameExpr Δ Δᵤ H (dbe e)) env ≡ evalLive Δᵤ e env H
dbe-correct (Val x) Δᵤ H env = refl
dbe-correct {Γ} {Δ} (Plus {Δ₁} {Δ₂} e₁ e₂) Δᵤ H env
  rewrite renameExpr-trans Δ₁ (Δ₁ ∪ Δ₂) Δᵤ (∪sub₁ Δ₁ Δ₂) H (dbe e₁)
  rewrite renameExpr-trans Δ₂ (Δ₁ ∪ Δ₂) Δᵤ (∪sub₂ Δ₁ Δ₂) H (dbe e₂) =
  let H₁ = dbe-correct e₁ Δᵤ (⊆trans Δ₁ (Δ₁ ∪ Δ₂) Δᵤ (∪sub₁ Δ₁ Δ₂) H) env
      H₂ = dbe-correct e₂ Δᵤ (⊆trans Δ₂ (Δ₁ ∪ Δ₂) Δᵤ (∪sub₂ Δ₁ Δ₂) H) env
  in
    cong₂ _+_ H₁ H₂
dbe-correct (Eq {Δ₁} {Δ₂} e₁ e₂) Δᵤ H env
  rewrite renameExpr-trans Δ₁ (Δ₁ ∪ Δ₂) Δᵤ (∪sub₁ Δ₁ Δ₂) H (dbe e₁)
  rewrite renameExpr-trans Δ₂ (Δ₁ ∪ Δ₂) Δᵤ (∪sub₂ Δ₁ Δ₂) H (dbe e₂) =
  let H₁ = dbe-correct e₁ Δᵤ (⊆trans Δ₁ (Δ₁ ∪ Δ₂) Δᵤ (∪sub₁ Δ₁ Δ₂) H) env
      H₂ = dbe-correct e₂ Δᵤ (⊆trans Δ₂ (Δ₁ ∪ Δ₂) Δᵤ (∪sub₂ Δ₁ Δ₂) H) env
  in
    cong₂ _≡ᵇ_ H₁ H₂
dbe-correct {Γ} {Δ} (Let {σ} {τ} {Δ₁} {Drop Δ₂} e₁ e₂) Δᵤ H env =
  eval (renameExpr (Δ₁ ∪ Δ₂) Δᵤ _ (inj₂ Δ₁ Δ₂ (dbe e₂))) env
  ≡⟨ cong (λ e → eval e env) (renameExpr-trans Δ₂ (Δ₁ ∪ Δ₂) Δᵤ (∪sub₂ Δ₁ Δ₂) H (dbe e₂)) ⟩
  eval (renameExpr Δ₂ Δᵤ _ (dbe e₂)) env
  ≡⟨ renameExpr-preserves Δ₂ Δᵤ _ (dbe e₂) env ⟩
  eval (dbe e₂) (prjEnv' Δ₂ Δᵤ _ env)
  ≡⟨ sym (renameExpr-preserves (Drop Δ₂) (Drop Δᵤ) _ (dbe e₂) env) ⟩
  eval (renameExpr (Drop Δ₂) (Drop Δᵤ) _ (dbe e₂)) env
  ≡⟨ dbe-correct {σ ∷ Γ} {Drop Δ₂} e₂ (Drop Δᵤ) _ env ⟩
  evalLive (Drop Δᵤ) e₂ env _
  ∎
  where
    open Relation.Binary.PropositionalEquality.≡-Reasoning
dbe-correct {Γ} {Δ} (Let {_} {_} {Δ₁} {Keep Δ₂} e₁ e₂) Δᵤ H env =
  -- I would like to do the following, but it fails because Hₑ is irrelevant,
  -- but ⊆trans doesn't use it as an irrelevant argument.
  -- let helper = ⊆trans Δ₂ (Δ₁ ∪ Δ₂) Δ (∪sub₂ Δ₁ Δ₂) H
  eval
    (renameExpr (Keep (Δ₁ ∪ Δ₂)) (Keep Δᵤ) _ (renameExpr (Keep Δ₂) (Keep (Δ₁ ∪ Δ₂)) _ (dbe e₂)))
    (Cons (eval (renameExpr (Δ₁ ∪ Δ₂) Δᵤ _ (inj₁ Δ₁ Δ₂ (dbe e₁))) env) env)
  ≡⟨ cong (λ e → eval e _)
      (renameExpr-trans (Keep Δ₂) (Keep (Δ₁ ∪ Δ₂)) (Keep Δᵤ) (∪sub₂ Δ₁ Δ₂) H (dbe e₂)) ⟩
  eval
    (renameExpr (Keep Δ₂) (Keep Δᵤ) _ (dbe e₂))
    (Cons (eval (renameExpr (Δ₁ ∪ Δ₂) Δᵤ _ (inj₁ Δ₁ Δ₂ (dbe e₁))) env) env)
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
  where
    open Relation.Binary.PropositionalEquality.≡-Reasoning
dbe-correct (Var i) Δᵤ H env = {!!}

-- TODO dead-binding-elimination preserves semantics
correct : (e : Expr Γ σ) (env : Env Γ) →
  let Δ , e' = analyse e
  in eval (dbe e') (prjEnv Δ env) ≡ eval e env
correct {Γ} e env =
  let Δ , e' = analyse e
  in
    eval (dbe e') (prjEnv Δ env)
  ≡⟨ {!!} ⟩  -- minor stuff
    eval (dbe e') (prjEnv' Δ (all Γ) (subset-⊆ Γ Δ) (env-of-all env))
  ≡⟨ sym (renameExpr-preserves Δ (all Γ) (subset-⊆ Γ Δ) (dbe e') (env-of-all env)) ⟩
    eval (renameExpr Δ (all Γ) (subset-⊆ Γ Δ) (dbe e')) (env-of-all env)
  ≡⟨ dbe-correct e' (all Γ) (subset-⊆ Γ Δ) (env-of-all env) ⟩  -- eval (dbe e) ≡ evalLive e
    evalLive (all Γ) e' (env-of-all env) (subset-⊆ Γ Δ)
  ≡⟨ evalLive-correct e' env ⟩  -- evalLive e ≡ eval (forget e)
    eval (forget e') env
  ≡⟨ cong (λ e' →  eval e' env) (analyse-preserves e) ⟩  -- forget (analyse e) ≡ e
    eval e env
  ∎
    -- TODO: what about directly: evalLive (analyse e) ≡ eval e
  where
    open Relation.Binary.PropositionalEquality.≡-Reasoning

-- original idea:
-- tease the proof apart into two steps: analyse preserves semantics (using evalLive);
-- and dbe and forget both preserve semantics;
-- and then combine these proofs (somehow) to show that dbe is semantics preserving.
-- eval e ≡ eval (forget (dbe e))
-- evalLive e ≡ evalLive (dbe (forget e))
-- eval e ≡ evalLive (analyse e)
-- analyse (dbe e)
