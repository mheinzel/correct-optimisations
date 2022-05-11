-- Strong live variable analysis
module StrongLive where

open import Data.Nat
  using (_+_ ; _≡ᵇ_) renaming (ℕ to Nat ; zero to Zero ; suc to Succ)
open import Data.List using (_∷_ ; [])
open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; trans ; cong ; subst ; cong₂ ; sym)

open import Lang
open import Subset

all[_] : Ref τ Γ → Subset Γ
all[ Top ] = Keep ∅
all[ Pop i ] = Drop (all[ i ])

-- A no-op, but  we need to convince the compiler somehow.
envOfAll : Env Γ → Env ⌊ all Γ ⌋
envOfAll Nil = Nil
envOfAll (Cons x env) = Cons x (envOfAll env)

prjEnv' : (Δ : Subset Γ) (env : Env Γ) → Env ⌊ Δ ⌋
prjEnv' {Γ} Δ env = prjEnv Δ (all Γ) (⊆all Γ Δ) (envOfAll env)

data LiveExpr (Γ : Ctx) : (Δ : Subset Γ) → (σ : U) → Set where
  Val : ⟦ σ ⟧ → LiveExpr Γ ∅ σ
  Plus : ∀ {Δ₁ Δ₂} → LiveExpr Γ Δ₁ NAT → LiveExpr Γ Δ₂ NAT → LiveExpr Γ (Δ₁ ∪ Δ₂) NAT
  Eq : ∀ {Δ₁ Δ₂} → LiveExpr Γ Δ₁ NAT → LiveExpr Γ Δ₂ NAT → LiveExpr Γ (Δ₁ ∪ Δ₂) BOOL
  Var : (i : Ref σ Γ) → LiveExpr Γ (all[ i ]) σ
  Eliminated : ∀ {Δ}
      → (decl : Expr Γ τ)  -- just remembering this, but we don't need to analyse it further, as it's unused
      → (body : LiveExpr (τ ∷ Γ) (Drop Δ) σ)
      → LiveExpr Γ Δ σ
  Let : ∀ {Δ₁ Δ₂}
      → (decl : LiveExpr Γ Δ₁ σ)
      → (body : LiveExpr (σ ∷ Γ) (Keep Δ₂) τ)
      → LiveExpr Γ (Δ₁ ∪ Δ₂) τ

forget : LiveExpr Γ Δ σ → Expr Γ σ
forget (Val x) = Val x
forget (Plus e₁ e₂) = Plus (forget e₁) (forget e₂)
forget (Eq e₁ e₂) = Eq (forget e₁) (forget e₂)
forget (Var i) = Var i
forget (Eliminated e₁ e₂) = Let e₁ (forget e₂)
forget (Let e₁ e₂) = Let (forget e₁) (forget e₂)

-- Now let's try to define a semantics for LiveExpr...
lookupSingle : (i : Ref σ Γ) → Env ⌊ (all[ i ]) ⌋ → ⟦ σ ⟧
lookupSingle Top (Cons x env) = x
lookupSingle (Pop i) env = lookupSingle i env

evalLive : LiveExpr Γ Δ σ → Env ⌊ Δ ⌋ → ⟦ σ ⟧
evalLive (Val x) env = x
evalLive (Plus {Δ₁} {Δ₂} e₁ e₂) env = evalLive e₁ (prjEnv₁ Δ₁ Δ₂ env) + evalLive e₂ (prjEnv₂ Δ₁ Δ₂ env)
evalLive (Eq {Δ₁} {Δ₂} e₁ e₂) env = evalLive e₁ (prjEnv₁ Δ₁ Δ₂ env) ≡ᵇ evalLive e₂ (prjEnv₂ Δ₁ Δ₂ env)
evalLive (Var i) env = lookupSingle i env
evalLive (Eliminated _ e) env = evalLive e env
evalLive (Let {σ} {τ} {Δ₁} {Δ₂} e₁ e₂) env =
  evalLive e₂ (Cons (evalLive e₁ (prjEnv₁ Δ₁ Δ₂ env)) (prjEnv₂ Δ₁ Δ₂ env))

-- strong dead binding elimination
analyse : Expr Γ σ → Σ[ Δ ∈ Subset Γ ] LiveExpr Γ Δ σ
analyse (Val x) =  ∅ , Val x
analyse (Plus e₁ e₂) with analyse e₁ | analyse e₂
... | Δ₁ , le₁ | Δ₂ , le₂ = (Δ₁ ∪ Δ₂) , (Plus le₁ le₂)
analyse (Eq e₁ e₂) with analyse e₁ | analyse e₂
... | Δ₁ , le₁ | Δ₂ , le₂ = (Δ₁ ∪ Δ₂) , (Eq le₁ le₂)
analyse (Let e₁ e₂) with analyse e₂
... | (Keep Δ₂) , le₂ = (proj₁ (analyse e₁) ∪ Δ₂) , (Let (proj₂ (analyse e₁)) le₂)
... | (Drop Δ₂) , le₂ = Δ₂ , Eliminated e₁ le₂
analyse {Γ} (Var x) = all[ x ] , (Var x)

restrictedRef : (i : Ref σ Γ) → Ref σ ⌊ all[ i ] ⌋
restrictedRef Top = Top
restrictedRef (Pop i) = restrictedRef i

helper : (Δ₁ : Subset (σ ∷ Γ)) (Δ₂ : Subset Γ) → Expr ⌊ Keep {Γ} {σ} Δ₂ ⌋ τ → Expr (σ ∷ ⌊ pop Δ₁ ∪ Δ₂ ⌋) τ 
helper (Drop Δ₁) Δ₂ e = injExpr₂ (Drop Δ₁) (Keep Δ₂) e
helper (Keep Δ₁) Δ₂ e = injExpr₂ (Keep Δ₁) (Keep Δ₂) e

optimize : LiveExpr Γ Δ σ → Expr ⌊ Δ ⌋ σ
optimize (Val x) = Val x
optimize (Plus {Δ₁} {Δ₂} e₁ e₂) = Plus (injExpr₁ Δ₁ Δ₂ (optimize e₁)) (injExpr₂ Δ₁ Δ₂ (optimize e₂))
optimize (Eq {Δ₁} {Δ₂} e₁ e₂) = Eq (injExpr₁ Δ₁ Δ₂ (optimize e₁)) (injExpr₂ Δ₁ Δ₂ (optimize e₂))
optimize {Γ} (Var i) = Var (restrictedRef i)
optimize (Eliminated _ e) = optimize e
optimize {Γ} (Let {σ} {τ} {Δ₁} {Δ₂} e₁ e₂) =
  Let {_} {σ}
    (injExpr₁ Δ₁ Δ₂ (optimize e₁))
    (helper {σ} {Γ} (Drop Δ₁) Δ₂ (optimize e₂))

sdbe : Expr Γ σ → Σ[ Δ ∈ Subset Γ ] Expr ⌊ Δ ⌋ σ
sdbe e with analyse e
...       | liveVars , analysed = liveVars , (optimize analysed)


⌊allΓ⌋≡Γ : (Γ : Ctx) →
  ⌊ all Γ ⌋ ≡ Γ
⌊allΓ⌋≡Γ [] = refl
⌊allΓ⌋≡Γ (τ ∷ Γ) = cong (τ ∷_) (⌊allΓ⌋≡Γ Γ)

liftRename : (Δ : Subset Γ) → Expr ⌊ Δ ⌋ σ → Expr Γ σ
liftRename {Γ} {σ} Δ e = subst (λ Γ' → Expr Γ' σ) (⌊allΓ⌋≡Γ Γ) (renameExpr Δ (all Γ) (⊆all Γ Δ) e)

sdbe' : Expr Γ σ → Expr Γ σ
sdbe' e = let liveVars , analysed = analyse e in liftRename liveVars (optimize analysed)

lemma-lookup : (Δ₁ Δ₂ : Subset Γ) (i : Ref σ ⌊ Δ₁ ⌋) (env : Env ⌊ Δ₂ ⌋) → (subset : Δ₁ ⊆ Δ₂) →
  lookup (renameVar Δ₁ Δ₂ subset i) env ≡ lookup i (prjEnv Δ₁ Δ₂ subset env)
lemma-lookup (Drop Δ₁) (Drop Δ₂) i env subset = lemma-lookup Δ₁ Δ₂ i env subset
lemma-lookup (Drop Δ₁) (Keep Δ₂) i (Cons x env) subset = lemma-lookup Δ₁ Δ₂ i env subset
lemma-lookup (Keep Δ₁) (Keep Δ₂) Top (Cons x env) subset = refl
lemma-lookup (Keep Δ₁) (Keep Δ₂) (Pop i) (Cons x env) subset = lemma-lookup Δ₁ Δ₂ i env subset

lemma : (Δ₁ Δ₂ : Subset Γ) (e : Expr ⌊ Δ₁ ⌋ σ) (env : Env ⌊ Δ₂ ⌋) → (subset : Δ₁ ⊆ Δ₂) →
  eval (renameExpr Δ₁ Δ₂ subset e) env ≡ eval e (prjEnv Δ₁ Δ₂ subset env)
lemma Δ₁ Δ₂ (Val x) env subset = refl
lemma Δ₁ Δ₂ (Plus e₁ e₂) env subset = cong₂ _+_ (lemma Δ₁ Δ₂ e₁ env subset) (lemma Δ₁ Δ₂ e₂ env subset)
lemma Δ₁ Δ₂ (Eq e₁ e₂) env subset =  cong₂ _≡ᵇ_ (lemma Δ₁ Δ₂ e₁ env subset) (lemma Δ₁ Δ₂ e₂ env subset)
lemma Δ₁ Δ₂ (Let e₁ e₂) env subset = {!!} -- should be doable, just a bit messy
lemma Δ₁ Δ₂ (Var i) env subset = lemma-lookup Δ₁ Δ₂ i env subset

lemma₁ : (e : LiveExpr Γ Δ₁ σ) (env : Env ⌊ Δ₁ ∪ Δ₂ ⌋)
  → (eval (optimize e) (prjEnv₁ Δ₁ Δ₂ env) ≡ evalLive e (prjEnv₁ Δ₁ Δ₂ env))
  → eval (injExpr₁ Δ₁ Δ₂ (optimize e)) env ≡ evalLive e (prjEnv₁ Δ₁ Δ₂ env)
lemma₁ {Γ} {Δ₁} {σ} {Δ₂} e env prf = trans (lemma Δ₁ (Δ₁ ∪ Δ₂) (optimize e) env (⊆∪₁ Δ₁ Δ₂)) prf

lemma₂ : (e : LiveExpr Γ Δ₂ σ) (env : Env ⌊ Δ₁ ∪ Δ₂ ⌋)
  → (eval (optimize e) (prjEnv₂ Δ₁ Δ₂ env) ≡ evalLive e (prjEnv₂ Δ₁ Δ₂ env))
  → eval (injExpr₂ Δ₁ Δ₂ (optimize e)) env ≡ evalLive e (prjEnv₂ Δ₁ Δ₂ env)
lemma₂ {Γ} {Δ₂} {σ} {Δ₁} e env prf = trans (lemma Δ₂ (Δ₁ ∪ Δ₂) (optimize e) env (⊆∪₂ Δ₁ Δ₂)) prf

lemma-ref : (i : Ref σ Γ) (env : Env ⌊ all[ i ] ⌋) →
  lookup (restrictedRef i) env ≡ lookupSingle i env
lemma-ref Top (Cons x env) = refl
lemma-ref (Pop i) env = lemma-ref i env

optimize-correct : (analysed : LiveExpr Γ Δ σ) (env : Env ⌊ Δ ⌋) →
   eval (optimize analysed) env ≡ evalLive analysed env
optimize-correct (Val x) env = refl
optimize-correct (Plus {Δ₁} {Δ₂} e₁ e₂) env =
  cong₂ _+_
    (lemma₁ e₁ env (optimize-correct e₁ (prjEnv₁ Δ₁ Δ₂ env)))
    (lemma₂ e₂ env (optimize-correct e₂ (prjEnv₂ Δ₁ Δ₂ env)))
optimize-correct (Eq {Δ₁} {Δ₂} e₁ e₂) env =
  cong₂ _≡ᵇ_
    (lemma₁ e₁ env (optimize-correct e₁ (prjEnv₁ Δ₁ Δ₂ env)))
    (lemma₂ e₂ env (optimize-correct e₂ (prjEnv₂ Δ₁ Δ₂ env)))
optimize-correct (Var i) env = lemma-ref i env
optimize-correct (Eliminated decl e) env = optimize-correct e env
optimize-correct {Γ} (Let {τ} {σ} {Δ₁} {Δ₂} e₁ e₂) env =
  let h₁ = optimize-correct e₁ (prjEnv₁ Δ₁ Δ₂ env)
      H₁ = lemma₁ e₁ env h₁ 
      h₂ = optimize-correct {τ ∷ Γ} {Keep Δ₂} e₂ (Cons (evalLive e₁ (prjEnv₁ Δ₁ Δ₂ env)) (prjEnv₂ Δ₁ Δ₂ env))
      -- not sure why this doesn't work?
      H₂ = lemma₂ {τ ∷ Γ} {Keep Δ₂} {σ} {Drop Δ₁} e₂ (Cons (evalLive e₁ (prjEnv₁ Δ₁ Δ₂ env)) env) {!h₂!}
  in
    eval
      (injExpr₂ (Drop Δ₁) (Keep Δ₂) (optimize e₂))
      (Cons (eval (injExpr₁ Δ₁ Δ₂ (optimize e₁)) env) env)
  ≡⟨ cong (λ x → eval (injExpr₂ (Drop Δ₁) (Keep Δ₂) (optimize e₂)) (Cons x env)) H₁ ⟩
    eval
      (injExpr₂ (Drop Δ₁) (Keep Δ₂) (optimize e₂))
      (Cons (evalLive e₁ (prjEnv₁ Δ₁ Δ₂ env)) env)
  ≡⟨ H₂ ⟩
    evalLive
      e₂
      (prjEnv₂ (Drop Δ₁) (Keep Δ₂) (Cons (evalLive e₁ (prjEnv₁ Δ₁ Δ₂ env)) env))
  ≡⟨ refl ⟩
    evalLive
      e₂
      (Cons (evalLive e₁ (prjEnv₁ Δ₁ Δ₂ env)) (prjEnv₂ Δ₁ Δ₂ env))
  ≡⟨ cong (λ x → evalLive e₂ (Cons x (prjEnv₂ Δ₁ Δ₂ env)) ) (sym H₁) ⟩
    evalLive
      e₂
      (Cons (eval (injExpr₁ Δ₁ Δ₂ (optimize e₁)) env) (prjEnv₂ Δ₁ Δ₂ env))
  ≡⟨ cong (λ v → evalLive e₂ (Cons v (prjEnv₂ Δ₁ Δ₂ env))) H₁ ⟩
    evalLive
      e₂
      (Cons (evalLive e₁ (prjEnv₁ Δ₁ Δ₂ env)) (prjEnv₂ Δ₁ Δ₂ env))
  ∎
  where
    open Relation.Binary.PropositionalEquality.≡-Reasoning
    
evalLive-correct : (e : LiveExpr Γ Δ σ) (env : Env Γ) →
  evalLive e (prjEnv' Δ env) ≡ eval (forget e) env
evalLive-correct (Val x) env = refl
evalLive-correct (Plus e₁ e₂) env = {!cong₂ _+_ (evalLive-correct e₁ ?) ?!}
-- we need: prjEnv₁ Δ₁ Δ₂ (prjEnv (Δ₁ ∪ Δ₂) env) ≡ prjEnv Δ₁ env
evalLive-correct (Eq e₁ e₂) env = {!!}
evalLive-correct (Var i) env = {!!}
evalLive-correct (Eliminated decl e) env = {!!}
evalLive-correct (Let e₁ e₂) env = {!!}

analyse-preserves : (e : Expr Γ σ) →
  forget (proj₂ (analyse e)) ≡ e
analyse-preserves (Val x) = refl
analyse-preserves (Plus e₁ e₂) = cong₂ Plus (analyse-preserves e₁) (analyse-preserves e₂)
analyse-preserves (Eq e₁ e₂) = cong₂ Eq (analyse-preserves e₁) (analyse-preserves e₂)
analyse-preserves (Let e₁ e₂) with analyse e₂ | analyse-preserves e₂
... | Drop Δ₂ , le₂ | r = cong (Let e₁) r
... | Keep Δ₂ , le₂ | r = cong₂ Let (analyse-preserves e₁) r
analyse-preserves (Var x) = refl

-- This is what we wanted to achieve, right? Broken down into subproofs.
opt-correct : (e : Expr Γ σ) (env : Env Γ) →
   eval (optimize (proj₂ (analyse e))) (prjEnv' (proj₁ (analyse e)) env) ≡ eval e env
opt-correct e env =
    eval (optimize (proj₂ (analyse e))) (prjEnv' (proj₁ (analyse e)) env)
  ≡⟨ optimize-correct (proj₂ (analyse e)) (prjEnv' (proj₁ (analyse e)) env) ⟩
    evalLive (proj₂ (analyse e)) (prjEnv' (proj₁ (analyse e)) env)
  ≡⟨ evalLive-correct (proj₂ (analyse e)) env ⟩
    eval (forget (proj₂ (analyse e))) env
  ≡⟨ cong (λ e' → eval e' env) (analyse-preserves e) ⟩
    eval e env
  ∎
  where
    open Relation.Binary.PropositionalEquality.≡-Reasoning
