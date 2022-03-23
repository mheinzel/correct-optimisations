-- Strong live variable analysis
module StrongLive where

open import Data.List using (_∷_ ; [])
open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; subst)

open import Lang
open import Subset

data LiveExpr (Γ : Ctx) : (Δ : Subset Γ) → (σ : U) → Set where
  Val : ⟦ σ ⟧ → LiveExpr Γ ∅ σ
  Plus : ∀ {Δ₁ Δ₂} → LiveExpr Γ Δ₁ NAT → LiveExpr Γ Δ₂ NAT → LiveExpr Γ (Δ₁ ∪ Δ₂) NAT
  Eq : ∀ {Δ₁ Δ₂} → LiveExpr Γ Δ₁ NAT → LiveExpr Γ Δ₂ NAT → LiveExpr Γ (Δ₁ ∪ Δ₂) BOOL
  Var : (i : Ref σ Γ) → LiveExpr Γ [ i ] σ
  -- TODO: can we get rid of this?
  Eliminated : ∀ {Δ} → LiveExpr (τ ∷ Γ) (Drop Δ) σ → LiveExpr Γ Δ σ
  Let : ∀ {Δ₁ Δ₂}
      → (decl : LiveExpr Γ Δ₁ σ)
      → (body : LiveExpr (σ ∷ Γ) (Keep Δ₂) τ)
      → LiveExpr Γ (Δ₁ ∪ Δ₂) τ

-- strong dead binding elimination
analyse : Expr Γ σ → Σ[ Δ ∈ Subset Γ ] LiveExpr Γ Δ σ
analyse (Val x) =  ∅ , Val x
analyse (Plus e₁ e₂) with analyse e₁ | analyse e₂
... | Δ₁ , le₁ | Δ₂ , le₂ = (Δ₁ ∪ Δ₂) , (Plus le₁ le₂)
analyse (Eq e₁ e₂) with analyse e₁ | analyse e₂
... | Δ₁ , le₁ | Δ₂ , le₂ = (Δ₁ ∪ Δ₂) , (Eq le₁ le₂)
analyse (Let e₁ e₂) with analyse e₁ | analyse e₂
--  | Δ₁ , le₁ | Δ₂ , le₂ = (Δ₁ ∪ (pop Δ₂)) , (Let le₁ le₂)
... | Δ₁ , le₁ | (Keep Δ₂) , le₂ = (Δ₁ ∪ Δ₂) , (Let le₁ le₂)
... | Δ₁ , le₁ | (Drop Δ₂) , le₂ = Δ₂ , Eliminated le₂
analyse (Var x) = [ x ] , (Var x)

restrictRef : (i : Ref σ Γ) → Ref σ ⌊ [ i ] ⌋
restrictRef Top = Top
restrictRef (Pop i) = restrictRef i

helper : (Δ₁ : Subset (σ ∷ Γ)) (Δ₂ : Subset Γ) → Expr ⌊ Keep {Γ} {σ} Δ₂ ⌋ τ → Expr (σ ∷ ⌊ pop Δ₁ ∪ Δ₂ ⌋) τ 
helper (Drop Δ₁) Δ₂ e = inj₂ (Drop Δ₁) (Keep Δ₂) e
helper (Keep Δ₁) Δ₂ e = inj₂ (Keep Δ₁) (Keep Δ₂) e

optimize : LiveExpr Γ Δ σ → Expr ⌊ Δ ⌋ σ
optimize (Val x) = Val x
optimize (Plus {Δ₁} {Δ₂} e₁ e₂) = Plus (inj₁ Δ₁ Δ₂ (optimize e₁)) (inj₂ Δ₁ Δ₂ (optimize e₂))
optimize (Eq {Δ₁} {Δ₂} e₁ e₂) = Eq (inj₁ Δ₁ Δ₂ (optimize e₁)) (inj₂ Δ₁ Δ₂ (optimize e₂))
optimize {Γ} (Var i) = Var (restrictRef i)
optimize (Eliminated e) = optimize e
optimize {Γ} (Let {σ} {τ} {Δ₁} {Δ₂} e₁ e₂) =
  Let {_} {σ}
    (inj₁ Δ₁ Δ₂ (optimize e₁))
    (helper {σ} {Γ} (Drop Δ₁) Δ₂ (optimize e₂))

sdbe : Expr Γ σ → Σ[ Δ ∈ Subset Γ ] Expr ⌊ Δ ⌋ σ
sdbe e with analyse e
...       | liveVars , analysed = liveVars , (optimize analysed)


liftRename : (Δ : Subset Γ) → Expr ⌊ Δ ⌋ σ → Expr Γ σ
liftRename {Γ} {σ} Δ e = subst (λ Γ' → Expr Γ' σ) (⊆-of-all Γ) (renameExpr Δ (all Γ) (subset-⊆ Γ Δ) e)

sdbe' : Expr Γ σ → Expr Γ σ
sdbe' e = let liveVars , analysed = analyse e in liftRename liveVars (optimize analysed)

ex-unused-optimized : Expr Γ NAT
ex-unused-optimized = Val 2

test-optimized : sdbe' {[]} ex-unused ≡ ex-unused-optimized
test-optimized = refl

-- now, can we prove any of this?
opt-correct : (e : Expr Γ σ) (env : Env Γ) →
  let liveVars , analysed = analyse e in
   eval (optimize analysed) (prjEnv liveVars env) ≡ eval e env

opt-correct (Val x) env = refl
opt-correct (Plus e₁ e₂) env =
  let r₁ = opt-correct e₁ env
      r₂ = opt-correct e₂ env
  in {!!}
  -- missing:
  --
  -- eval 
  --   (optimized e₁)
  --   (prjEnv (liveVars e₁) env)
  --
  -- vs.
  --
  -- eval 
  --   (renameExpr (liveVars e₁) (liveVars e₁ ∪ liveVars e₂) _ (optimized e₁))
  --   (prjEnv (liveVars e₁ ∪ liveVars e₂) env)
  --
  -- with:
  -- liveVars = proj₁ . analyse
  -- optimized = optimize . proj₂ . analyse

opt-correct (Eq e₁ e₂) env = {!!}
opt-correct (Let e₁ e₂) env = {!!}
opt-correct (Var x) env = {!!}
