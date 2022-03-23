-- Live variable analysis
module Live where

open import Data.Nat using (_+_ ; _≡ᵇ_)
open import Data.List using (List ; _∷_ ; [])
open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; trans ; cong₂)

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
lookupSingle : (i : Ref σ Γ) → Env ⌊ ([ i ]) ⌋ → ⟦ σ ⟧
lookupSingle Top (Cons x env) = x
lookupSingle (Pop i) env = lookupSingle i env

evalLive : LiveExpr Γ Δ σ → Env ⌊ Δ ⌋ → ⟦ σ ⟧
evalLive (Val x) env = x
evalLive (Plus {Δ₁ = Δ₁} {Δ₂ = Δ₂} le₁ le₂) env = (evalLive le₁ (prj₁ Δ₁ Δ₂ env)) + (evalLive le₂ (prj₂ Δ₁ Δ₂ env))
evalLive (Eq {Δ₁ = Δ₁} {Δ₂ = Δ₂} le₁ le₂) env = (evalLive le₁ (prj₁ Δ₁ Δ₂ env)) ≡ᵇ (evalLive le₂ (prj₂ Δ₁ Δ₂ env))
evalLive (Let {Δ₁ = Δ₁} {Δ₂ = Drop Δ₂} le₁ le₂) env = evalLive le₂ (prj₂ Δ₁ Δ₂ env)
evalLive (Let {Δ₁ = Δ₁} {Δ₂ = Keep Δ₂} le₁ le₂) env = evalLive le₂ (Cons (evalLive le₁ (prj₁ Δ₁ Δ₂ env)) (prj₂ Δ₁ Δ₂ env))
evalLive (Var i) env = lookupSingle i env

-- TODO is this generality worthwhile? It can help avoid some of the
-- problems with composing environment projections in evalLive (and
-- the corresponding correctness proofs)
evalLive-sub : LiveExpr Γ Δ₁ σ → Δ₁ ⊆ Δ₂ → Env ⌊ Δ₂ ⌋ → ⟦ σ ⟧
evalLive-sub (Val x) H env = x
evalLive-sub (Plus le₁ le₂) H env = evalLive-sub le₁ {!!} env + evalLive-sub le₂ {!!} env
evalLive-sub (Eq le₁ le₂) H env = {!!}
evalLive-sub (Let le₁ le₂) H env = {!!}
evalLive-sub (Var i) H env = {!!}

-- forget . analyse = id
analyse-preserves : (e : Expr Γ σ) → forget (proj₂ (analyse e)) ≡ e
analyse-preserves (Val x) = refl
analyse-preserves (Plus e₁ e₂) = cong₂ Plus (analyse-preserves e₁) (analyse-preserves e₂)
analyse-preserves (Eq e₁ e₂) = cong₂ Eq (analyse-preserves e₁) (analyse-preserves e₂)
analyse-preserves (Let e₁ e₂) = cong₂ Let (analyse-preserves e₁) (analyse-preserves e₂)
analyse-preserves (Var x) = refl

-- TODO show evalLive (analyse e) = eval e (slightly harder)
analyse-correct : (e : Expr Γ σ) (env : Env Γ) →
  evalLive (proj₂ (analyse e)) (prjEnv (proj₁ (analyse e)) env) ≡ eval e env
analyse-correct (Val x) env = refl
analyse-correct (Plus e₁ e₂) env with analyse e₁ | analyse e₂
... | Δ₁ , le₁ | Δ₂ , le₂ = {!!}
analyse-correct (Eq e e₁) env = {!!}
analyse-correct (Let e e₁) env = {!!}
analyse-correct (Var x) env = {!!}


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

-- TODO show eval e = dbe (analyse e) -- that is dead-binding-elimination preserves semantics
-- probably easier to reformulate this (avoiding the let/with)
-- and tease the proof apart into two steps: analyse preserves semantics (using evalLive);
-- and dbe and forget both preserve semantics;
-- and then combine these proofs (somehow) to show that dbe is semantics preserving.
correct : (e : Expr Γ σ) (env : Env Γ) →
  let (Δ , le) = analyse e in eval e env ≡ eval (dbe le) (prjEnv Δ env)
correct (Val x) env = refl
correct (Plus e₁ e₂) env with analyse e₁ | analyse e₂
... | Δ₁ , le₁ | Δ₂ , le₂ = {!!}
correct (Eq e e₁) env = {!!}
correct (Let e₁ e₂) env with analyse e₁ | analyse e₂
... | Δ₁ , le₁ | Drop Δ₂ , le₂ =
  let ih = correct e₂ (Cons (eval e₁ env) env) in trans ih {!!}
... | Δ₁ , le₁ | Keep Δ₂ , le₂ = {!!}
correct (Var Top) (Cons x env) = refl
correct (Var (Pop x)) (Cons _ env) = correct (Var x) env
