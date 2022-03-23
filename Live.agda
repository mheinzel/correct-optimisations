module Live where

open import Data.Nat
  using (_+_ ; _≡ᵇ_) renaming (ℕ to Nat ; zero to Zero ; suc to Succ)
open import Data.Bool renaming (true to True ; false to False)
open import Data.Fin using (Fin)
open import Data.List using (List ; _∷_ ; [])
open import Data.Product
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; trans ; cong ; subst ; cong₂)

-- Types
data U : Set where
  BOOL NAT : U

⟦_⟧ : U → Set
⟦ BOOL ⟧  = Bool
⟦ NAT ⟧   = Nat

Ctx = List U

variable
  n : Nat
  b : Bool
  Γ : Ctx
  σ τ : U

-- Syntax
data Ref (σ : U) : Ctx → Set where
  Top  : Ref σ (σ ∷ Γ)
  Pop  : Ref σ Γ → Ref σ (τ ∷ Γ)
 
data Expr (Γ : Ctx) : (σ : U) → Set where
  Val : ⟦ σ ⟧ → Expr Γ σ
  Plus : Expr Γ NAT → Expr Γ NAT → Expr Γ NAT
  Eq : Expr Γ NAT → Expr Γ NAT → Expr Γ BOOL
  Let : (decl : Expr Γ σ) → (body : Expr (σ ∷ Γ) τ) → Expr Γ τ
  Var : Ref σ Γ → Expr Γ σ

-- Semantics
data Env : Ctx → Set where
  Nil   : Env []
  Cons  : ⟦ σ ⟧ → Env Γ → Env (σ ∷ Γ)

lookup : Ref σ Γ → Env Γ → ⟦ σ ⟧
lookup Top        (Cons x env)   = x
lookup (Pop ref)  (Cons x env)   = lookup ref env

eval : Expr Γ σ → Env Γ → ⟦ σ ⟧
eval (Val x) env = x
eval (Eq n m) env = (eval n env) ≡ᵇ (eval m env)
eval (Plus e₁ e₂) env = eval e₁ env + eval e₂ env
eval (Let e body) env = eval body (Cons (eval e env) env)
eval (Var x) env = lookup x env 

-- Examples

-- let x = 1 in let y = x in 2
ex-unused : Expr Γ NAT
ex-unused = Let (Val 1) (Let (Var Top) (Val 2))

-- λ a → let x = a in let y = 1 in let z = x + 5 in y + a
ex-unused-2 : Expr (NAT ∷ Γ) NAT
ex-unused-2 =
  Let (Var Top)
    (Let (Val 1)
      (Let (Var (Pop Top))
        (Plus (Var (Pop Top)) (Var (Pop (Pop (Pop Top)))))))

test-ex-unused : (env : Env Γ) → eval ex-unused env ≡ 2
test-ex-unused env = refl

test-ex-unused-2 : (env : Env Γ) (n : Nat) → eval ex-unused-2 (Cons n env) ≡ Succ n
test-ex-unused-2 env n = refl

-- Subsets of our context and operations them 
data Subset : Ctx → Set where
  Empty  : Subset []
  Drop   : Subset Γ → Subset (τ ∷ Γ)
  Keep   : Subset Γ → Subset (τ ∷ Γ)

variable
  Δ Δ₁ Δ₂ : Subset Γ

∅ : {Γ : Ctx} → Subset Γ
∅ {[]} = Empty
∅ {x ∷ Γ} = Drop ∅

all : (Γ : Ctx) → Subset Γ
all [] = Empty
all (x ∷ Γ) = Keep (all Γ)

_∪_ : Subset Γ → Subset Γ → Subset Γ
Empty ∪ Empty = Empty
Drop Δ₁ ∪ Drop Δ₂ = Drop (Δ₁ ∪ Δ₂)
Drop Δ₁ ∪ Keep Δ₂ = Keep (Δ₁ ∪ Δ₂)
Keep Δ₁ ∪ Drop Δ₂ = Keep (Δ₁ ∪ Δ₂)
Keep Δ₁ ∪ Keep Δ₂ = Keep (Δ₁ ∪ Δ₂)

[_] : Ref τ Γ → Subset Γ
[ Top ]    = Keep ∅
[ Pop p ]  = Drop [ p ]

pop : Subset (σ ∷ Γ) → Subset Γ
pop (Drop Δ) = Δ
pop (Keep Δ) = Δ

⌊_⌋ : Subset Γ → Ctx
⌊ Empty ⌋              = []
⌊ Drop Δ ⌋             = ⌊ Δ ⌋
⌊ Keep {τ = τ} Δ ⌋     = τ ∷ ⌊ Δ ⌋

⊆-of-all : (Γ : Ctx) → ⌊ all Γ ⌋ ≡ Γ
⊆-of-all [] = refl
⊆-of-all (x ∷ Γ) = cong (λ Γ' → x ∷ Γ') (⊆-of-all Γ)

-- Relating subsets and environments
_⊆_ : Subset Γ → Subset Γ → Set
Empty ⊆ Empty = ⊤
Drop Δ₁ ⊆ Drop Δ₂ = Δ₁ ⊆ Δ₂
Drop Δ₁ ⊆ Keep Δ₂ = Δ₁ ⊆ Δ₂
Keep Δ₁ ⊆ Drop Δ₂ = ⊥
Keep Δ₁ ⊆ Keep Δ₂ = Δ₁ ⊆ Δ₂

subset-⊆ : (Γ : Ctx) → (Δ : Subset Γ) → Δ ⊆ all Γ
subset-⊆ Γ Empty = tt
subset-⊆ (x ∷ Γ) (Drop Δ) = subset-⊆ Γ Δ
subset-⊆ (x ∷ Γ) (Keep Δ) = subset-⊆ Γ Δ

-- Renamings / weakenings
renameVar : (Δ₁ Δ₂ : Subset Γ) → Δ₁ ⊆ Δ₂ → Ref σ ⌊ Δ₁ ⌋ → Ref σ ⌊ Δ₂ ⌋
renameVar (Drop Δ₁) (Drop Δ₂) H i = renameVar Δ₁ Δ₂ H i
renameVar (Drop Δ₁) (Keep Δ₂) H i = Pop (renameVar Δ₁ Δ₂ H i)
renameVar (Keep Δ₁) (Keep Δ₂) H Top = Top
renameVar (Keep Δ₁) (Keep Δ₂) H (Pop i) = Pop (renameVar Δ₁ Δ₂ H i)

renameExpr : (Δ₁ Δ₂ : Subset Γ) → Δ₁ ⊆ Δ₂ → Expr ⌊ Δ₁ ⌋ σ → Expr ⌊ Δ₂ ⌋ σ
renameExpr Δ₁ Δ₂ H (Val x) = Val x
renameExpr Δ₁ Δ₂ H (Plus e₁ e₂) = Plus (renameExpr Δ₁ Δ₂ H e₁) (renameExpr Δ₁ Δ₂ H e₂)
renameExpr Δ₁ Δ₂ H (Eq e₁ e₂) = Eq (renameExpr Δ₁ Δ₂ H e₁) (renameExpr Δ₁ Δ₂ H e₂)
renameExpr Δ₁ Δ₂ H (Let e₁ e₂) = Let (renameExpr Δ₁ Δ₂ H e₁) (renameExpr (Keep Δ₁) (Keep Δ₂) H e₂)
renameExpr Δ₁ Δ₂ H (Var x) = Var (renameVar Δ₁ Δ₂ H x)

∪sym : (Δ₁ Δ₂ : Subset Γ) → (Δ₁ ∪ Δ₂) ≡ (Δ₂ ∪ Δ₁)
∪sym Empty Empty = refl
∪sym (Drop x) (Drop y) = cong Drop (∪sym x y)
∪sym (Drop x) (Keep y) = cong Keep (∪sym x y)
∪sym (Keep x) (Drop y) = cong Keep (∪sym x y)
∪sym (Keep x) (Keep y) = cong Keep (∪sym x y)

∪trans : (Δ₁ Δ₂ Δ₃ : Subset Γ) → (Δ₁ ⊆ Δ₂) → (Δ₂ ⊆ Δ₃) → Δ₁ ⊆ Δ₃
∪trans Empty Empty Empty Δ₁⊆Δ₂ Δ₂⊆Δ₃ = tt
∪trans (Drop Δ₁) (Drop Δ₂) (Drop Δ₃) Δ₁⊆Δ₂ Δ₂⊆Δ₃ = ∪trans Δ₁ Δ₂ Δ₃ Δ₁⊆Δ₂ Δ₂⊆Δ₃
∪trans (Drop Δ₁) (Drop Δ₂) (Keep Δ₃) Δ₁⊆Δ₂ Δ₂⊆Δ₃ = ∪trans Δ₁ Δ₂ Δ₃ Δ₁⊆Δ₂ Δ₂⊆Δ₃
∪trans (Drop Δ₁) (Keep Δ₂) (Keep Δ₃) Δ₁⊆Δ₂ Δ₂⊆Δ₃ = ∪trans Δ₁ Δ₂ Δ₃ Δ₁⊆Δ₂ Δ₂⊆Δ₃
∪trans (Keep Δ₁) (Keep Δ₂) (Keep Δ₃) Δ₁⊆Δ₂ Δ₂⊆Δ₃ = ∪trans Δ₁ Δ₂ Δ₃ Δ₁⊆Δ₂ Δ₂⊆Δ₃

∪sub₁ : (Δ₁ Δ₂ : Subset Γ) → Δ₁ ⊆ (Δ₁ ∪ Δ₂)
∪sub₁ Empty Empty = tt
∪sub₁ (Drop Δ₁) (Drop Δ₂) = ∪sub₁ Δ₁ Δ₂
∪sub₁ (Drop Δ₁) (Keep Δ₂) = ∪sub₁ Δ₁ Δ₂
∪sub₁ (Keep Δ₁) (Drop Δ₂) = ∪sub₁ Δ₁ Δ₂
∪sub₁ (Keep Δ₁) (Keep Δ₂) = ∪sub₁ Δ₁ Δ₂

∪sub₂ : (Δ₁ Δ₂ : Subset Γ) → Δ₂ ⊆ (Δ₁ ∪ Δ₂)  
∪sub₂ Empty Empty = tt
∪sub₂ (Drop Δ₁) (Drop Δ₂) = ∪sub₂ Δ₁ Δ₂
∪sub₂ (Drop Δ₁) (Keep Δ₂) = ∪sub₂ Δ₁ Δ₂
∪sub₂ (Keep Δ₁) (Drop Δ₂) = ∪sub₂ Δ₁ Δ₂
∪sub₂ (Keep Δ₁) (Keep Δ₂) = ∪sub₂ Δ₁ Δ₂

inj₁ : (Δ₁ Δ₂ : Subset Γ) → Expr ⌊ Δ₁ ⌋ σ → Expr ⌊ Δ₁ ∪ Δ₂ ⌋ σ
inj₁ Δ₁ Δ₂ = renameExpr Δ₁ (Δ₁ ∪ Δ₂) (∪sub₁ Δ₁ Δ₂)

inj₂ : (Δ₁ Δ₂ : Subset Γ) → Expr ⌊ Δ₂ ⌋ σ → Expr ⌊ Δ₁ ∪ Δ₂ ⌋ σ
inj₂ Δ₁ Δ₂ = renameExpr Δ₂ (Δ₁ ∪ Δ₂) (∪sub₂ Δ₁ Δ₂)

-- Restricting an environment to some subset of (required) values
prjEnv : (Δ : Subset Γ) → Env Γ → Env ⌊ Δ ⌋
prjEnv Empty Nil = Nil
prjEnv (Drop Δ) (Cons x env) = prjEnv Δ env
prjEnv (Keep Δ) (Cons x env) = Cons x (prjEnv Δ env)

-- More general version
prjEnv' : (Δ₁ Δ₂ : Subset Γ) → Δ₁ ⊆ Δ₂ → Env ⌊ Δ₂ ⌋ → Env ⌊ Δ₁ ⌋
prjEnv' Empty Empty prf env = env
prjEnv' (Drop Δ₁) (Drop Δ₂) prf env = prjEnv' Δ₁ Δ₂ prf env
prjEnv' (Drop Δ₁) (Keep Δ₂) prf (Cons x env) = prjEnv' Δ₁ Δ₂ prf env
prjEnv' (Keep Δ₁) (Keep Δ₂) prf (Cons x env) = Cons x (prjEnv' Δ₁ Δ₂ prf env)


-- TODO what is the expected behaviour and use of this?
sub₁ : (Δ₁ Δ₂ : Subset Γ) → Subset ⌊ Δ₁ ∪ Δ₂ ⌋
sub₁ Empty Empty = Empty
sub₁ (Drop Δ₁) (Drop Δ₂) = sub₁ Δ₁ Δ₂
sub₁ (Drop Δ₁) (Keep Δ₂) = Drop (sub₁ Δ₁ Δ₂) -- why not: Drop (sub₁ Δ₁ Δ₂)
sub₁ (Keep Δ₁) (Drop Δ₂) = Keep (sub₁ Δ₁ Δ₂) -- not sure why this is not symmetric
sub₁ (Keep Δ₁) (Keep Δ₂) = Keep (sub₁ Δ₁ Δ₂)

-- TODO finish these? Or use alternative def using ⊆?
prj₁ : ∀ (Δ₁ Δ₂ : Subset Γ) → Env ⌊ Δ₁ ∪ Δ₂ ⌋ → Env ⌊ Δ₁ ⌋
prj₁ Δ₁ Δ₂ = prjEnv' Δ₁ (Δ₁ ∪ Δ₂) (∪sub₁ Δ₁ Δ₂)

prj₂ : (Δ₁ Δ₂ : Subset Γ) → Env ⌊ Δ₁ ∪ Δ₂ ⌋ → Env ⌊ Δ₂ ⌋
prj₂ Δ₁ Δ₂ = prjEnv' Δ₂ (Δ₁ ∪ Δ₂) (∪sub₂ Δ₁ Δ₂)

-- Live variable analysis
module Live where
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
