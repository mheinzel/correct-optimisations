---
author: Matthias Heinzel
title: Provingly Correct Optimisations on Intrinsically Typed Expressions
subtitle: Extended Abstract
institute: Utrecht University
theme: metropolis
---


# Intrinsically typed syntax trees

## A simple language

$$
  P, Q ::= v
  \ \big|\  P + Q
  \ \big|\  \ldots
  \ \big|\  \textbf{let } x = P \textbf{ in } Q
  \ \big|\  x
$$

## Type-safety by construction

```agda
data U : Set where
  BOOL  : U
  NAT   : U

⟦_⟧ : U → Set
⟦ BOOL ⟧  = Bool
⟦ NAT ⟧   = Nat

data Expr : (σ : U) → Set where
  Val   : ⟦ σ ⟧ → Expr σ
  Plus  : Expr NAT → Expr NAT → Expr NAT
  ...
```

## Scope-safety by construction

De-Bruijn-indices:

* keep track of bindings in scope (by position)

```agda
Ctx = List U
```

## Scope-safety by construction

```agda
data Expr (Γ : Ctx) : (σ : U) → Set where
  Val   : ⟦ σ ⟧ → Expr Γ σ
  Plus  : Expr Γ NAT → Expr Γ NAT → Expr Γ NAT
```
. . .

```agda
  Let   : Expr Γ σ → Expr (σ ∷ Γ) τ → Expr Γ τ
  Var   : Ref σ Γ → Expr Γ σ
```

. . .

```agda
data Ref (σ : U) : Ctx → Set where
  Top  : Ref σ (σ ∷ Γ)
  Pop  : Ref σ Γ → Ref σ (τ ∷ Γ)
```

## Scope-safety by construction

```agda
data Env : Ctx → Set where
  Nil   : Env []
  Cons  : ⟦ σ ⟧ → Env Γ → Env (σ ∷ Γ)
```

```agda
eval : Expr Γ σ → Env Γ → ⟦ σ ⟧
eval (Val v)       env  = v
eval (Plus e₁ e₂)  env  = eval e₁ env + eval e₂ env
eval (Let e₁ e₂)   env  = eval e₂ (Cons (eval e₁ env) env)
eval (Var x)       env  = lookup x env
```

## Intrinsically typed syntax trees

* well-known idea

* existing work on basic operations (evaluation, substitution, ...)

* but little focus on optimisations


# Optimisations on intrinsically typed expressions

## Optimisations on intrinsically typed expressions

* plethora of potential optimisations

* essential for most compilers

* many opportunities to introduce bugs

## Optimisations on intrinsically typed expressions

* **Analysis** needs to identify optimisation opportunities *and* provide proof that they are safe

* **Transformation** needs to preserve type- and scope-safety

* finally, we want to prove preservation of semantics


# Dead binding elimination (DBE)

* if bindings are not used, we want to remove them

* use live variable analysis (LVA) to annotate each expression with subset of context that is live

## Sub-contexts

* a **sub-context** is a context with an order-preserving embedding (OPE)

* useful to bundle these into a single data type

```agda
data SubCtx : Ctx → Set where
  Empty  : SubCtx []
  Drop   : SubCtx Γ → SubCtx (τ ∷ Γ)
  Keep   : SubCtx Γ → SubCtx (τ ∷ Γ)
```

## Sub-contexts

* we define some operations

```agda
_⊆_ : SubCtx Γ → SubCtx Γ → Set

_∪_ : SubCtx Γ → SubCtx Γ → SubCtx Γ
```

* we will only consider expressions in a context $\lfloor \Delta \rfloor$ determined by some sub-context $\Delta$

## Annotated expressions

* $\Delta$: *defined* bindings, top-down (as $\Gamma$ before)
* $\Delta'$: *used* bindings, bottom-up

```agda
data LiveExpr : (Δ Δ' : SubCtx Γ) (σ : U) → Set where
  Var :  (x : Ref σ ⌊ Δ ⌋) →
         LiveExpr Δ (sing Δ x) σ
  Plus : LiveExpr Δ Δ₁ NAT →
         LiveExpr Δ Δ₂ NAT →
         LiveExpr Δ (Δ₁ ∪ Δ₂) NAT
  ...
```

## Live variable analysis

* we can relate ordinary and annotated expressions

```agda
analyse : Expr ⌊ Δ ⌋ σ → Σ[ Δ' ∈ SubCtx Γ ]
                         LiveExpr Δ Δ' σ

forget : LiveExpr Δ Δ' σ → Expr ⌊ Δ ⌋ σ
```

* reasonable requirement: `forget ∘ analyse ≡ id`

## Dead binding elimination

```
dbe : LiveExpr Δ Δ' σ → Expr ⌊ Δ' ⌋ σ
```

* on a `Let`, it branches on whether the variable is live

* if not, just remove the binding


# Correctness

## Optimised semantics

* to split up the correctness proofs, we give semantics `evalLive` for annotated expressions

  * on a `Let`, it also branches
  * generalisation helps: accept any `Env ⌊ Δᵤ ⌋` with `Δ' ⊆ Δᵤ`

## Correctness

* the goal: `eval ∘ dbe ∘ analyse ≡ eval`

* for the analysis, we know that: `forget ∘ analyse ≡ id`

* so it is sufficient to do two straight-forward proofs:

  * `eval ∘ dbe ≡ evalLive`
  * `evalLive ≡ eval ∘ forget`

* both only require small lemmas for the `Let` case


# What's next?

* extend the language

  * lambda abstractions
  * recursive bindings

* implement more optimisations

  * *strong* live variable analysis
  * moving bindings up or down in the syntax tree
  * common subexpression elimination

* identify patterns, generalise the approach


## {.standout}

<https://github.com/mheinzel/correct-optimisations>

I'm looking forward to your feedback!
