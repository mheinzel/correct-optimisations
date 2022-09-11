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


# What's next?

* extend the language

  * lambda abstractions
  * recursive bindings

* implement more optimisations

  * moving bindings around in the syntax tree
  * common subexpression elimination

* identify patterns, generalise approach


## {.standout}

<https://github.com/mheinzel/correct-optimisations>

I'm looking forward to your feedback!
