---
author: Matthias Heinzel
title: Analysis and Transformation of Intrinsically Typed Syntax
subtitle: Master's Thesis
institute: Utrecht University
theme: metropolis
---

# $\lambda$-calculus
  - well studied notion of computation
  - we add let-bindings, Booleans, integers and addition

  $$ \text{(definition)} $$

# Analysis and Transformation
  - fundamental part of compilers
  - we focus on those dealing with bindings

  $$ \text{(example with opportunities for inlining, DBE, moving binding)} $$

## Dead Binding Elimination
  - remove dead (unused) bindings
  - which bindings exactly are dead?

  $$ \text{(example with binding only used in other dead declaration)} $$

## Live Variable Analysis
  - collect live variables, bottom up
  - for *strongly* live variable analysis, at let-binding:
    - only consider declaration if its binding is live

  $$ \text{(example with binding only used in other dead declaration)} $$

# Variable Representations
  - so far, we looked at it conceptually
  - but how does a compiler represent variables?

## Named Representation
  - what we have done so far, just use strings
  - pitfall: $\alpha$-equivalence
  - pitfall: shadowing, variable capture
    - GHC adopts Barendregt convention, creates "the rapier"
      - relies on invariants upheld by convention
    - Dex reports many bugs, creates "the foil"
      - uses types to "make it harder to poke your eye out"

## de Bruijn Representation
  - no names, de Bruijn indices are natural numbers
  - *relative* reference to binding ($0$ = innermost)
  - $\alpha$-equivalence for free!
  - pitfall: need to rename when adding/removing bindings

  $$ \text{(example with dead binding)} $$

## Other Representations
  - co-de-Bruijn
  - higher-order abstract syntax (HOAS)
  - combinations of multiple techniques
  - ... ^[<http://jesper.sikanda.be/posts/1001-syntax-representations.html>]

# Intrinsically Typed de Bruijn Representation

[comment]: # start showing Agda code (similar to Haskell!)
[comment]: # work towards it, motivate design

## Naive Syntax
  ```agda
    data Expr : Set where
      Var  : Nat → Expr
      App  : Expr → Expr → Expr
      Lam  : Expr → Expr
      Let  : Expr → Expr → Expr
      Num  : Int → Expr
      Bln  : Bool → Expr
      Plus : Expr → Expr → Expr
  ```

  - What about `Plus (Bln False) (Var 42)`?
  - error-prone, evaluation is partial

## Sorts
  - solution: index expressions by their sort (type of their result)

  ```agda
    data U : Set where
      _=>_ : U → U → U
      BOOL : U
      NAT  : U
  ```

## Sorts
  ```agda
    data Expr : U → Set where
      Var  : Nat → Expr σ
      App  : Expr (σ => τ) → Expr σ → Expr τ
      Lam  : Expr τ → Expr (σ => τ)
      Let  : Expr σ → Expr τ → Expr τ
      Val  : ⟦ σ ⟧ → Expr σ
      Plus : Expr NAT → Expr NAT → Expr NAT
  ```

  - helps, but variables are still not safe!

## Context
  - always consider which variables are in scope

  ```agda
    Ctx = List U

    data Ref (σ : U) : Ctx → Set where
      Top  : Ref σ (σ ∷ Γ)
      Pop  : Ref σ Γ → Ref σ (τ ∷ Γ)
  ```

  - a reference is both:
    - an index (unary numbers)
    - proof that a fitting binding is in scope

## Intrinsically Typed Syntax
  ```agda
    data Expr : U → Ctx → Set where
      Var  : Ref σ Γ → Expr σ Γ
      App  : Expr (σ => τ) Γ → Expr σ Γ → Expr τ Γ
      Lam  : Expr τ (σ ∷ Γ) → Expr (σ => τ) Γ
      Let  : Expr σ Γ → Expr τ (σ ∷ Γ) → Expr τ Γ
      Val  : ⟦ σ ⟧ → Expr σ Γ
      Plus : Expr NAT Γ → Expr NAT Γ → Expr NAT Γ
  ```

  - *intrinsically* typed
  - well-typed and well-scoped *by construction*!

## Variable Liveness

## Thinnings

# Intrinsically Typed co-de-Bruijn Representation

# Generic co-de-Bruijn Representation


## {.standout}

<https://github.com/mheinzel/correct-optimisations>
