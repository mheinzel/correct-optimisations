---
author: Matthias Heinzel
title: Analysis and Transformation of Intrinsically Typed Syntax
subtitle: Master's Thesis
institute: Utrecht University
theme: metropolis
---

[comment]: # This is probably too much content for a 30-45 min talk, but we can still cut later.
[comment]: # Audience does not need to understand full code. Focus on signatures and things I highlight.
[comment]: # TODO: Fix alignment, e.g. by setting math symbol width to agree with monospace font.


# Analysis and Transformation

## Expression Language
  $$ \text{(definition)} $$

  - based on $\lambda$-calculus
    - well studied notion of computation
  - we add let-bindings, Booleans, integers and addition

## Analysis and Transformation

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

[comment]: # start showing Agda code (looks similar to Haskell, but total!)
[comment]: # work towards it, motivate design

## Naive Syntax
  ```agda
    data Expr : Set where
      Var  : Nat → Expr
      App  : Expr → Expr → Expr
      Lam  : Expr → Expr
      Let  : Expr → Expr → Expr
      Num  : Nat → Expr
      Bln  : Bool → Expr
      Plus : Expr → Expr → Expr
  ```

  - What about `Plus (Bln False) (Var 42)`?
  - error-prone, evaluation is partial

## Sorts
  - solution: index expressions by their sort (type of their result)

  ```agda
    data U : Set where
      _⇒_ : U → U → U
      BOOL : U
      NAT  : U

    ⟦_⟧ : U → Set
    ⟦ σ ⇒ τ ⟧ = ⟦ σ ⟧ → ⟦ τ ⟧
    ⟦ BOOL ⟧   = Bool
    ⟦ NAT ⟧    = Nat
  ```

## Sorts
  ```agda
    data Expr : U → Set where
      Var  : Nat → Expr σ
      App  : Expr (σ ⇒ τ) → Expr σ → Expr τ
      Lam  : Expr τ → Expr (σ ⇒ τ)
      Let  : Expr σ → Expr τ → Expr τ
      Val  : ⟦ σ ⟧ → Expr σ
      Plus : Expr NAT → Expr NAT → Expr NAT
  ```

  - helps, e.g. addition now only on numbers
  - but variables are still not safe!

## Context
  - always consider *context*, i.e. which variables are in scope

  ```agda
    Ctx = List U

    data Ref (σ : U) : Ctx → Set where
      Top  : Ref σ (σ :: Γ)
      Pop  : Ref σ Γ → Ref σ (τ :: Γ)
  ```

  - a reference is both:
    - an index (unary numbers)
    - proof that the index refers to a suitable variable in scope

## Intrinsically Typed Syntax
  ```agda
    data Expr : U → Ctx → Set where
      Var  : Ref σ Γ → Expr σ Γ
      App  : Expr (σ ⇒ τ) Γ → Expr σ Γ → Expr τ Γ
      Lam  : Expr τ (σ :: Γ) → Expr (σ ⇒ τ) Γ
      Let  : Expr σ Γ → Expr τ (σ :: Γ) → Expr τ Γ
      Val  : ⟦ σ ⟧ → Expr σ Γ
      Plus : Expr NAT Γ → Expr NAT Γ → Expr NAT Γ
  ```

  - *intrinsically* typed
  - well-typed and well-scoped *by construction*!

## Evaluation
  - during evaluation, we have an *environment*

    (a value for each variable in the context)

  ```agda
    data Env : List I → Set where
      Nil   : Env []
      Cons  : ⟦ σ ⟧ → Env Γ → Env (σ :: Γ)

    eval : Expr σ Γ → Env Γ → ⟦ σ ⟧
  ```

## Evaluation
  ```agda
    data Ref (σ : U) : Ctx → Set where
      Top  : Ref σ (σ :: Γ)
      Pop  : Ref σ Γ → Ref σ (τ :: Γ)

    data Env : List I → Set where
      Nil   : Env []
      Cons  : ⟦ σ ⟧ → Env Γ → Env (σ :: Γ)

    lookup : Ref σ Γ → Env Γ → ⟦ σ ⟧
    lookup Top      (Cons v env)   = v
    lookup (Pop i)  (Cons v env)   = lookup i env
  ```

  - lookup is total

## Intrinsically Typed Syntax
  ```agda
    eval : Expr σ Γ → Env Γ → ⟦ σ ⟧
    eval (Var x)      env = lookup x env
    eval (App e₁ e₂)  env = eval e₁ env (eval e₂ env)
    eval (Lam e₁)     env = λ v → eval e₁ (Cons v env)
    eval (Let e₁ e₂)  env = eval e₂ (Cons (eval e₁ env) env)
    eval (Val v)      env = v
    eval (Plus e₁ e₂) env = eval e₁ env + eval e₂ env
  ```

  - evaluation is total

## Variable Liveness
  - we want to talk about the *live* context (result of LVA)

  ```agda
    foo : Expr (NAT ⇒ NAT) [ NAT , NAT ]
    foo = Lam (Plus (Val 42) (Var (Pop Top)))
  ```

  - here: `[ NAT ]`, but which variable does that refer to?
    - live context alone is ambiguous!
  - also, we need operations (popping top variable, union)

## Thinnings
  - we use *thinnings* (order-preserving embeddings)

  ```agda
    data _⊑_ : List I → List I → Set where
      o' : Δ ⊑ Γ →       Δ  ⊑ (τ :: Γ)  -- drop
      os : Δ ⊑ Γ → (τ :: Δ) ⊑ (τ :: Γ)  -- keep
      oz : [] ⊑ []                         -- done
  ```

  ```
    a ------ a      os
           - b      o'
    c ------ c      os
                    oz
  ```

  ```agda
    os (o' (os oz)) : [ a , c ] ⊑ [ a , b , c ]
  ```

## Thinnings (composition)
  ```agda
    _ₒ_ : Γ₁ ⊑ Γ₂ → Γ₂ ⊑ Γ₃ → Γ₁ ⊑ Γ₃
  ```

  ```
    a ------ a     a ------ a     a ------ a
                ₒ         - b  =         - b
           - c     c ------ c            - c
  ```

  [comment]: # corresponds to (os (o' oz) ₒ os (o' (os oz)) = os (o' (o' oz)) : (a :: []) ⊑ (a :: b :: c :: []))

# Intrinsically Typed co-de-Bruijn Representation

# Generic co-de-Bruijn Representation

# Other Transformations

## Let-sinking

# Discussion


## {.standout}

<https://github.com/mheinzel/correct-optimisations>
