---
author: Matthias Heinzel
title: Analysis and Transformation of Intrinsically Typed Syntax
subtitle: Master's Thesis
institute: Utrecht University
theme: metropolis
---

[comment]: # This is probably too much content for a 30-45 min talk, but we can still cut later.
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

## Dead Binding Elimination (DBE)
  - remove dead (unused) bindings
  - which bindings exactly are dead?

  $$ \text{(example with binding only used in other dead declaration)} $$

## Live Variable Analysis (LVA)
  - collect live variables, bottom up
  - for *strongly* live variable analysis, at let-binding:
    - only consider declaration if its binding is live

  $$ \text{(example with binding only used in other dead declaration)} $$


# Variable Representations

::: notes
So far, we looked at it conceptually, but how does a compiler represent variables?
:::

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

::: notes
- start showing Agda code (looks similar to Haskell, but total!)
- work towards it, motivate design
- no need to understand full code
- focus on signatures and things I highlight!
:::

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
    foo = Lam (Plus (Var Top) (Var (Pop Top)))
  ```

## Variable Liveness
  ```agda
    foo : Expr (NAT ⇒ NAT) [ NAT , NAT ]
    foo = Lam (Plus (Var Top) (Var (Pop Top)))
  ```

  - here: only the innermost binding *outside* of `foo` is live
  - but how to represent that fact in Agda?
    - `[ NAT ]` is live context, but which variable does that refer to?
    - conceptually: for each variable, do we keep or drop it?

## Thinnings
  - we use *thinnings* (order-preserving embeddings) from source into target

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

::: notes
There are many other options, but thinnings are generally useful and have nice operations.
:::

## Thinnings, Categorically

::: notes
I won't say much, but there is a rich categorical structure (see McBride).
For example, category with thinnings as morphisms between contexts.
:::

  ```agda
    _ₒ_ : Γ₁ ⊑ Γ₂ → Γ₂ ⊑ Γ₃ → Γ₁ ⊑ Γ₃
  ```

  ```
    a ------ a     a ------ a     a ------ a
                ₒ          - b  =         - b
           - c     c ------ c            - c
  ```

:::::: columns

::: {.column width=25%}
  ```agda
    oi : Γ ⊑ Γ
  ```

  ```
    a ------ a
    b ------ b
    c ------ c
  ```
:::

::: {.column width=65%}
  ```agda
    law-ₒoi : θ ₒ oi ≡ θ
    law-oiₒ : oi ₒ θ ≡ θ
    law-ₒₒ : θ ₒ (ϕ ₒ ψ) ≡ (θ ₒ ϕ) ₒ ψ
  ```
:::

::::::

::: notes
And many other useful operations we will see later.
:::

## Dead Binding Elimination (direct approach)
  - first, we attempt DBE in a single pass
  - return result in *some* live context
    - with thinning into original context `Γ`

  ```agda
    dbe : Expr σ Γ → Expr σ ⇑ Γ
  ```

. . .

  ```agda
    record _⇑_ (T : List I → Set) (Γ : List I) : Set where
      constructor _↑_
      field
        {support} : List I
        thing : T support
        thinning : support ⊑ Γ
  ```

## Dead Binding Elimination (direct approach)

::: notes
Expression structure will not change much:
Remove some bindings, but then also need to rename variables.
:::

  - removing bindings changes context, makes renaming necessary
  - we will do it based on thinnings

  ```agda
    rename-Ref  : Δ ⊑ Γ → Ref σ Δ  → Ref σ Γ

    rename-Expr : Δ ⊑ Γ → Expr σ Δ → Expr σ Γ
  ```

## Dead Binding Elimination (direct approach)
  ```agda
    dbe (Val v) =
      Val v ↑ oe
  ```

  - in values, no variable is live
  - empty thinning

  ```agda
    oe : [] ⊑ Γ
  ```

::: notes
Empty context is initial object!
:::

## Dead Binding Elimination (direct approach)
  ```agda
    dbe (Var x) =
      Var Top ↑ o-Ref x
  ```

  - variables have exactly one live variable
  - thinnings from singleton context are isomorphic to references

  ```agda
    o-Ref : Ref τ Γ → (τ ∷ []) ⊑ Γ
  ```

## Dead Binding Elimination (direct approach)
  ```agda
    dbe (App e₁ e₂) =
      let e₁' ↑ θ₁ = dbe e₁  -- θ₁ : Δ₁ ⊑ Γ
          e₂' ↑ θ₂ = dbe e₂  -- θ₂ : Δ₂ ⊑ Γ
      in App (rename-Expr (un-∪₁ θ₁ θ₂) e₁')
             (rename-Expr (un-∪₂ θ₁ θ₂) e₂')
         ↑ (θ₁ ∪ θ₂)
  ```

  - find minimal live context (if θ₁ or θ₂ keeps, keep!)
  - rename subexpressions into that context

  ```agda
    _∪_   : ∀ θ₁ θ₂ → ∪-domain θ₁ θ₂ ⊑ Γ
    un-∪₁ : ∀ θ₁ θ₂ → Δ₁ ⊑ ∪-domain θ₁ θ₂
    un-∪₂ : ∀ θ₁ θ₂ → Δ₂ ⊑ ∪-domain θ₁ θ₂
  ```

## Dead Binding Elimination (direct approach)
  ```agda
    dbe (Lam e₁) =
      let e₁' ↑ θ = dbe e₁  -- θ : Δ ⊑ (σ ∷ Γ)
      in Lam (rename-Expr (un-pop θ) e₁') ↑ pop θ
  ```

  - pop off the top element
    - corresponding to variable bound by `Lam`

  ```agda
    pop    : ∀ θ → pop-domain θ ⊑ Γ
    un-pop : ∀ θ → Δ ⊑ (σ ∷ pop-domain θ)
  ```

## Dead Binding Elimination (direct approach)
  ```agda
    dbe (Let e₁ e₂) with dbe e₁ | dbe e₂
    ... | e₁' ↑ θ₁  | e₂' ↑ o' θ₂ =
      e₂' ↑ θ₂
    ... | e₁' ↑ θ₁  | e₂' ↑ os θ₂ =
      Let (rename-Expr (un-∪₁ θ₁ θ₂) e₁')
          (rename-Expr (os (un-∪₂ θ₁ θ₂)) e₂')
      ↑ (θ₁ ∪ θ₂)
  ```

  - most interesting case
  - look at live context of transformed subexpressions:
    - if `o'`, eliminate dead binding!
    - if `os`, we cannot remove it (Agda won't let us)
  - this corresponds to *strongly* live variable analysis

## Dead Binding Elimination (direct approach)
  ```agda
    dbe (Plus e₁ e₂) =
      let e₁' ↑ θ₁ = dbe e₁  -- θ₁ : Δ₁ ⊑ Γ
          e₂' ↑ θ₂ = dbe e₂  -- θ₂ : Δ₂ ⊑ Γ
      in Plus (rename-Expr (un-∪₁ θ₁ θ₂) e₁')
              (rename-Expr (un-∪₂ θ₁ θ₂) e₂')
         ↑ (θ₁ ∪ θ₂)
  ```

  - identical to `App`
  - this time, note that repeated renaming is inefficient
  - hard to avoid
    - in which context do we need the transformed subexpressions?
    - we can query it upfront, but that's also quadratic
    - caching?

## Dead Binding Elimination (direct approach)
  - intrinsically typed syntax enforces some invariants
  - correctness proof is stronger, but what does "correctness" mean?

. . .

  - here: preservation of semantics (based on `eval`)

  ```agda
    project-Env : Δ ⊑ Γ → Env Γ → Env Δ

    dbe-correct :
      (e : Expr σ Γ) (env : Env Γ) →
      let e' ↑ θ = dbe e
      in eval e' (project-Env θ env) ≡ eval e env
  ```

::: notes
There are many options, e.g. using `rename-Expr`, but in this case proof is similar.
:::

## Dead Binding Elimination (direct approach)
  ```agda
    dbe-correct :
      (e : Expr σ Γ) (env : Env Γ) →
      let e' ↑ θ = dbe e
      in eval e' (project-Env θ env) ≡ eval e env
  ```

  - equality on result of evaluation is simple, but:
    - only works for total language (e.g. no unbounded recursion)
    - values include functions, so we need extensional equality

  ```agda
    postulate
      extensionality :
        {S : Set} {T : S → Set} (f g : (x : S) → T x) →
        (∀ x → f x ≡ g x) → f ≡ g
  ```

## Dead Binding Elimination (direct approach)
  ```agda
    dbe-correct :
      (e : Expr σ Γ) (env : Env Γ) →
      let e' ↑ θ = dbe e
      in eval e' (project-Env θ env) ≡ eval e env
  ```

  - proof by structural induction
  - requires laws about evaluation, renaming, environment projection, operations on thinnings, ...

## Dead Binding Elimination (direct approach) {frameoptions="shrink"}
  ```agda
    dbe-correct (Lam e₁) env =
      let e₁' ↑ θ₁ = dbe e₁
      in extensionality _ _ λ v →
          eval (rename-Expr (un-pop θ₁) e₁') (project-Env (os (pop θ₁)) (Cons v env))
        ≡⟨ ... ⟩
          eval e₁' (project-Env (un-pop θ₁) (project-Env (os (pop θ₁)) (Cons v env)))
        ≡⟨ ... ⟩
          eval e₁' (project-Env (un-pop θ₁ ₒ os (pop θ₁)) (Cons v env))
        ≡⟨ ... ⟩
          eval e₁' (project-Env θ₁ (Cons v env))
        ≡⟨ dbe-correct e₁ (Cons v env) ⟩
          eval e₁ (Cons v env)
        ∎
  ```

  - binary constructors similarly with `_∪_` (for each subexpression)
  - for `Let`, distinguish cases again

  ```agda
    dbe-correct (Let e₁ e₂) env with dbe e₁ | dbe e₂ | dbe-correct e₁ | dbe-correct e₂
    ... | e₁' ↑ θ₁ | e₂' ↑ o' θ₂ | h₁ | h₂ =
      h₂ (Cons (eval e₁ env) env)
    ... | e₁' ↑ θ₁ | e₂' ↑ os θ₂ | h₁ | h₂ =
      ...  -- long
  ```

[comment]: # TODO: Make this look nicer, e.g. only shrink the code block?


## Dead Binding Elimination (using annotations)
  TODO: continue


# Intrinsically Typed co-de-Bruijn Representation


# Generic co-de-Bruijn Representation


# Other Transformations

## Let-sinking
  - (optional, can be skipped if low on time)
  - (just a short glimpse, showing segmented context and thinnings)


# Discussion


## {.standout}

<https://github.com/mheinzel/correct-optimisations>
