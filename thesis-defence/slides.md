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
  \begin{align*}
    P, Q ::=&\ x
    \\ \big|&\ P\ Q
    \\ \big|&\ \lambda x.\ P
    \\ \big|&\ \textbf{let } x = P \textbf{ in } Q
    \\ \big|&\ v
    \\ \big|&\ P + Q
  \end{align*}

  - based on $\lambda$-calculus
    - well studied notion of computation
  - we add let-bindings, Booleans, integers and addition

## Analysis and Transformation
  - fundamental part of compilers
  - we focus on those dealing with bindings

  \begin{align*}
    &\textbf{let } f = \lambda x.\ (x + 1) \textbf{ in} \\
    &\ \ \textbf{let } y = 42 \textbf{ in}         \\
    &\ \ \ \ \textbf{let } z = a + a \textbf{ in}    \\
    &\ \ \ \ \ \ f\ 1 + (z + z)
  \end{align*}

## Dead Binding Elimination (DBE)
  - remove dead (unused) bindings
  - which bindings exactly are dead?
    - $x$ occurs in its body, but only in declaration of $y$

  \begin{align*}
    &\textbf{let } x = 42 \textbf{ in}  \\
    &\ \ \textbf{let } y = x \textbf{ in} \\
    &\ \ \ \ 1337
  \end{align*}

## Live Variable Analysis (LVA)
  - collect live variables, bottom up
  - for *strongly* live variable analysis, at let-binding:
    - only consider declaration if its binding is live

  \begin{align*}
    &\textbf{let } x = 42 \textbf{ in}  \\
    &\ \ \textbf{let } y = x \textbf{ in} \\
    &\ \ \ \ 1337
  \end{align*}


# Variable Representations

::: notes
So far, we looked at it conceptually, but how does a compiler represent variables?
:::

## Named Representation
  - what we have done so far, just use strings
  - pitfall: $\alpha$-equivalence
    - is $\lambda x.\ x$ equivalent to $\lambda x.\ y$?
  - pitfall: shadowing, variable capture
    - e.g. inlining $y$ in $\textbf{let } y = x + 1 \textbf{ in } \lambda x.\ (x + y)$
    - GHC adopts Barendregt convention, creates *the rapier*
      - relies on invariants upheld by convention
    - Dex reports many bugs, creates *the foil*
      - uses types to "make it harder to poke your eye out"

## de Bruijn Representation
  - no names, de Bruijn indices are natural numbers
  - *relative* reference to binding ($0$ = innermost)
  - $\alpha$-equivalence for free!
  - pitfall: need to rename when adding/removing bindings

  \begin{align*}
    &\textbf{let } 42 \textbf{ in }     \\
    &\ \ \textbf{let } 99 \textbf{ in } \\
    &\ \ \ \ \langle 1 \rangle
  \end{align*}

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

## Intrinsically Typed de Bruijn Representation
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

## Intrinsically Typed de Bruijn Representation
  - evaluation requires an *environment*

    (a value for each variable in the context)

  ```agda
    data Env : List I → Set where
      Nil   : Env []
      Cons  : ⟦ σ ⟧ → Env Γ → Env (σ :: Γ)

    eval : Expr σ Γ → Env Γ → ⟦ σ ⟧
  ```

## Intrinsically Typed de Bruijn Representation
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

## Intrinsically Typed de Bruijn Representation
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


## Dead Binding Elimination (annotated)
  - repeated renaming can be avoided by first running analysis
    - so we know upfront which which context to use
  - common in compilers
  - annotated syntax tree
    - again using thinnings, constructed as before
    - for `{θ : Δ ⊑ Γ}`, we have `LiveExpr σ θ`

## Dead Binding Elimination (annotated) {frameoptions="shrink"}
  ```agda
    data LiveExpr {Γ : Ctx} : {Δ : Ctx} → U → Δ ⊑ Γ → Set where
      Var :
        (x : Ref σ Γ) →
        LiveExpr σ (o-Ref x)
      App :
        {θ₁ : Δ₁ ⊑ Γ} {θ₂ : Δ₂ ⊑ Γ} →
        LiveExpr (σ ⇒ τ) θ₁ →
        LiveExpr σ θ₂ →
        LiveExpr τ (θ₁ ∪ θ₂)
      Lam :
        {θ : Δ ⊑ (σ ∷ Γ)} →
        LiveExpr τ θ →
        LiveExpr (σ ⇒ τ) (pop θ)
      Let : ...
      Val : ...
      Plus : ...
  ```

## Dead Binding Elimination (annotated)
  ```agda
    Let :
      {θ₁ : Δ₁ ⊑ Γ} {θ₂ : Δ₂ ⊑ (σ ∷ Γ)} →
      LiveExpr σ θ₁ → LiveExpr τ θ₂ →
      LiveExpr τ (combine θ₁ θ₂)
  ```

  - in direct approach, handled in two cases
  - for analysis, we have a choice:

    1. treat `Let` as an immediately `App`lied  `Lam`

        ```agda
          combine θ₁ θ₂ = θ₁ ∪ pop θ₂
        ```

    2. custom operation for *strongly* live variable analysis

        ```agda
          combine θ₁ (o' θ₂) = θ₂
          combine θ₁ (os θ₂) = θ₁ ∪ θ₂
        ```

        (only consider declaration if binding is live!)

## Dead Binding Elimination (annotated)
  - now, construct an annotated expression

  ```agda
    analyse :
      Expr σ Γ →
      Σ[ Δ ∈ Ctx ]
        Σ[ θ ∈ (Δ ⊑ Γ) ]
          LiveExpr σ θ
  ```

  - annotations can also be forgotten again

  ```agda
    forget : {θ : Δ ⊑ Γ} → LiveExpr σ θ → Expr σ Γ
  ```

## Dead Binding Elimination (annotated)
  - implementation does not surprise

  ```agda
    analyse (Var {σ} x) =
      σ ∷ [] , o-Ref x , Var x
    analyse (App e₁ e₂) =
      let Δ₁ , θ₁ , le₁ = analyse e₁
          Δ₂ , θ₂ , le₂ = analyse e₂
      In ∪-domain θ₁ θ₂ , (θ₁ ∪ θ₂) , App le₁ le₂
    ...
  ```

## Dead Binding Elimination (annotated)
  - after analysis, do transformation
  - caller can choose the context (but at least live context)
  - together, same type signature as direct approach

  ```agda
    transform : {θ : Δ ⊑ Γ} →
      LiveExpr σ θ → Δ ⊑ Γ' → Expr σ Γ'

    dbe : Expr σ Γ → Expr σ ⇑ Γ
    dbe e =
      let Δ , θ , le = analyse e
      in transform le oi ↑ θ
  ```

## Dead Binding Elimination (annotated)
  - no renaming anymore, directly choose desired context

  ```agda
    transform (Var x) θ' = Var (ref-o θ')
    transform (App {θ₁ = θ₁} {θ₂ = θ₂} e₁ e₂) θ' =
      App (transform e₁ (un-∪₁ θ₁ θ₂ ₒ θ'))
          (transform e₂ (un-∪₂ θ₁ θ₂ ₒ θ'))
    transform (Lam {θ = θ} e₁) θ' =
      Lam (transform e₁ (un-pop θ ₒ os θ'))
    ...
  ```

## Dead Binding Elimination (annotated)
  - for `Let`, again split on thinning
  ```agda
    ...
    transform (Let {θ₁ = θ₁} {θ₂ = o' θ₂} e₁ e₂) θ' =
      transform e₂ (un-∪₂ θ₁ θ₂  ₒ θ')
    transform (Let {θ₁ = θ₁} {θ₂ = os θ₂} e₁ e₂) θ' =
      Let (transform e₁ (un-∪₁ θ₁ θ₂ ₒ θ'))
          (transform e₂ (os (un-∪₂ θ₁ θ₂ ₒ θ')))
    ...
  ```

## Dead Binding Elimination (annotated)
### Correctness
  - TODO (first decide on phrasing of specification)

## Intrinsically Typed de Bruijn Representation
### Discussion

::: notes
Discussion also includes insight from other transformations.
:::

  - analysis requires an extra pass, but is useful
  - currently, transformations get rid of annotations
    - maintaining them would require more effort
  - `LiveExpr` is indexed by two contexts, which seems redundant


# Intrinsically Typed co-de-Bruijn Representation
  - "dual" to de Bruijn indices, due to Conor McBride:
    - de Bruijn indices pick from the context "as late as possible"
    - co-de-Bruijn gets rid of bindings "as early as possible"
      - using thinnings
  - observation: expressions indexed by their (weakly) live context

## Intrinsically Typed co-de-Bruijn Representation
  - how to deal with multiple subexpressions?
  - basically, as with `LiveExpr` we need:
    - a suitable overall context `Γ` (like `_∪_`)
    - for each subexpression, a thinning into `Γ`
  - building block: *relevant pair*

## Intrinsically Typed co-de-Bruijn Representation
  ```agda
    record _×ᴿ_ (S T : List I → Set) (Γ : List I) : Set where
      constructor pairᴿ
      field
        outl  : S ⇑ Γ    -- S Δ₁ and Δ₁ ⊑ Γ
        outr  : T ⇑ Γ    -- T Δ₂ and Δ₂ ⊑ Γ
        cover : Cover (thinning outl) (thinning outr)
  ```

  - usage: `(Expr (σ ⇒ τ) ×ᴿ Expr σ) Γ`

. . .

  - what is a cover?
    - we just have some overall context `Γ`
    - cover ensures that `Γ` is *relevant*, as small as possible

## Intrinsically Typed co-de-Bruijn Representation
  - each element of `Γ` needs to be relevant
  - i.e. at least one thinning keeps it

  ```agda
    data Cover : Γ₁ ⊑ Γ → Γ₂ ⊑ Γ → Set where
      c's : Cover θ₁ θ₂ → Cover (o' θ₁) (os θ₂)
      cs' : Cover θ₁ θ₂ → Cover (os θ₁) (o' θ₂)
      css : Cover θ₁ θ₂ → Cover (os θ₁) (os θ₂)
      czz : Cover oz oz
  ```

## Intrinsically Typed co-de-Bruijn Representation
  - how to deal with bindings?
  - here, we allow multiple simultaneous bindings `Γ'`
    - requires talking about context concatenation (replaces `pop`)

. . .

  - new construct `(Γ' ⊢ T) Γ`, consists of two things:

  ```agda
    ψ : Δ' ⊑ Γ'     -- which new variables are used?
    t : T (Δ' ++ Γ)  -- used variables added to context
  ```

## Intrinsically Typed co-de-Bruijn Representation
  ```agda
    record _⊢_ (Γ' : List I)
               (T : List I → Set)
               (Γ : List I) : Set where
      constructor _\\_
      field
        {used} : List I
        thinning : used ⊑ Γ'
        thing : T (used ++ Γ)
  ```

::: notes
Just for reference, skip this slide quickly.
:::

## Intrinsically Typed co-de-Bruijn Representation

  ```agda
    data Expr : U → Ctx → Set where
      Var :
        Expr σ (σ ∷ [])
      App :
        (Expr (σ ⇒ τ) ×ᴿ Expr σ) Γ →
        Expr τ Γ
      Lam :
        ((σ ∷ []) ⊢ Expr τ) Γ →
        Expr (σ ⇒ τ) Γ
      Let :
        (Expr σ ×ᴿ ((σ ∷ []) ⊢ Expr τ)) Γ →
        Expr τ Γ
      ...
  ```

[comment]: # Could also talk about evaluation briefly. Precursor to `relax`, accumulating thinning.

## Conversion From Co-de-Bruijn Syntax
  - take all those thinnings at the nodes
  - only use them at the latest moment, variables

  ```agda
    relax : Γ' ⊑ Γ → Expr σ Γ' → DeBruijn.Expr σ Γ
  ```

  - keep composing the thinning
    - how do we deal with bindings (`ψ \\ e`)?

## Concatenation of Thinnings
  - thinnings have monoidal structure

  ```agda
    _++⊑_ :
      Δ₁ ⊑ Γ₁ → Δ₂ ⊑ Γ₂ →
      (Δ₁ ++ Δ₂) ⊑ (Γ₁ ++ Γ₂)
  ```

  - extends to covers

  ```agda
    _++ᶜ_ :
      Cover θ₁ θ₂ → Cover ϕ₁ ϕ₂ →
      Cover (θ₁ ++⊑ ϕ₁) (θ₂ ++⊑ ϕ₂)
  ```

[comment]: # TODO: Not sure if this is actually needed for the presentation.

## Conversion From Co-de-Bruijn Syntax
  ```agda
    relax : Γ' ⊑ Γ → Expr σ Γ' → DeBruijn.Expr σ Γ
    relax θ Var =
      -- eventually turn thinning into Ref
      DeBruijn.Var (ref-o θ)
    relax θ (App (pairᴿ (e₁ ↑ ϕ₁) (e₂ ↑ ϕ₂) cover)) =
      DeBruijn.App (relax (ϕ₁ ₒ θ) e₁) (relax (ϕ₂ ₒ θ) e₂)
    relax θ (Lam (ψ \\ e)) =
      DeBruijn.Lam (relax (ψ ++⊑ θ) e)
    relax θ (Let (pairᴿ (e₁ ↑ θ₁) ((ψ \\ e₂) ↑ θ₂) c)) =
      -- combination of product and binding
      DeBruijn.Let (relax (θ₁ ₒ θ) e₁) (relax (ψ ++⊑ (θ₂ ₒ θ)) e₂)
    ...
  ```

## Conversion To Co-de-Bruijn Syntax
  - other direction is harder
  - we need to find all these thinnings
  - resulting live context not known upfront, use `_⇑_`

  ```agda
    tighten : DeBruijn.Expr σ Γ → Expr σ ⇑ Γ
  ```

## Conversion To Co-de-Bruijn Syntax
  ```agda
    _,ᴿ_ : S ⇑ Γ → T ⇑ Γ → (S ×ᴿ T) ⇑ Γ
  ```

  - implementation similar to `_∪_`, but also constructs cover

  ```agda
    _\\ᴿ_ : (Γ' : List I) → T ⇑ (Γ' ++ Γ) → (Γ' ⊢ T) ⇑ Γ
  ```

  - relies on the fact that thinnings can be split

## Conversion To Co-de-Bruijn Syntax
  ```agda
    tighten : DeBruijn.Expr σ Γ → Expr σ ⇑ Γ
    tighten (DeBruijn.Var x) =
      Var ↑ o-Ref x
    tighten (DeBruijn.App e₁ e₂) =
      map⇑ App (tighten e₁ ,ᴿ tighten e₂)
    tighten (DeBruijn.Lam e) =
      map⇑ Lam ((_ ∷ []) \\ᴿ tighten e)
    tighten (DeBruijn.Let e₁ e₂) =
      map⇑ Let (tighten e₁ ,ᴿ ((_ ∷ []) \\ᴿ tighten e₂))
    ...
  ```

  ```agda
    -- map⇑ f (t ↑ θ) = f t ↑ θ
  ```

## Conversion To Co-de-Bruijn Syntax
  - also prove that conversion agrees with semantics

  ```agda
    relax-correct :
      (e : Expr τ Γ') (θ : Γ' ⊑ Γ) (env : Env Γ) →
      let e' = relax θ e
      in DeBruijn.eval e' env ≡ eval e θ env

    tighten-correct :
      (e : DeBruijn.Expr τ Γ) (env : Env Γ) →
      let e' ↑ θ' = tighten e
      in eval e' θ' env ≡ DeBruijn.eval e env
  ```

## Dead Binding Elimination (co-de-Bruijn)
  - co-de-Bruijn: all variables in the context must occur
  - but let-bindings can still be dead (`o' oz \\ e₂`)
    - easy to identify now
    - remove them!

. . .

  - this might make some (previously weakly live) bindings dead
    - context gets smaller

  ```agda
    dbe : Expr τ Γ → Expr τ ⇑ Γ
  ```

## Dead Binding Elimination (co-de-Bruijn)
  ```agda
    dbe : Expr τ Γ → Expr τ ⇑ Γ
    dbe Var =
      Var ↑ oi
    dbe (App (pairᴿ (e₁ ↑ ϕ₁) (e₂ ↑ ϕ₂) c)) =
      map⇑ App (thin⇑ ϕ₁ (dbe e₁) ,ᴿ thin⇑ ϕ₂ (dbe e₂))
    dbe (Lam (_\\_ {Γ'} ψ e)) =
      map⇑ (Lam ∘ map⊢ ψ) (Γ' \\ᴿ dbe e)
    ...
  ```

## Dead Binding Elimination (co-de-Bruijn)
  ```agda
    dbe (Let (pairᴿ (e₁ ↑ ϕ₁) ((o' oz \\ e₂) ↑ ϕ₂) c)) =
      thin⇑ ϕ₂ (dbe e₂)
    dbe (Let (pairᴿ (e₁ ↑ ϕ₁) ((os oz \\ e₂) ↑ ϕ₂) c)) =
      map⇑ Let
        (  thin⇑ ϕ₁ (dbe e₁)
        ,ᴿ thin⇑ ϕ₂ ((_ ∷ []) \\ᴿ dbe e₂)
        )
  ```

  - option 1: check liveness in input
  - binding might still become dead in dbe e₂
  - correspondes to *weakly* live variable analysis


## Dead Binding Elimination (co-de-Bruijn)
  ```agda
    Let? : (Expr σ ×ᴿ ((σ ∷ []) ⊢ Expr τ)) Γ → Expr τ ⇑ Γ
    Let?   (pairᴿ _ ((o' oz \\ e₂) ↑ θ₂) _) = e₂ ↑ θ₂
    Let? p@(pairᴿ _ ((os oz \\ _)  ↑ _)  _) = Let p ↑ oi

    dbe (Let (pairᴿ (e₁ ↑ ϕ₁) ((_\\_ {Γ'} ψ e₂) ↑ ϕ₂) c)) =
      bind⇑ Let?
        (  thin⇑ ϕ₁ (dbe e₁)
        ,ᴿ thin⇑ ϕ₂ (map⇑ (map⊢ ψ) (Γ' \\ᴿ dbe e₂))
        )
  ```

  - option 2: check liveness after recursive call
  - correspondes to *strongly* live variable analysis

## Dead Binding Elimination (co-de-Bruijn)
  - correctness, simplest statement:

  ```agda
    dbe-correct :
      (e : Expr τ Γ) (env : Env Γ) →
      let e' ↑ θ = dbe e
      in eval e' θ env ≡ eval e oi env
  ```

  - more flexibility for inductive step:

  ```agda
    dbe-correct :
      (e : Expr τ Δ) (env : Env Γ) (θ : Δ ⊑ Γ) →
      let e' ↑ θ' = dbe e
      in eval e' (θ' ₒ θ) env ≡ eval e θ env
  ```

## Dead Binding Elimination (co-de-Bruijn)
  - correctness proof requires extensive massaging
  - associativity of thinnings, identities, ...
  - laws about `project-Env` with `_ₒ_` and `oi`
  - laws about thinnings created by `_,ᴿ_`
  - `(θ ₒ θ') ++⊑ (ϕ ₒ ϕ') ≡ (θ ++⊑ ϕ) ₒ (θ' ++⊑ ϕ')`

  - for strong version:
    - `Let? p` semantically equivalent to `Let p`

## Intrinsically Typed co-de-Bruijn Representation
### Discussion
  - co-de-Bruijn representation keeps benefits of `LiveExpr`
    - liveness information available by design
  - some parts get simpler (just a single context)
  - some parts get more complicated (mainly proofs)
    - thinnings in result requires reasoning about them a lot
    - operations on thinnings get quite complex
  - building blocks (e.g. relevant pair) allow code reuse

::: notes
We can take this further!
:::


# Syntax-generic co-de-Bruijn Representation

::: notes
Some might know datatype-generic programming, e.g. `GHC.Generics`.
:::

## Syntax-generic Programming
  - based on work by Allais et al.
    - *A type- and scope-safe universe of syntaxes with binding: their semantics and proofs*
  - problem:
    - any time you define a language, you need common operations (renaming, substitution, ...) and laws about them
    - for these, languages need variables and bindings, the rest is noise
    - `Ctrl+C`, `Ctrl+V`?

## Syntax-generic Programming

::: notes
The code takes some time to understand in detail, so let's focus on the main ideas
:::

  - main idea:
    - define a datatype of syntax descriptions `Desc`
    - each `(d : Desc I)` describes a language of terms `Tm d σ Γ`
    - implement operations *once*, generically over descriptions

      ```agda
        foo : (d : Desc I) → Tm d σ Γ → ...
      ```

    - describe your language using `Desc`, get operations for free

. . .

  - authors created Agda package `generic-syntax`
    - we build on top of that
    - made it compile with recent Agda versions
      (had to remove sized types that were used to show termination)

## Syntax-generic Programming
  ```agda
    data Desc (I : Set) : Set₁ where
      `σ : (A : Set) → (A → Desc I)  → Desc I
      `X : List I → I → Desc I       → Desc I
      `∎ : I                         → Desc I
  ```

  - let's describe our language!

## Syntax-generic Programming
  ```agda
    `σ : (A : Set) → (A → Desc I) → Desc I
  ```

  - `` `σ`` is for storing data, e.g. which constructor it is
    - variables are assumed, no need to describe them

  ```agda
    data Tag : Set where
      `App  : U → U → Tag
      ...

    Lang : Desc U
    Lang = `σ Tag λ where
      (`App σ τ) → ...
      ...
  ```

## Syntax-generic Programming
  ```agda
    `X :        -- for recursion (subexpression)
      List I →  -- new variables bound in subexpression
      I →       -- sort of subexpression
      Desc I →  -- (continue)
      Desc I
    `∎ :        -- terminates description
      I →       -- sort
      Desc I
  ```

  ```agda
      (`App σ τ) → `X [] (σ ⇒ τ) (`X [] σ (`∎ τ))
      (`Lam σ τ) → `X (σ ∷ []) τ (`∎ (σ ⇒ τ))
      ...
  ```

## Syntax-generic Programming
  ```agda
    data Tag : Set where
      `App  : U → U → Tag
      `Lam  : U → U → Tag
      `Let  : U → U → Tag
      `Val  : U → Tag
      `Plus : Tag

    Lang : Desc U
    Lang = `σ Tag λ where
      (`App σ τ) → `X [] (σ ⇒ τ) (`X [] σ (`∎ τ))
      (`Lam σ τ) → `X (σ ∷ []) τ (`∎ (σ ⇒ τ))
      (`Let σ τ) → `X [] σ (`X (σ ∷ []) τ (`∎ τ))
      (`Val τ)   → `σ Core.⟦ τ ⟧ λ _ → `∎ τ
      `Plus      → `X [] NAT (`X [] NAT (`∎ NAT))
  ```

## Syntax-generic co-de-Bruijn Representation
  - we interpret into co-de-Bruijn terms instead
    - McBride had something similar, but for different `Desc` type

  ```agda
    _─Scoped : Set → Set₁
    I ─Scoped = I → List I → Set
  ```

  - something indexed by sort and context
    - e.g. `Expr : U ─Scoped`

## Syntax-generic co-de-Bruijn Representation
  ```agda
    data Tm (d : Desc I) : I ─Scoped where
      `var : Tm d i (i ∷ [])
      `con : ⟦ d ⟧ (Scope (Tm d)) i Γ → Tm d i Γ
  ```

  - terms always have variables
  - for the rest, interpret the description

## Syntax-generic co-de-Bruijn Representation
  ```agda
    Scope : I ─Scoped → List I → I ─Scoped
    Scope T    []      i = T i
    Scope T Δ@(_ ∷ _) i = Δ ⊢ T i
  ```

  - `Scope` roughly corresponds to bindings
  - empty scopes are very common, avoid trivial `[] ⊢_`

## Syntax-generic co-de-Bruijn Representation
  ```agda
    ⟦_⟧ : Desc I → (List I → I ─Scoped) → I ─Scoped
    ⟦ `σ A d    ⟧ X i Γ = Σ[ a ∈ A ] (⟦ d a ⟧ X i Γ)
    ⟦ `X Δ j d  ⟧ X i = X Δ j ×ᴿ ⟦ d ⟧ X i
    ⟦ `∎ j      ⟧ X i Γ = i ≡ j × Γ ≡ []
  ```

  - context only contains live variables
    - enforced by relevant pair and constraints in `` `∎``

## Syntax-generic co-de-Bruijn Representation
  - working generically, this works well
  - but once description is concrete, there are unexpected indirections
  - e.g. "unary product" ``⟦ `X Δ σ (`∎ τ) ⟧``
    - trivial relevant pair (right side has empty context)

  ```agda
    ×ᴿ-trivial t = pairᴿ (t ↑ oi) ((refl , refl) ↑ oe) cover-oi-oe
  ```

  - in the other direction, we first have to "discover" that these extra thinnings are `oi` and `oe`

## Generic Conversion From Co-de-Bruijn Syntax
  - we can convert between de Bruijn and co-de-Bruijn
    - completely generically!
  - implementation is concise (few cases to handle)

  ```agda
    relax :
      (d : Desc I) → Δ ⊑ Γ →
      CoDeBruijn.Tm d τ Δ →
      DeBruijn.Tm d τ Γ

    tighten :
      (d : Desc I) →
      DeBruijn.Tm d τ Γ →
      CoDeBruijn.Tm d τ ⇑ Γ
  ```

## Dead Binding Elimination (generic co-de-Bruijn)
  - DBE can be done generically as well
  - we need let-bindings, the rest does not matter

. . .

  - descriptions are closed under sums:

    ``Tm (d `+ `Let) τ Γ``

## Dead Binding Elimination (generic co-de-Bruijn)
  ```agda
     _`+_ : Desc I → Desc I → Desc I
     d `+ e = `σ Bool λ isLeft →
       if isLeft then d else e

    `Let : Desc I
    `Let {I} = `σ (I × I) $ uncurry $ λ σ τ →
      `X [] σ (`X (σ ∷ []) τ (`∎ τ))

    -- ⟦ d ⟧ or ⟦ e ⟧ in ⟦ d + e ⟧
    pattern inl t = true  , t
    pattern inr t = false , t
  ```

## Dead Binding Elimination (generic co-de-Bruijn)
  - stay in co-de-Bruijn representation
  - define mutually recursive functions

  ```agda
    dbe :
      Tm (d `+ `Let) τ Γ →
      Tm (d `+ `Let) τ ⇑ Γ
    dbe-⟦∙⟧ :
      ⟦ d ⟧ (Scope (Tm (d' `+ `Let))) τ Γ →
      ⟦ d ⟧ (Scope (Tm (d' `+ `Let))) τ ⇑ Γ
    dbe-Scope :
      (Δ : List I) →
      Scope (Tm (d `+ `Let)) Δ τ Γ →
      Scope (Tm (d `+ `Let)) Δ τ ⇑ Γ
  ```

## Dead Binding Elimination (generic co-de-Bruijn)
  - recognise parts from the concrete implementation?

  ```agda
    dbe `var = `var ↑ oi
    dbe (`con (inl t)) = map⇑ (`con ∘ inl) (dbe-⟦∙⟧ t)
    dbe (`con (inr t)) = bind⇑ Let? (dbe-⟦∙⟧ {d = `Let} t)

    Let? : ⟦ `Let ⟧ (...) τ Γ → Tm (d `+ `Let) τ ⇑ Γ
    Let? t@(a , pairᴿ (t₁ ↑ θ₁) (t₂ ↑ p) _)
      with ×ᴿ-trivial⁻¹ p
    ... | (o' oz \\ t₂) , refl = t₂ ↑ θ₂
    ... | (os oz \\ t₂) , refl = `con (inr t) ↑ oi
  ```

## Dead Binding Elimination (generic co-de-Bruijn)
  ```agda
    dbe-⟦∙⟧ {d = `σ A d} (a , t) =
      map⇑ (a ,_) (dbe-⟦∙⟧ t)
    dbe-⟦∙⟧ {d = `X Δ j d} (pairᴿ (t₁ ↑ θ₁) (t₂ ↑ θ₂) c) =
      thin⇑ θ₁ (dbe-Scope Δ t₁) ,ᴿ thin⇑ θ₂ (dbe-⟦∙⟧ t₂)
    dbe-⟦∙⟧ {d = `∎ i} t =
      t ↑ oi

    dbe-Scope [] t = dbe t
    dbe-Scope (_ ∷ _) (ψ \\ t) =
      map⇑ (map⊢ ψ) (_ \\ᴿ dbe t)
  ```

## Generic co-de-Bruijn Representation
### Discussion
  - generic code is more reusable
  - in some sense nice to write
    - fewer cases to handle (abstraction)
  - but also more complex

## Generic co-de-Bruijn Representation
### Discussion
  - Allais et al. define generic notion of `Semantics`
    - abstracts over traversal (similar to recursion schemes)
  - defining a similar `Semantics` for co-de-Bruijn expressions seems more difficult
    - scopes change at each node, manipulating them requires re-constructing covers
    - probably easier when operating on thinned expressions (`_⇑_`)

## Generic co-de-Bruijn Representation
### Discussion
  - no correctness proofs yet
    - using which semantics?
    - generic notion of `Semantics` could be sufficient
    - or could at least prove it for a specific language


# Other Transformations

## Let-sinking

::: notes
Optional, can be skipped if low on time.
:::

  - move let-binding as far inwards as possible without
    - duplicating it
    - moving it into a $\lambda$-abstraction

## Let-sinking

  - pretty similar to DBE
    - also requires liveness information to find location
    - can be done directly, with repeated liveness querying
    - annotations make it more efficient
  - but it gets more complex
    - instead of just removing bindings, they get reordered
    - also reorders the context, but thinnings are *order-preserving*
    - requires another mechanism to talk about that
  - to keep it manageable, we focus on one binding at a time

## Let-sinking
  - top level signature remains somewhat simple
  - should look similar to

    `Let : Expr σ Γ → Expr τ (σ ∷ Γ) → Expr τ Γ`

  - but as we go under binders, the binding doesn't stay on top

  ```agda
    sink-let :
      Expr σ (Γ₁ ++ Γ₂) →
      Expr τ (Γ₁ ++ σ ∷ Γ₂) →
      Expr τ (Γ₁ ++ Γ₂)
  ```

## Let-sinking
  - also requires renaming, partitioning context into 4 parts

  ```agda
    rename-top-Expr :
      (Γ' : Ctx) →
      Expr τ (Γ' ++ Γ₁ ++ σ ∷ Γ₂) →
      Expr τ (Γ' ++ σ ∷ Γ₁ ++ Γ₂)
  ```

  - this gets cumbersome
  - especially for co-de-Bruijn:
    - need to partition and re-assemble thinnings
      - same for covers?
    - 12 thinnings in scope

## Let-sinking
### Discussion
  - implemented for de Bruijn (incl. annotated) and co-de-Bruijn
    - exact phrasing of signatures has a big impact
  - progress with co-de-Bruijn proof, but messy and unfinished

. . .

  - generally similar conclusions as from DBE
  - re-ordering context does not interact nicely with thinnings
  - maintaining the co-de-Bruijn structure is especially cumbersome
  - for more details, see thesis


# Discussion
  - TODO


## {.standout}

<https://github.com/mheinzel/correct-optimisations>
