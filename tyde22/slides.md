---
author: Matthias Heinzel
title: Provingly Correct Optimisations on Intrinsically Typed Expressions
subtitle: Extended Abstract
institute: Utrecht University
theme: metropolis
---

## Motivation

$$
  P, Q ::= v
  \ \big|\  P + Q
  \ \big|\  \ldots
  \ \big|\  \textbf{let } x = P \textbf{ in } Q
  \ \big|\  x
$$

```agda
data Expr (Γ : Ctx) : (σ : U) → Set where
  Val   : ⟦ σ ⟧ → Expr Γ σ
  Plus  : Expr Γ NAT → Expr Γ NAT → Expr Γ NAT
  ...
  Let   : Expr Γ σ → Expr (σ ∷ Γ) τ → Expr Γ τ
  Var   : Ref σ Γ → Expr Γ σ
```


## {.standout}

github.com/mheinzel/correct-optimisations

I'm looking forward to your feedback!
