module Generic.DeBruijn.Semantics.Unit where

open import Data.Unit
open import Data.Var
open import Generic.Syntax
open import Generic.DeBruijn.Semantics

private
  variable
    I : Set
    d : Desc I

Unit : I ─Scoped
Unit = λ _ _ → ⊤

SemUnit : Semantics d Unit Unit
SemUnit = _
