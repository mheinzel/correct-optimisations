-- Based on:
-- A Type and Scope Safe Universe of Syntaxes with Binding: Their Semantics and Proofs
-- (https://github.com/gallais/generic-syntax)
module Generic.DeBruijn.Semantics.Unit where

open import Data.Unit using (⊤)
open import Data.Var using (_─Scoped)
open import Generic.Syntax using (Desc)
open import Generic.DeBruijn.Semantics using (Semantics)

private
  variable
    I : Set
    d : Desc I

Unit : I ─Scoped
Unit = λ _ _ → ⊤

SemUnit : Semantics d Unit Unit
SemUnit = _
