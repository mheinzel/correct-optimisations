{-# OPTIONS --safe #-}

-- Based on:
-- A Type and Scope Safe Universe of Syntaxes with Binding: Their Semantics and Proofs
-- (https://github.com/gallais/generic-syntax)
module Generic.Syntax where

open import Data.Bool using (Bool; if_then_else_)
open import Data.List.Base using (List; []; map; foldr)
open import Relation.Binary.PropositionalEquality

open import Data.Var using (_─Scoped)

private
  variable
    I : Set


-- Descriptions

data Desc (I : Set) : Set₁ where
  `σ : (A : Set) → (A → Desc I)  → Desc I
  `X : List I → I → Desc I       → Desc I
  `∎ : I                         → Desc I

reindex : {I J : Set} → (I → J) → Desc I → Desc J
reindex f (`σ A d)   = `σ A λ a → reindex f (d a)
reindex f (`X Δ j d) = `X (map f Δ) (f j) (reindex f d)
reindex f (`∎ i)     = `∎ (f i)


-- Descriptions are closed under sums

module _ {I : Set} where

 infixr 5 _`+_


 _`+_ : Desc I → Desc I → Desc I
 d `+ e = `σ Bool λ isLeft →
          if isLeft then d else e


-- Descriptions are closed under products

module _ {I : Set} where

 infixr 6 _`*_

 _`%_ : Desc I → I → Desc I
 `σ A d   `% v = `σ A (λ a → d a `% v)
 `X Δ j d `% v = `X Δ j (d `% v)
 `∎ i     `% v = `σ (i ≡ v) (λ _ → `∎ i)


 _`*_ : Desc I → Desc I → Desc I
 `σ A d   `* e = `σ A (λ a → d a `* e)
 `X Δ j d `* e = `X Δ j (d `* e)
 `∎ i     `* e = e `% i


-- Descriptions are closed under products of recursive positions

module _ {I : Set} where

 `Xs : List I → Desc I → Desc I
 `Xs js d = foldr (`X []) d js
