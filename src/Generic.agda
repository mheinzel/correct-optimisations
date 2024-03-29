-- Based on:
-- A Type and Scope Safe Universe of Syntaxes with Binding: Their Semantics and Proofs
-- (https://github.com/gallais/generic-syntax)
module Generic where

--------------------------------------------------------------------------------
-- THE LIBRARY
--------------------------------------------------------------------------------

-- Notations for indexed types
import Stdlib

-- SYNTAX (de Bruijn)
--------------------------------------------------------------------------------

-- Variables as well scoped-and-sorted de Bruijn indices
import Data.Var as V
import Data.Var.Varlike

-- Universe of Well Scoped-and-Sorted Syntaxes with Binding
import Generic.DeBruijn.Syntax

-- SEMANTICS (de Bruijn)
--------------------------------------------------------------------------------

-- Environments as Well Scoped-and-Sorted Functions from Variables to Values
import Data.Environment

-- Semantics as Well Scoped-and-Sorted Algebras on Syntaxes with Binding
import Generic.DeBruijn.Semantics

-- Trivial Semantics
import Generic.DeBruijn.Semantics.Unit

-- Renaming and Substitution as Semantics
-- import Generic.DeBruijn.Semantics.Syntactic

-- Contraction as a Semantics
-- import Generic.DeBruijn.Semantics.Contract

-- PHOAS syntax, including a converter from de Bruijn syntax
open import Generic.DeBruijn.Syntax.PHOAS

-- PROPERTIES (de Bruijn)
--------------------------------------------------------------------------------

-- Relator: Head Constructors with Related Subterms
import Generic.DeBruijn.Relator

-- Fundamental Lemma of Logical Predicates
import Data.Pred as P
import Generic.DeBruijn.Fundamental

-- Generic Notion of Simulation Between Two Semantics
import Data.Relation as R
import Generic.DeBruijn.Simulation
-- import Generic.DeBruijn.Simulation.Syntactic

-- Applying the Identity Substitution is the Identity
-- import Generic.DeBruijn.Identity

-- SYNTAX (co de Bruijn)
--------------------------------------------------------------------------------

-- Thinnings, also called Order-Preserving Embeddings
import Data.Thinning

-- Relevant Pairs and Scopes
import Data.Relevant

-- Universe of Well Scoped-and-Sorted Syntaxes with Binding
import Generic.CoDeBruijn.Syntax

-- SEMANTICS (co de Bruijn)
--------------------------------------------------------------------------------

-- Semantics as Well Scoped-and-Sorted Algebras on Syntaxes with Binding
import Generic.DeBruijn.Semantics

-- CONVERSION (de Bruijn <-> co de Bruijn)
--------------------------------------------------------------------------------

import Generic.Conversion
