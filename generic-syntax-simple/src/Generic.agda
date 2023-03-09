module Generic where

--------------------------------------------------------------------------------
-- THE LIBRARY
--------------------------------------------------------------------------------

-- Notations for indexed types
import Stdlib

-- SYNTAX
--------------------------------------------------------------------------------

-- Variables as well scoped-and-sorted de Bruijn indices
import Data.Var as V
import Data.Var.Varlike

-- Universe of Well Scoped-and-Sorted Syntaxes with Binding
import Generic.Syntax

-- Alternative interpretation of descriptions empower us to write:

-- A converter to PHOAS syntax
open import Generic.Syntax.PHOAS

-- SEMANTICS
--------------------------------------------------------------------------------

-- Environments as Well Scoped-and-Sorted Functions from Variables to Values
import Data.Environment

-- Semantics as Well Scoped-and-Sorted Algebras on Syntaxes with Binding
import Generic.Semantics

-- Trivial Semantics
import Generic.Semantics.Unit

-- Renaming and Substitution as Semantics
-- import Generic.Semantics.Syntactic

-- Contraction as a Semantics
-- import Generic.Semantics.Contract

-- PROPERTIES
--------------------------------------------------------------------------------

-- Relator: Head Constructors with Related Subterms
import Generic.Relator

-- Fundamental Lemma of Logical Predicates
import Data.Pred as P
import Generic.Fundamental

-- Generic Notion of Simulation Between Two Semantics
import Data.Relation as R
import Generic.Simulation
-- import Generic.Simulation.Syntactic

-- Applying the Identity Substitution is the Identity
-- import Generic.Identity

-- FUSION

-- Generic Notion of Fusible Semantics
-- import Generic.Fusion

-- Renaming and Substitution interact well with each other and let-elaboration
-- import Generic.Fusion.Syntactic
-- import Generic.Fusion.Elaboration.LetBinder

-- Based on Kaiser, Schäfer, and Stark's remark, we can concoct an axiom-free
-- specialised version of fusion for renaming-semantics interactions (it makes
-- some of the previous proofs shorter).
-- We can also use it to replicate their result assuming functional extensionality
-- import Generic.Fusion.Specialised.Propositional
-- import Generic.Fusion.Specialised.Replication
