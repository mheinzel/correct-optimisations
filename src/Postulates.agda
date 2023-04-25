module Postulates where

open import Relation.Binary.PropositionalEquality using (_≡_)

-- This is needed because our notion of semantical equivalence is "same evaluation result",
-- and values include Agda functions.
postulate
  extensionality :
    {S : Set} {T : S -> Set} (f g : (x : S) -> T x) ->
    ((x : S) -> f x ≡ g x) ->
    f ≡ g
