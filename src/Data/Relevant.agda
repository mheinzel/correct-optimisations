{-# OPTIONS --safe #-}

-- Based on:
-- Everybody's Got To Be Somewhere
-- (https://arxiv.org/abs/1807.04085)
module Data.Relevant where

open import Data.Unit
open import Data.Nat using (_+_)
open import Data.List using (List ; _∷_ ; [] ; _++_)
open import Data.Product
open import Function using (_∘_ ; _$_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; cong₂ ; sym ; trans)
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import Data.Thinning

private
  variable
    I : Set
    Γ Γ₁ Γ₂ : List I
    τ σ : I
    S T : I ─Indexed

data Cover : {I : Set} {Γ₁ Γ₂ Γ : List I} → Γ₁ ⊑ Γ → Γ₂ ⊑ Γ → Set where
  c's : {θ₁ : Γ₁ ⊑ Γ} {θ₂ : Γ₂ ⊑ Γ} → Cover θ₁ θ₂ → Cover {Γ = τ ∷ _} (o' θ₁) (os θ₂)
  cs' : {θ₁ : Γ₁ ⊑ Γ} {θ₂ : Γ₂ ⊑ Γ} → Cover θ₁ θ₂ → Cover {Γ = τ ∷ _} (os θ₁) (o' θ₂)
  css : {θ₁ : Γ₁ ⊑ Γ} {θ₂ : Γ₂ ⊑ Γ} → Cover θ₁ θ₂ → Cover {Γ = τ ∷ _} (os θ₁) (os θ₂)
  czz  : Cover {I} oz oz

infixr 19 _++ᶜ_

_++ᶜ_ :
  {Γ₁ Γ₂ Γ Γ₁' Γ₂' Γ' : List I} →
  {θ₁ : Γ₁ ⊑ Γ} {θ₂ : Γ₂ ⊑ Γ} {ϕ₁ : Γ₁' ⊑ Γ'} {ϕ₂ : Γ₂' ⊑ Γ'} →
  Cover θ₁ θ₂ → Cover ϕ₁ ϕ₂ →
  Cover (θ₁ ++⊑ ϕ₁) (θ₂ ++⊑ ϕ₂)
c's c ++ᶜ c' = c's (c ++ᶜ c')
cs' c ++ᶜ c' = cs' (c ++ᶜ c')
css c ++ᶜ c' = css (c ++ᶜ c')
czz   ++ᶜ c' = c'

cover-split-++⊑ :
  {Γ₁ Γ₂ Γ Γ₁' Γ₂' Γ' : List I} →
  (θ₁ : Γ₁ ⊑ Γ) (θ₂ : Γ₂ ⊑ Γ) (ϕ₁ : Γ₁' ⊑ Γ') (ϕ₂ : Γ₂' ⊑ Γ') →
  Cover (θ₁ ++⊑ ϕ₁) (θ₂ ++⊑ ϕ₂) →
  Cover θ₁ θ₂ × Cover ϕ₁ ϕ₂
cover-split-++⊑ {Γ = []}    oz oz ϕ₁ ϕ₂ c = czz , c
cover-split-++⊑ {Γ = τ ∷ Γ} (o' θ₁) (os θ₂) ϕ₁ ϕ₂ (c's c) = let c' , c'' = cover-split-++⊑ θ₁ θ₂ ϕ₁ ϕ₂ c in c's c' , c''
cover-split-++⊑ {Γ = τ ∷ Γ} (os θ₁) (o' θ₂) ϕ₁ ϕ₂ (cs' c) = let c' , c'' = cover-split-++⊑ θ₁ θ₂ ϕ₁ ϕ₂ c in cs' c' , c''
cover-split-++⊑ {Γ = τ ∷ Γ} (os θ₁) (os θ₂) ϕ₁ ϕ₂ (css c) = let c' , c'' = cover-split-++⊑ θ₁ θ₂ ϕ₁ ϕ₂ c in css c' , c''

law-cover-split-++⊑ :
  {Γ₁ Γ₂ Γ Γ₁' Γ₂' Γ' : List I} →
  (θ₁ : Γ₁ ⊑ Γ) (θ₂ : Γ₂ ⊑ Γ) (ϕ₁ : Γ₁' ⊑ Γ') (ϕ₂ : Γ₂' ⊑ Γ') →
  (c : Cover (θ₁ ++⊑ ϕ₁) (θ₂ ++⊑ ϕ₂)) →
  let c' , c'' = cover-split-++⊑ θ₁ θ₂ ϕ₁ ϕ₂ c
  in c' ++ᶜ c'' ≡ c
law-cover-split-++⊑ {Γ = []} oz oz ϕ₁ ϕ₂ c = refl
law-cover-split-++⊑ {Γ = x ∷ Γ} (o' θ₁) (os θ₂) ϕ₁ ϕ₂ (c's c) = cong c's (law-cover-split-++⊑ θ₁ θ₂ ϕ₁ ϕ₂ c)
law-cover-split-++⊑ {Γ = x ∷ Γ} (os θ₁) (o' θ₂) ϕ₁ ϕ₂ (cs' c) = cong cs' (law-cover-split-++⊑ θ₁ θ₂ ϕ₁ ϕ₂ c)
law-cover-split-++⊑ {Γ = x ∷ Γ} (os θ₁) (os θ₂) ϕ₁ ϕ₂ (css c) = cong css (law-cover-split-++⊑ θ₁ θ₂ ϕ₁ ϕ₂ c)

cover-oi-oi : Cover {Γ = Γ} oi oi
cover-oi-oi {Γ = []} = czz
cover-oi-oi {Γ = x ∷ Γ} = css cover-oi-oi

cover-oi-oe : Cover {Γ = Γ} oi oe
cover-oi-oe {Γ = []} = czz
cover-oi-oe {Γ = x ∷ Γ} = cs' cover-oi-oe

cover-oi-oe⁻¹ : {θ : Γ₁ ⊑ Γ} {ϕ : [] ⊑ Γ} → Cover θ ϕ → Γ₁ ≡ Γ
cover-oi-oe⁻¹ (cs' c) = cong (_ ∷_) (cover-oi-oe⁻¹ c)
cover-oi-oe⁻¹ czz = refl

cover-flip : {θ : Γ₁ ⊑ Γ} {ϕ : Γ₂ ⊑ Γ} → Cover θ ϕ → Cover ϕ θ
cover-flip (c's c) = cs' (cover-flip c)
cover-flip (cs' c) = c's (cover-flip c)
cover-flip (css c) = css (cover-flip c)
cover-flip czz = czz

-- Relevant pair
record _×ᴿ_ (S T : I ─Indexed) (Γ : List I) : Set where
  constructor pairᴿ
  field
    outl  : S ⇑ Γ
    outr  : T ⇑ Γ
    cover : Cover (_⇑_.thinning outl) (_⇑_.thinning outr)

record _⊢_ (Γ' : List I) (T : I ─Indexed) (Γ : List I) : Set where
  constructor _\\_
  field
    {bound} : List I
    thinning : bound ⊑ Γ'
    thing : T (bound ++ Γ)

map⊢ : Γ₁ ⊑ Γ₂ → (Γ₁ ⊢ T) Γ → (Γ₂ ⊢ T) Γ
map⊢ ϕ (θ \\ t) = (θ ₒ ϕ) \\ t

{- original definition
_\\ᴿ_ : {T : I ─Indexed} (Γ' : List I) → T ⇑ (Γ' ++ Γ) → (Γ' ⊢ T) ⇑ Γ
Γ' \\ᴿ (t ↑ ψ)       with Γ' ⊣ ψ
Γ' \\ᴿ (t ↑ .(θ ++⊑ ϕ)) | split θ ϕ (refl , refl) = (θ \\ t) ↑ ϕ
-}

-- TODO: better name? R → ᴿ
\\ᴿ-helper : {Γ Γ' Γ'' : List I} {ψ : Γ'' ⊑ (Γ' ++ Γ)} → Split Γ' ψ → T Γ'' → (Γ' ⊢ T) ⇑ Γ
\\ᴿ-helper (split ϕ₁ ϕ₂ (refl , refl)) t = (ϕ₁ \\ t) ↑ ϕ₂

_\\ᴿ_ : (Γ' : List I) → T ⇑ (Γ' ++ Γ) → (Γ' ⊢ T) ⇑ Γ
Γ' \\ᴿ (t ↑ ψ) = \\ᴿ-helper (Γ' ⊣ ψ) t

-- Just to avoid a huge chain of Σ-types.
record Coproduct {I : Set} {Γ₁ Γ₂ Γ : List I} (θ : Γ₁ ⊑ Γ) (ϕ : Γ₂ ⊑ Γ) : Set where
  constructor coproduct
  field
    Γ' : List I
    ψ  : Γ' ⊑ Γ
    θ' : Γ₁ ⊑ Γ'
    ϕ' : Γ₂ ⊑ Γ'
    pθ : θ ≡ (θ' ₒ ψ)
    pϕ : ϕ ≡ (ϕ' ₒ ψ)
    c  : Cover θ' ϕ'

cop : (θ : Γ₁ ⊑ Γ) (ϕ : Γ₂ ⊑ Γ) → Coproduct θ ϕ
cop (o' θ) (o' ϕ) =
  let coproduct _ ψ _ _ pθ pϕ c = cop θ ϕ
  in  coproduct _ (o' ψ) _ _ (cong o' pθ) (cong o' pϕ) c
cop (o' θ) (os ϕ) =
  let coproduct _ ψ _ _ pθ pϕ c = cop θ ϕ
  in  coproduct _ (os ψ) _ _ (cong o' pθ) (cong os pϕ) (c's c)
cop (os θ) (o' ϕ) =
  let coproduct _ ψ _ _ pθ pϕ c = cop θ ϕ
  in  coproduct _ (os ψ) _ _ (cong os pθ) (cong o' pϕ) (cs' c)
cop (os θ) (os ϕ) =
  let coproduct _ ψ _ _ pθ pϕ c = cop θ ϕ
  in  coproduct _ (os ψ) _ _ (cong os pθ) (cong os pϕ) (css c)
cop oz oz =
  coproduct _ oz _ _ refl refl czz

_,ᴿ_ : S ⇑ Γ → T ⇑ Γ → (S ×ᴿ T) ⇑ Γ
(s ↑ θ) ,ᴿ (t ↑ ϕ) =
  let coproduct _ ψ θ' ϕ' _ _ c = cop θ ϕ
  in pairᴿ (s ↑ θ') (t ↑ ϕ') c ↑ ψ

{-
cover-rotate :
  {Γ₁ Γ₂ Γ₃ Γ₂₃ : List I} →
  (θ₁ : Γ₁ ⊑ Γ) (θ₂₃ : Γ₂₃ ⊑ Γ) (θ₂₋₂₃ : Γ₃ ⊑ Γ₂₃) (θ₃₋₂₃ : Γ₃ ⊑ Γ₂₃) →
  (c₁₊₂₃ : Cover θ₁ θ₂₃) →
  (c₂₊₃  : Cover θ₂₋₂₃ θ₃₋₂₃) →
  let coproduct Γ₁₂ θ₁₂ θ₁₋₁₂ θ₂₋₁₂ eq₁ eq₂ c₁₊₂ = cop θ₁ (θ₂₋₂₃ ₒ θ₂₃)
      θ₃ = θ₃₋₂₃ ₒ θ₂₃
  in
  Cover θ₁₂ θ₃
cover-rotate θ₁ θ₂₃ θ₂₋₂₃ θ₃₋₂₃ c₁₊₂₃ c₂₊₃ with cop θ₁ (θ₂₋₂₃ ₒ θ₂₃)
... | coproduct Γ₁₂ θ₁₂ θ₁₋₁₂ θ₂₋₁₂ eq₁ eq₂ c₁₊₂ =
  {!!}
-}
