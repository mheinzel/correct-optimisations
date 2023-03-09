-- fundamental constructions
module CoDeBruijn.Core {I : Set} where

open import Data.Unit
open import Data.Nat using (_+_)
open import Data.List using (List ; _∷_ ; [] ; _++_)
open import Data.Product
open import Function using (_∘_ ; _$_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; cong₂ ; sym ; trans)
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import OPE {I}

private
  variable
    Γ Γ₁ Γ₂ : List I
    τ σ : I
    S T : I ─Scoped

data Cover : {Γ₁ Γ₂ Γ : List I} → Γ₁ ⊑ Γ → Γ₂ ⊑ Γ → Set where
  _c's : {θ₁ : Γ₁ ⊑ Γ} {θ₂ : Γ₂ ⊑ Γ} → Cover θ₁ θ₂ → Cover (_o' {τ} θ₁) (θ₂ os)
  _cs' : {θ₁ : Γ₁ ⊑ Γ} {θ₂ : Γ₂ ⊑ Γ} → Cover θ₁ θ₂ → Cover (_os {τ} θ₁) (θ₂ o')
  _css : {θ₁ : Γ₁ ⊑ Γ} {θ₂ : Γ₂ ⊑ Γ} → Cover θ₁ θ₂ → Cover (_os {τ} θ₁) (θ₂ os)
  czz  :                                             Cover oz           oz

infixr 19 _++ᶜ_

_++ᶜ_ :
  {Γ₁ Γ₂ Γ Γ₁' Γ₂' Γ' : List I} →
  {θ₁ : Γ₁ ⊑ Γ} {θ₂ : Γ₂ ⊑ Γ} {ϕ₁ : Γ₁' ⊑ Γ'} {ϕ₂ : Γ₂' ⊑ Γ'} →
  Cover θ₁ θ₂ → Cover ϕ₁ ϕ₂ →
  Cover (θ₁ ++⊑ ϕ₁) (θ₂ ++⊑ ϕ₂)
(c c's) ++ᶜ c' = (c ++ᶜ c') c's
(c cs') ++ᶜ c' = (c ++ᶜ c') cs'
(c css) ++ᶜ c' = (c ++ᶜ c') css
czz     ++ᶜ c' = c'

cover-split-++⊑ :
  {Γ₁ Γ₂ Γ Γ₁' Γ₂' Γ' : List I} →
  (θ₁ : Γ₁ ⊑ Γ) (θ₂ : Γ₂ ⊑ Γ) (ϕ₁ : Γ₁' ⊑ Γ') (ϕ₂ : Γ₂' ⊑ Γ') →
  Cover (θ₁ ++⊑ ϕ₁) (θ₂ ++⊑ ϕ₂) →
  Cover θ₁ θ₂ × Cover ϕ₁ ϕ₂
cover-split-++⊑ {Γ = []}    oz oz ϕ₁ ϕ₂ c = czz , c
cover-split-++⊑ {Γ = τ ∷ Γ} (θ₁ o') (θ₂ os) ϕ₁ ϕ₂ (c c's) = let c' , c'' = cover-split-++⊑ θ₁ θ₂ ϕ₁ ϕ₂ c in (c' c's) , c''
cover-split-++⊑ {Γ = τ ∷ Γ} (θ₁ os) (θ₂ o') ϕ₁ ϕ₂ (c cs') = let c' , c'' = cover-split-++⊑ θ₁ θ₂ ϕ₁ ϕ₂ c in (c' cs') , c''
cover-split-++⊑ {Γ = τ ∷ Γ} (θ₁ os) (θ₂ os) ϕ₁ ϕ₂ (c css) = let c' , c'' = cover-split-++⊑ θ₁ θ₂ ϕ₁ ϕ₂ c in (c' css) , c''

law-cover-split-++⊑ :
  {Γ₁ Γ₂ Γ Γ₁' Γ₂' Γ' : List I} →
  (θ₁ : Γ₁ ⊑ Γ) (θ₂ : Γ₂ ⊑ Γ) (ϕ₁ : Γ₁' ⊑ Γ') (ϕ₂ : Γ₂' ⊑ Γ') →
  (c : Cover (θ₁ ++⊑ ϕ₁) (θ₂ ++⊑ ϕ₂)) →
  let c' , c'' = cover-split-++⊑ θ₁ θ₂ ϕ₁ ϕ₂ c
  in c' ++ᶜ c'' ≡ c
law-cover-split-++⊑ {Γ = []} oz oz ϕ₁ ϕ₂ c = refl
law-cover-split-++⊑ {Γ = x ∷ Γ} (θ₁ o') (θ₂ os) ϕ₁ ϕ₂ (c c's) = cong _c's (law-cover-split-++⊑ θ₁ θ₂ ϕ₁ ϕ₂ c)
law-cover-split-++⊑ {Γ = x ∷ Γ} (θ₁ os) (θ₂ o') ϕ₁ ϕ₂ (c cs') = cong _cs' (law-cover-split-++⊑ θ₁ θ₂ ϕ₁ ϕ₂ c)
law-cover-split-++⊑ {Γ = x ∷ Γ} (θ₁ os) (θ₂ os) ϕ₁ ϕ₂ (c css) = cong _css (law-cover-split-++⊑ θ₁ θ₂ ϕ₁ ϕ₂ c)

cover-oi : Cover {Γ} oi oi
cover-oi {[]} = czz
cover-oi {x ∷ Γ} = cover-oi css

cover-flip : {Γ₁ Γ₂ Γ : List I} {θ : Γ₁ ⊑ Γ} {ϕ : Γ₂ ⊑ Γ} → Cover θ ϕ → Cover ϕ θ
cover-flip (c c's) = cover-flip c cs'
cover-flip (c cs') = cover-flip c c's
cover-flip (c css) = cover-flip c css
cover-flip czz = czz

-- Relevant pair
record _×ᴿ_ (S T : I ─Scoped) (Γ : List I) : Set where
  constructor pairᴿ
  field
    outl  : S ⇑ Γ
    outr  : T ⇑ Γ
    cover : Cover (_⇑_.thinning outl) (_⇑_.thinning outr)

record _⊢_ (Γ' : List I) (T : I ─Scoped) (Γ : List I) : Set where
  constructor _\\_
  field
    {bound} : List I
    thinning : bound ⊑ Γ'
    thing : T (bound ++ Γ)

map⊢ : Γ₁ ⊑ Γ₂ → (Γ₁ ⊢ T) Γ → (Γ₂ ⊢ T) Γ
map⊢ ϕ (θ \\ t) = (θ ₒ ϕ) \\ t

{- original definition
_\\R_ : {T : I ─Scoped} (Γ' : List I) → T ⇑ (Γ' ++ Γ) → (Γ' ⊢ T) ⇑ Γ
Γ' \\R (t ↑ ψ)       with Γ' ⊣ ψ
Γ' \\R (t ↑ .(θ ++⊑ ϕ)) | ⊣r θ ϕ (refl , refl) = (θ \\ t) ↑ ϕ
-}

\\R-helper : ∀ {T Γ Γ' Γ''} {ψ : Γ'' ⊑ (Γ' ++ Γ)} → Γ' ⊣R ψ → T Γ'' → (Γ' ⊢ T) ⇑ Γ
\\R-helper (⊣r ϕ₁ ϕ₂ (refl , refl)) t = (ϕ₁ \\ t) ↑ ϕ₂

_\\R_ : ∀ {T Γ} (Γ' : List I) → T ⇑ (Γ' ++ Γ) → (Γ' ⊢ T) ⇑ Γ
Γ' \\R (t ↑ ψ) = \\R-helper (Γ' ⊣ ψ) t


-- Just to avoid a huge chain of Σ-types.
record Coproduct (θ : Γ₁ ⊑ Γ) (ϕ : Γ₂ ⊑ Γ) : Set where
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
cop (θ o') (ϕ o') =
  let coproduct _ ψ _ _ pθ pϕ c = cop θ ϕ
  in  coproduct _ (ψ o') _ _ (cong _o' pθ) (cong _o' pϕ) c
cop (θ o') (ϕ os) =
  let coproduct _ ψ _ _ pθ pϕ c = cop θ ϕ
  in  coproduct _ (ψ os) _ _ (cong _o' pθ) (cong _os pϕ) (c c's)
cop (θ os) (ϕ o') =
  let coproduct _ ψ _ _ pθ pϕ c = cop θ ϕ
  in  coproduct _ (ψ os) _ _ (cong _os pθ) (cong _o' pϕ) (c cs')
cop (θ os) (ϕ os) =
  let coproduct _ ψ _ _ pθ pϕ c = cop θ ϕ
  in  coproduct _ (ψ os) _ _ (cong _os pθ) (cong _os pϕ) (c css)
cop oz oz =
  coproduct _ oz _ _ refl refl czz

_,ᴿ_ : S ⇑ Γ → T ⇑ Γ → (S ×ᴿ T) ⇑ Γ
(s ↑ θ) ,ᴿ (t ↑ ϕ) =
  let coproduct _ ψ θ' ϕ' _ _ c = cop θ ϕ
  in pairᴿ (s ↑ θ') (t ↑ ϕ') c ↑ ψ
