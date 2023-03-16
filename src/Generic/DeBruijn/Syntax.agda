-- Based on:
-- A Type and Scope Safe Universe of Syntaxes with Binding: Their Semantics and Proofs
-- (https://github.com/gallais/generic-syntax)
module Generic.DeBruijn.Syntax where

open import Data.Bool using (true; false)
open import Data.List.Base as L using (List; []; _∷_; _++_)
open import Data.Product as Prod using (_×_; Σ-syntax; _,_)
open import Function using (id; _∘_; _∋_)
open import Relation.Binary.PropositionalEquality

open import Data.Var
open import Relation.Unary
open import Generic.Syntax
open import Data.Environment hiding (sequenceA; curry; uncurry)

private
  variable
    I : Set
    i σ : I
    Γ₁ Γ₂ : List I
    X Y : List I → I ─Scoped

-- Interpretation of Descriptions

⟦_⟧ : Desc I → (List I → I ─Scoped) → I ─Scoped
⟦ `σ A d    ⟧ X i Γ = Σ[ a ∈ A ] (⟦ d a ⟧ X i Γ)
⟦ `X Δ j d  ⟧ X i Γ = X Δ j Γ × ⟦ d ⟧ X i Γ
⟦ `∎ j      ⟧ X i Γ = i ≡ j

-- Syntaxes: Free Relative Monad of a Description's Interpretation

Scope : I ─Scoped → List I → I ─Scoped
Scope T Δ i = (Δ ++_) ⊢ T i

module _ {I : Set} where

 data Tm (d : Desc I) : I ─Scoped where
   `var  : ∀[ Var i                   ⇒ Tm d i ]
   `con  : ∀[ ⟦ d ⟧ (Scope (Tm d)) i  ⇒ Tm d i ]


module _ {I i Γ} {d : Desc I} where

  `var-inj : ∀ {t u} → (Tm d i Γ ∋ `var t) ≡ `var u → t ≡ u
  `var-inj refl = refl

  `con-inj : ∀ {t u} → (Tm d i Γ ∋ `con t) ≡ `con u → t ≡ u
  `con-inj refl = refl

-- Closed terms
module _ {I : Set} where

  TM : Desc I → I → Set
  TM d i = Tm d i []


-- Descriptions are closed under sums

module _ {I : Set} {d e : Desc I} {X : List I → I ─Scoped}
         {A : Set} {i : I} {Γ : List I} where

 case : (⟦ d ⟧ X i Γ → A) → (⟦ e ⟧ X i Γ → A) →
        (⟦ d `+ e  ⟧ X i Γ → A)
 case l r (true   , t) = l t
 case l r (false  , t) = r t


-- Descriptions are closed under products

module _ {I : Set} {X : List I → I ─Scoped}
         {i : I} {Γ : List I} where

 byRefl : ∀ {d} → ⟦ d ⟧ X i Γ → ⟦ d `% i ⟧ X i Γ
 byRefl {`σ A d}   (a , t) = a , byRefl t
 byRefl {`X Δ j d} (r , t) = r , byRefl t
 byRefl {`∎ i}     eq      = sym eq , eq

 eqView : ∀ {d v} → ⟦ d `% v ⟧ X i Γ → ⟦ d ⟧ X i Γ × i ≡ v
 eqView {`σ A d}   (a , t)       = Prod.map₁ (a ,_) (eqView t)
 eqView {`X Δ j d} (r , t)       = Prod.map₁ (r ,_) (eqView t)
 eqView {`∎ i}     (refl , refl) = refl , refl


 uncurry : {d e : Desc I} {A : Set} →
           (⟦ d ⟧ X i Γ → ⟦ e ⟧ X i Γ → A) →
           (⟦ d `* e  ⟧ X i Γ → A)
 uncurry {`σ A d}   f (a , t) = uncurry (f ∘ (a ,_)) t
 uncurry {`X Δ j d} f (r , t) = uncurry (f ∘ (r ,_)) t
 uncurry {`∎ i}     f t with eqView t
 ... | u , eq = f eq u

 curry : {d e : Desc I} {A : Set} →
         (⟦ d `* e  ⟧ X i Γ → A) →
         (⟦ d ⟧ X i Γ → ⟦ e ⟧ X i Γ → A)
 curry {`σ A d}   f (a , t) u = curry (f ∘ (a ,_)) t u
 curry {`X Δ j d} f (r , t) u = curry (f ∘ (r ,_)) t u
 curry {`∎ i}     f refl    u = f (byRefl u)


-- Descriptions are closed under products of recursive positions

module _ {I : Set} {d : Desc I} {X : List I → I ─Scoped} {i : I} {Γ : List I} where

 unXs : ∀ Δ → ⟦ `Xs Δ d ⟧ X i Γ → (Δ ─Env) (X []) Γ × ⟦ d ⟧ X i Γ
 unXs []       v       = ε , v
 unXs (σ ∷ Δ)  (r , v) = Prod.map₁ (_∙ r) (unXs Δ v)


-- Descriptions give rise to traversable functors

module _ {I : Set} {X Y : List I → I ─Scoped} {Γ Δ} {i} where


 fmap :  (d : Desc I) → (∀ Θ i → X Θ i Γ → Y Θ i Δ) → ⟦ d ⟧ X i Γ → ⟦ d ⟧ Y i Δ
 fmap (`σ A d)    f = Prod.map₂ (fmap (d _) f)
 fmap (`X Δ j d)  f = Prod.map (f Δ j) (fmap d f)
 fmap (`∎ i)      f = id

 fmap-ext : (d : Desc I) {f g : ∀ Θ i → X Θ i Γ → Y Θ i Δ} →
            (f≈g : ∀ Θ i x → f Θ i x ≡ g Θ i x) (v : ⟦ d ⟧ X i Γ) →
            fmap d f v ≡ fmap d g v
 fmap-ext (`σ A d)   f≈g (a , v) = cong (a ,_) (fmap-ext (d a) f≈g v)
 fmap-ext (`X Δ j d) f≈g (r , v) = cong₂ _,_ (f≈g Δ j r) (fmap-ext d f≈g v)
 fmap-ext (`∎ i)     f≈g v       = refl

module _ {I : Set} {X : List I → I ─Scoped} where

 fmap-id : (d : Desc I) {Γ : List I} {i : I} (v : ⟦ d ⟧ X i Γ) → fmap d (λ _ _ x → x) v ≡ v
 fmap-id (`σ A d)    (a , v)  = cong (a ,_) (fmap-id (d a) v)
 fmap-id (`X Δ j d)  (r , v)  = cong (r ,_) (fmap-id d v)
 fmap-id (`∎ x)      v        = refl

module _ {I : Set} {X Y Z : List I → I ─Scoped} where

 fmap² : (d : Desc I) {Γ Δ Θ : List I} {i : I}
         (f : ∀ Φ i → X Φ i Γ → Y Φ i Δ) (g : ∀ Φ i → Y Φ i Δ → Z Φ i Θ)
         (t : ⟦ d ⟧ X i Γ) →
         fmap  {I} {Y} {Z} d g (fmap d f t) ≡ fmap d (λ Φ i → g Φ i ∘ f Φ i) t
 fmap² (`σ A d)    f g (a , t)  = cong (_ ,_) (fmap² (d a) f g t)
 fmap² (`X Δ j d)  f g (r , t)  = cong (_ ,_) (fmap² d f g t)
 fmap² (`∎ i)      f g t        = refl


open import Category.Applicative

module _ {A : Set → Set} {{app : RawApplicative A}} where

 module A = RawApplicative app
 open A

 sequenceA : (d : Desc I) →
             ∀[ ⟦ d ⟧ (λ Δ j Γ → A (X Δ j Γ)) i ⇒ A ∘ ⟦ d ⟧ X i ]
 sequenceA (`σ A d)    (a , t)  = (λ b → a , b) A.<$> sequenceA (d a) t
 sequenceA (`X Δ j d)  (r , t)  = _,_ A.<$> r ⊛ sequenceA d t
 sequenceA (`∎ i)      t        = pure t

 mapA : (d : Desc I) →
        (f : ∀ Δ j → X Δ j Γ₁ → A (Y Δ j Γ₂))
        → ⟦ d ⟧ X σ Γ₁ → A (⟦ d ⟧ Y σ Γ₂)
 mapA d f = sequenceA d ∘ fmap d f


-- Desc Morphisms

record DescMorphism {I : Set} (d e : Desc I) : Set₁ where
  constructor MkDescMorphism
  field apply : ∀ {X i Δ} → ⟦ d ⟧ X i Δ → ⟦ e ⟧ X i Δ

module _ {I : Set} {d e : Desc I} where

  {-# TERMINATING #-}
  map^Tm : DescMorphism d e → ∀ {σ Γ} → Tm d σ Γ → Tm e σ Γ
  map^Tm f (`var v) = `var v
  map^Tm f (`con t) = `con (DescMorphism.apply f (fmap d (λ _ _ → map^Tm f) t))
