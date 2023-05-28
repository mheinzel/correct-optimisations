module Generic.Conversion where

open import Data.Product using (_,_)
open import Data.List using (List; []; _∷_; [_]; _++_)
open import Function using (_$_; _∘_)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Data.Relevant as Relevant using (pairᴿ; _,ᴿ_; _\\_; _\\ᴿ_)
open import Data.Thinning
open import Data.Var using (_─Scoped; Var; z; s; injectˡ; injectʳ)
open import Generic.Syntax
open import Generic.DeBruijn.Syntax as DeBruijn
open import Generic.CoDeBruijn.Syntax as CoDeBruijn

private
  variable
    I : Set
    σ τ : I
    Γ Γ' Δ : List I
    T : I ─Scoped

Var-from-⊑ : [ τ ] ⊑ Γ → Var τ Γ
Var-from-⊑ (o' θ) = s (Var-from-⊑ θ)
Var-from-⊑ (os θ) = z

⊑-from-Var : Var τ Γ → [ τ ] ⊑ Γ
⊑-from-Var z = os oe
⊑-from-Var (s k) = o' (⊑-from-Var k)

module Relax where
  relax :
    (d : Desc I) → Γ' ⊑ Γ →
    CoDeBruijn.Tm d τ Γ' →
    DeBruijn.Tm d τ Γ

  relax-Scope :
    (Δ : List I) (d : Desc I) → Γ' ⊑ Γ →
    CoDeBruijn.Scope (CoDeBruijn.Tm d) Δ τ Γ' →
    DeBruijn.Scope (DeBruijn.Tm d) Δ τ Γ

  relax-⟦∙⟧ :
    (d d' : Desc I) → Γ' ⊑ Γ →
    CoDeBruijn.⟦ d ⟧ (CoDeBruijn.Scope (CoDeBruijn.Tm d')) τ Γ' →
    DeBruijn.⟦ d ⟧ (DeBruijn.Scope (DeBruijn.Tm d')) τ Γ

  relax d θ `var = `var (Var-from-⊑ θ)
  relax d θ (`con t) = `con (relax-⟦∙⟧ d d θ t)

  relax-Scope [] d θ t = relax d θ t
  relax-Scope Δ@(_ ∷ _) d θ (ψ \\ t) = relax d (ψ ++⊑ θ) t

  relax-⟦∙⟧ (`σ A k) d' θ (a , t) =
    a , relax-⟦∙⟧ (k a) d' θ t
  relax-⟦∙⟧ (`X Δ j d) d' θ (pairᴿ (t₁ ↑ θ₁) (t₂ ↑ θ₂) cover) =


    relax-Scope Δ d' (θ₁ ₒ θ) t₁ , relax-⟦∙⟧ d d' (θ₂ ₒ θ) t₂
  relax-⟦∙⟧ (`∎ j) d' θ (refl , refl) =
    refl

module RelaxSem where
  open import Data.Environment using (lookup; identity; th^Var; Kripke; _>>_; _<$>_)
  open import Generic.CoDeBruijn.Semantics as Sem using (Semantics)

  𝓒ᴿ : Desc I → I ─Scoped
  𝓒ᴿ {I} d τ Γ' = (Γ : List I) → Γ' ⊑ Γ → DeBruijn.Tm d τ Γ

  alg-Kripke :
    {d : Desc I} (Δ : List I) → Γ' ⊑ Γ →
    Kripke Var (𝓒ᴿ d) Δ τ Γ' →
    DeBruijn.Scope (DeBruijn.Tm d) Δ τ Γ
  alg-Kripke [] θ t = t _ θ
  alg-Kripke {Γ' = Γ'} {Γ = Γ} Δ@(_ ∷ _) θ k =
    Data.Environment.th^□ k
      identity
      (Data.Environment.pack (injectʳ Δ))
      (Data.Environment.pack (injectˡ Γ'))
      (Δ ++ Γ)
      (oi ++⊑ θ)
    {-
    k {!? >> From⊑.toEnv θ!} -- (From⊑.toEnv (oe ++⊑ θ))
      (From⊑.toEnv (coerce (_⊑ (Δ ++ Γ)) (Data.List.Properties.++-identityʳ Δ) (oi ++⊑ oe)))
      (Δ ++ Γ)
      oi
    -}

  alg-⟦∙⟧ :
    (d : Desc I) {d' : Desc I} → Γ' ⊑ Γ →
    CoDeBruijn.⟦ d ⟧ (Kripke Var (𝓒ᴿ d')) τ Γ' →
    DeBruijn.⟦ d ⟧ (DeBruijn.Scope (DeBruijn.Tm d')) τ Γ
  alg-⟦∙⟧ (`σ A k) θ (a , t) = a , alg-⟦∙⟧ (k a) θ t
  alg-⟦∙⟧ (`X Δ j d) θ (pairᴿ (t₁ ↑ θ₁) (t₂ ↑ θ₂) c) = alg-Kripke Δ (θ₁ ₒ θ) t₁ , alg-⟦∙⟧ d (θ₂ ₒ θ) t₂
  alg-⟦∙⟧ (`∎ j) θ (refl , refl) = refl

  Relax : (d : Desc I) → Semantics d Var (𝓒ᴿ d)
  Relax d = record
    { th^𝓥 = th^Var
    ; var = λ k _ θ → `var (lookup (From⊑.toEnv θ) k)
    ; alg = λ t _ θ → `con (alg-⟦∙⟧ d θ t)
    }

  relax : (d : Desc I) → Γ' ⊑ Γ → CoDeBruijn.Tm d τ Γ' → DeBruijn.Tm d τ Γ
  relax d θ t = Sem.semantics (Relax d) identity t _ θ

module Tighten where
  tighten :
    (d : Desc I) →
    DeBruijn.Tm d τ Γ →
    CoDeBruijn.Tm d τ ⇑ Γ

  tighten-Scope :
    (Δ : List I) (d : Desc I) →
    DeBruijn.Scope (DeBruijn.Tm d) Δ τ Γ →
    CoDeBruijn.Scope (CoDeBruijn.Tm d) Δ τ ⇑ Γ

  tighten-⟦∙⟧ :
    (d d' : Desc I) →
    DeBruijn.⟦ d ⟧ (DeBruijn.Scope (DeBruijn.Tm d')) τ Γ →
    CoDeBruijn.⟦ d ⟧ (CoDeBruijn.Scope (CoDeBruijn.Tm d')) τ ⇑ Γ

  tighten d (`var k) = `var ↑ ⊑-from-Var k
  tighten d (`con t) = map⇑ `con (tighten-⟦∙⟧ d d t)

  tighten-Scope [] d t = tighten d t
  tighten-Scope Δ@(_ ∷ _) d t = Δ \\ᴿ tighten d t

  tighten-⟦∙⟧ (`σ A k) d' (a , t) = map⇑ (a ,_) (tighten-⟦∙⟧ (k a) d' t)
  tighten-⟦∙⟧ (`X Δ j d) d' (t₁ , t₂) = tighten-Scope Δ d' t₁ ,ᴿ tighten-⟦∙⟧ d d' t₂
  tighten-⟦∙⟧ (`∎ j) d' refl = (refl , refl) ↑ oe

module TightenSem where
  open import Data.Environment using (identity; th^Var; Kripke)
  open import Generic.DeBruijn.Semantics as Sem using (Semantics)

  alg-Kripke :
    {d : Desc I} (Δ : List I) →
    Kripke Var (λ σ → CoDeBruijn.Tm d σ ⇑_) Δ τ Γ →
    CoDeBruijn.Scope (CoDeBruijn.Tm d) Δ τ ⇑ Γ
  alg-Kripke [] t = t
  alg-Kripke Δ@(_ ∷ _) k = Δ \\ᴿ k (Data.Environment.pack (injectʳ _)) (Data.Environment.pack (injectˡ _))

  alg-⟦∙⟧ :
    (d : Desc I) {d' : Desc I} →
    DeBruijn.⟦ d ⟧ (Kripke Var (λ σ → CoDeBruijn.Tm d' σ ⇑_)) τ Γ →
    CoDeBruijn.⟦ d ⟧ (CoDeBruijn.Scope (CoDeBruijn.Tm d')) τ ⇑ Γ
  alg-⟦∙⟧ (`σ A k) (a , t) = map⇑ (a ,_) (alg-⟦∙⟧ (k a) t)
  alg-⟦∙⟧ (`X Δ j d) (t₁ , t₂) = alg-Kripke Δ t₁ ,ᴿ alg-⟦∙⟧ d t₂
  alg-⟦∙⟧ (`∎ j) refl = (refl , refl) ↑ oe

  Tighten : (d : Desc I) → Semantics d Var (λ τ → CoDeBruijn.Tm d τ ⇑_)
  Tighten d = record
    { th^𝓥 = th^Var
    ; var = λ k → `var ↑ ⊑-from-Var k
    ; alg = λ t → map⇑ `con (alg-⟦∙⟧ d t)
    }

  tighten : (d : Desc I) → DeBruijn.Tm d τ Γ → CoDeBruijn.Tm d τ ⇑ Γ
  tighten d = Sem.semantics (Tighten d) identity
