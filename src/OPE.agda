module OPE where

open import Data.List using (_∷_ ; [])

open import Lang

data OPE : Ctx → Ctx → Set where
  Empty : OPE [] []
  Drop : {Γ' Γ : Ctx} (τ : U) → OPE Γ' Γ → OPE Γ' (τ ∷ Γ)
  Keep : {Γ' Γ : Ctx} (τ : U) → OPE Γ' Γ → OPE (τ ∷ Γ') (τ ∷ Γ)

ope-id : (Γ : Ctx) → OPE Γ Γ
ope-id [] = Empty
ope-id (x ∷ Γ) = Keep x (ope-id Γ)

ope-trans : ∀ {Γ₁ Γ₂ Γ₃} → OPE Γ₁ Γ₂ → OPE Γ₂ Γ₃ → OPE Γ₁ Γ₃
ope-trans Empty b = b
ope-trans a (Drop τ b) = Drop τ (ope-trans a b)
ope-trans (Drop .τ a) (Keep τ b) = Drop τ (ope-trans a b)
ope-trans (Keep .τ a) (Keep τ b) = Keep τ (ope-trans a b)

project-Env : ∀ {Γ' Γ} → OPE Γ' Γ → Env Γ → Env Γ'
project-Env Empty env = env
project-Env (Keep τ ope) (Cons v env) = Cons v (project-Env ope env)
project-Env (Drop τ ope) (Cons v env) = project-Env ope env
