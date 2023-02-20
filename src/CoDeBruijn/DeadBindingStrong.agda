-- Dead binding elimination, but in a single pass (equivalent to strongly live variable analysis)
-- Using co-de-Bruijn representation.
module CoDeBruijn.DeadBindingStrong where

open import Data.Nat using (_+_)
open import Data.List using (List ; _∷_ ; [] ; _++_)
open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; cong₂ ; sym ; trans)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Function using (_∘_ ; _$_ ; flip)

open import Core
open import CoDeBruijn.Lang
open import OPE

let-? : ∀ {σ τ Γ} → (Expr σ ×R ((σ ∷ []) ⊢ Expr τ)) Γ → Expr τ ⇑ Γ
let-? (pair (e₁ ↑ θ₁) (((oz o') \\ e₂) ↑ θ₂) c) = e₂ ↑ θ₂  -- remove binding
let-? (pair (e₁ ↑ θ₁) (((oz os) \\ e₂) ↑ θ₂) c) = Let (pair (e₁ ↑ θ₁) (((oz os) \\ e₂) ↑ θ₂) c) ↑ oi

lemma-let-? :
  (p : (Expr σ ×R ((σ ∷ []) ⊢ Expr τ)) Γ) (env : Env Γ) →
  let e' ↑ θ' = let-? p
  in eval (Let p) oi env ≡ eval e' θ' env
lemma-let-? (pair (e₁ ↑ θ₁) (((oz o') \\ e₂) ↑ θ₂) c) env =
  trans
    (lemma-eval e₂ (Cons (eval e₁ (θ₁ ₒ oi) env) env) θ₂ (oi o'))
    (cong (eval e₂ θ₂) (law-project-Env-oi env))
lemma-let-? (pair (e₁ ↑ θ₁) (((oz os) \\ e₂) ↑ θ₂) c) env = refl

lemma-let-?' :
  {Γₑ : Ctx} (p : (Expr σ ×R ((σ ∷ []) ⊢ Expr τ)) Γ) (env : Env Γₑ) (θ : Γ ⊑ Γₑ) →
  let e' ↑ θ' = let-? p
  in eval (Let p) θ env ≡ eval e' (θ' ₒ θ) env
lemma-let-?' p env θ =
  let pair (e₁ ↑ θ₁) ((ψ \\ e₂) ↑ θ₂) c = p
      e' ↑ θ' = let-? p
  in
    eval (Let p) θ env
  ≡⟨ refl ⟩
    eval e₂ (ψ ++⊑ (θ₂ ₒ θ)) (Cons (eval e₁ (θ₁ ₒ θ) env) env)
  ≡⟨ cong (λ x → eval e₂ _ (Cons x env)) (trans (lemma-eval e₁ env θ₁ θ) (cong (λ x → eval e₁ x (project-Env θ env)) (sym (law-ₒoi θ₁) ))) ⟩
    eval e₂ (ψ ++⊑ (θ₂ ₒ θ)) (Cons (eval e₁ (θ₁ ₒ oi) (project-Env θ env)) env)
  ≡⟨ {!!} ⟩  -- Should be doable, but might require a few basic laws.
            -- Instead, we could bake it into the lemma above from the beginning?
    eval e₂ (ψ ++⊑ (θ₂ ₒ oi)) (Cons (eval e₁ (θ₁ ₒ oi) (project-Env θ env)) (project-Env θ env))
  ≡⟨ lemma-let-? p (project-Env θ env) ⟩
    eval e' θ' (project-Env θ env)
  ≡⟨ sym (lemma-eval e' env θ' θ) ⟩
    eval e' (θ' ₒ θ) env
  ∎

mutual
  -- Also remove bindings that are tagged live in the input Expr,
  -- but where the body is revealed to not use the top variable after the recursive call.
  dbe : Expr τ Γ → Expr τ ⇑ Γ
  dbe Var =
    Var ↑ oz os
  dbe (App (pair (e₁ ↑ ϕ₁) (e₂ ↑ ϕ₂) c)) =
    map⇑ App (thin⇑ ϕ₁ (dbe e₁) ,R thin⇑ ϕ₂ (dbe e₂))
  dbe (Lam (_\\_ {bound = Γ'} ψ e)) =
    map⇑ (Lam ∘ map⊢ ψ) (Γ' \\R dbe e)
  dbe (Let p) =
    mult⇑ (map⇑ let-? (dbe-Let p))
  dbe (Val v) =
    Val v ↑ oz
  dbe (Plus (pair (e₁ ↑ ϕ₁) (e₂ ↑ ϕ₂) c)) =
    map⇑ Plus (thin⇑ ϕ₁ (dbe e₁) ,R thin⇑ ϕ₂ (dbe e₂))

  dbe-Let : (Expr σ ×R ((σ ∷ []) ⊢ Expr τ)) Γ → (Expr σ ×R ((σ ∷ []) ⊢ Expr τ)) ⇑ Γ
  dbe-Let (pair (e₁ ↑ ϕ₁) ((_\\_ {bound = Γ'} ψ e) ↑ ϕ₂) c) =
    thin⇑ ϕ₁ (dbe e₁) ,R thin⇑ ϕ₂ (map⇑ (map⊢ ψ) (Γ' \\R dbe e))

-- IDEA: We could show that this is a fixpoint? dbe (dbe e) ≡ dbe e

-- TODO: implicit args?
helper-assoc :
  ∀ {Γ Γ₁ Γ₂ Γ' Γ''} →
  (θ₁  : Γ  ⊑ Γ₁) →
  (θ₁' : Γ₁ ⊑ Γ') →
  (θ₂  : Γ  ⊑ Γ₂) →
  (θ₂' : Γ₂ ⊑ Γ') →
  (θ   : Γ' ⊑ Γ'') →
  θ₁ ₒ θ₁' ≡ θ₂ ₒ θ₂' →
  θ₁ ₒ θ₁' ₒ θ ≡ θ₂ ₒ θ₂' ₒ θ
helper-assoc θ₁ θ₁' θ₂ θ₂' θ h =
    θ₁ ₒ θ₁' ₒ θ
  ≡⟨ law-ₒₒ _ _ _ ⟩
    (θ₁ ₒ θ₁') ₒ θ
  ≡⟨  cong (_ₒ θ) h ⟩
    (θ₂ ₒ θ₂') ₒ θ
  ≡⟨ sym (law-ₒₒ _ _ _) ⟩
    θ₂ ₒ θ₂' ₒ θ
  ∎

-- TODO: factor out handling of _×R_ and _⊢_ ?

dbe-correct-Lam : 
  {Γₑ : Ctx} (l : ((σ ∷ []) ⊢ Expr τ) Γ) (env : Env Γₑ) (θ : Γ ⊑ Γₑ) →
  let _\\_ {bound = Γ'} ψ e₁ = l
      e₁' ↑ θ₁' = dbe e₁
      e = Lam l
      e' ↑ θ' = dbe e
  in
  (h : (v : ⟦ σ ⟧) → eval e₁' (θ₁' ₒ (ψ ++⊑ θ)) (Cons v env) ≡ eval e₁ (ψ ++⊑ θ) (Cons v env)) →
  eval e' (θ' ₒ θ) env ≡ eval e θ env
dbe-correct-Lam (_\\_ {bound = Γ'} ψ e₁) env θ h
  with dbe e₁
...  | e₁' ↑ θ₁
  with Γ' ⊣ θ₁
...  | ⊣r ϕ₁ ϕ₂ (refl , refl) =
  extensionality _ _ λ v →  -- TODO: move extensionality out?
      eval e₁' ((ϕ₁ ₒ ψ) ++⊑ (ϕ₂ ₒ θ)) (Cons v env)
    ≡⟨ cong (λ x → eval e₁' x (Cons v env)) (law-commute-ₒ++⊑ ϕ₁ ψ ϕ₂ θ) ⟩
      eval e₁' ((ϕ₁ ++⊑ ϕ₂) ₒ (ψ ++⊑ θ)) (Cons v env)
    ≡⟨ h v ⟩
      eval e₁ (ψ ++⊑ θ) (Cons v env)
    ∎

dbe-correct-×R :
  {Γₑ : Ctx}
  {τ₁ τ₂ τ : U} (eval-step : ⟦ τ₁ ⟧ → ⟦ τ₂ ⟧ → ⟦ τ ⟧) →
  (p : (Expr τ₁ ×R Expr τ₂) Γ) (env : Env Γₑ) (θ : Γ ⊑ Γₑ) →
  let pair (e₁ ↑ θ₁) (e₂ ↑ θ₂) c = p
      e₁' ↑ θ₁' = dbe e₁
      e₂' ↑ θ₂' = dbe e₂
      p' ↑ θ' = _,R_ {Expr _} {Expr _} (e₁' ↑ (θ₁' ₒ θ₁)) (e₂' ↑ (θ₂' ₒ θ₂))
  in
  (h₁ : (envₕ : Env Γₑ) (θₕ : Γ ⊑ Γₑ) → eval e₁' (θ₁' ₒ θ₁ ₒ θₕ) envₕ ≡ eval e₁ (θ₁ ₒ θₕ) envₕ) →
  (h₂ : (envₕ : Env Γₑ) (θₕ : Γ ⊑ Γₑ) → eval e₂' (θ₂' ₒ θ₂ ₒ θₕ) envₕ ≡ eval e₂ (θ₂ ₒ θₕ) envₕ) →
  eval-binop eval-step p' (θ' ₒ θ) env ≡ eval-binop eval-step p θ env
  --   eval-step (eval e₁'' (θ₁'' ₒ θ' ₒ θ) env) (eval e₂'' (θ₂'' ₒ θ' ₒ θ) env)
  -- ≡ eval-step (eval e₁ (θ₁ ₒ θ) env) (eval e₂ (θ₂ ₒ θ) env)
dbe-correct-×R eval-step (pair (e₁ ↑ θ₁) (e₂ ↑ θ₂) c) env θ h₁ h₂
  with dbe e₁   | dbe e₂
...  | e₁' ↑ θ₁' | e₂' ↑ θ₂'
  with cop (θ₁' ₒ θ₁) (θ₂' ₒ θ₂) 
...  | coproduct Γ' ψ θ₁'' θ₂'' p₁ p₂ c =
     eval-step
       (eval e₁' (θ₁'' ₒ ψ ₒ θ) env)
       (eval e₂' (θ₂'' ₒ ψ ₒ θ) env)
   ≡⟨ cong (λ x → eval-step (eval e₁' _ _) (eval e₂' x env)) (helper-assoc _ _ _ _ _ (sym p₂)) ⟩
     eval-step
       (eval e₁' (θ₁'' ₒ ψ ₒ θ) env)
       (eval e₂' (θ₂' ₒ θ₂ ₒ θ) env)
   ≡⟨ cong (λ x → eval-step (eval e₁' x env) _) (helper-assoc _ _ _ _ _ (sym p₁)) ⟩
     eval-step
       (eval e₁' (θ₁' ₒ θ₁ ₒ θ) env)
       (eval e₂' (θ₂' ₒ θ₂ ₒ θ) env)
   ≡⟨ cong₂ eval-step (h₁ env θ) (h₂ env θ) ⟩
    eval-step
      (eval e₁ (θ₁ ₒ θ) env)
      (eval e₂ (θ₂ ₒ θ) env)
  ∎

dbe-correct-Let : 
  {Γₑ : Ctx} (p : (Expr σ ×R ((σ ∷ []) ⊢ Expr τ)) Γ) (env : Env Γₑ) (θ : Γ ⊑ Γₑ) →
  let pair (e₁ ↑ θ₁) (l ↑ θ₂) c = p
      _\\_ {bound = Γ'} ψ e₂ = l
      e₁' ↑ θ₁' = dbe e₁
      e₂' ↑ θ₂' = dbe e₂
      p' ↑ θ' = dbe-Let p
  in
  (h₁ : (envₕ : Env Γₑ) (θₕ : Γ ⊑ Γₑ) → eval e₁' (θ₁' ₒ θ₁ ₒ θₕ) envₕ ≡ eval e₁ (θ₁ ₒ θₕ) envₕ) →
  (h₂ : (envₕ : Env (σ ∷ Γₑ)) (θₕ : Γ ⊑ Γₑ) → eval e₂' (θ₂' ₒ (ψ ++⊑ (θ₂ ₒ θₕ))) envₕ ≡ eval e₂ (ψ ++⊑ (θ₂ ₒ θₕ)) envₕ) →
  eval (Let p') (θ' ₒ θ) env ≡ eval (Let p) θ env
dbe-correct-Let (pair (e₁ ↑ θ₁) (_\\_ {bound = Γ'} ψ e₂ ↑ θ₂) c) env θ h₁ h₂ =
  let p' ↑ θ' = dbe-Let (pair (e₁ ↑ θ₁) (_\\_ {bound = Γ'} ψ e₂ ↑ θ₂) c)
  in
    eval (Let p') (θ' ₒ θ) env
  ≡⟨ {!!} ⟩
    {!!} -- (flip _$_)  (Let p') (θ' ₒ θ) env
  ≡⟨ {!!} ⟩
    {!eval-binop (flip _$_) !}
  ≡⟨ dbe-correct-×R (flip _$_) (pair (e₁ ↑ θ₁) (Lam (_\\_ {bound = Γ'} ψ e₂) ↑ θ₂) c) env θ
      (λ envₕ θₕ → h₁ envₕ θₕ)
      (λ envₕ θₕ → dbe-correct-Lam (_\\_ {bound = Γ'} ψ e₂) envₕ (θ₂ ₒ θₕ)
        λ v → h₂ (Cons v envₕ) θₕ) ⟩
    eval-binop (flip _$_) (pair (e₁ ↑ θ₁) (Lam (_\\_ {bound = Γ'} ψ e₂) ↑ θ₂) c) θ env
  ≡⟨ refl ⟩
    eval (Let (pair (e₁ ↑ θ₁) (_\\_ {bound = Γ'} ψ e₂ ↑ θ₂) c)) θ env
  ∎

dbe-correct :
  {Γₑ : Ctx} (e : Expr τ Γ) (env : Env Γₑ) (θ : Γ ⊑ Γₑ) →
  let e' ↑ θ' = dbe e
  in eval e' (θ' ₒ θ) env ≡ eval e θ env

dbe-correct Var env θ =
  cong (λ x → lookup Top (project-Env x env)) (law-oiₒ θ)

dbe-correct (App (pair (e₁ ↑ θ₁) (e₂ ↑ θ₂) cover)) env θ =
  dbe-correct-×R _$_ (pair (e₁ ↑ θ₁) (e₂ ↑ θ₂) cover) env θ
    (λ envₕ θₕ → dbe-correct e₁ envₕ (θ₁ ₒ θₕ))
    (λ envₕ θₕ → dbe-correct e₂ envₕ (θ₂ ₒ θₕ))

dbe-correct (App (pair (e₁ ↑ θ₁) (e₂ ↑ θ₂) cover)) env θ =
  let e = App (pair (e₁ ↑ θ₁) (e₂ ↑ θ₂) cover)
      e' ↑ θ' = dbe e
      e₁' ↑ θ₁' = dbe e₁
      e₂' ↑ θ₂' = dbe e₂
      pair (e₁'' ↑ θ₁'') (e₂'' ↑ θ₂'') c ↑ θ'' = thin⇑ θ₁ (dbe e₁) ,R thin⇑ θ₂ (dbe e₂)
      h₁ = dbe-correct e₁ env (θ₁ ₒ θ)
      h₂ = dbe-correct e₂ env (θ₂ ₒ θ)
  in
    eval e' (θ' ₒ θ) env
  ≡⟨ refl ⟩
    _$_ (eval e₁'' (θ₁'' ₒ θ'' ₒ θ) env) (eval  e₂'' (θ₂'' ₒ θ'' ₒ θ) env)
  ≡⟨ {!!} ⟩
    _$_ (eval e₁' (θ₁' ₒ θ₁ ₒ θ) env) (eval e₂' (θ₂' ₒ θ₂ ₒ θ) env)
  ≡⟨ cong₂ _$_ h₁ h₂ ⟩
    _$_ (eval e₁ (θ₁ ₒ θ) env) (eval e₂ (θ₂ ₒ θ) env)
  ≡⟨ refl ⟩
    eval e θ env
  ∎
dbe-correct (App (pair (e₁ ↑ ϕ₁) (e₂ ↑ ϕ₂) cover)) env θ
  with dbe e₁   | dbe e₂   | dbe-correct e₁ env (ϕ₁ ₒ θ) | dbe-correct e₂ env (ϕ₂ ₒ θ) 
...  | e₁' ↑ θ₁ | e₂' ↑ θ₂ | h₁                          | h₂
  with cop (θ₁ ₒ ϕ₁) (θ₂ ₒ ϕ₂) 
...  | coproduct Γ' ψ θ₁' θ₂' p₁ p₂ c =
  let H e p env = cong (λ x → eval e x env) (helper-assoc _ _ _ _ _ (sym p))
      K e p env = cong (λ x → eval e x env) (helper-assoc _ _ _ _ _ (sym p))
  in
    eval e₁' (θ₁' ₒ ψ ₒ θ) env
      (eval e₂' (θ₂' ₒ ψ ₒ θ) env)
  -- ≡⟨ cong (λ x → eval e₁' _ _ (eval e₂' x env)) (helper-assoc _ _ _ _ _ (sym p₂)) ⟩
  --   eval e₁' (θ₁' ₒ ψ ₒ θ) env
  --     (eval e₂' (θ₂ ₒ ϕ₂ ₒ θ) env)
  -- ≡⟨ cong (λ x → eval e₁' x env _) (helper-assoc _ _ _ _ _ (sym p₁)) ⟩
  --   eval e₁' (θ₁ ₒ ϕ₁ ₒ θ) env
  --     (eval e₂' (θ₂ ₒ ϕ₂ ₒ θ) env)
  -- ≡⟨ cong₂ _$_ h₁ h₂ ⟩
  ≡⟨ cong₂ _$_ (trans (H e₁' p₁ env) h₁) (trans (K e₂' p₂ env) h₂) ⟩
    eval e₁ (ϕ₁ ₒ θ) env
      (eval e₂ (ϕ₂ ₒ θ) env)
  ∎

-- dbe-correct-⊢ :
dbe-correct (Lam (_\\_ {bound = Γ'} ψ e₁)) env θ =
  dbe-correct-Lam (ψ \\ e₁) env θ  λ v → dbe-correct e₁ (Cons v env) (ψ ++⊑ θ)
  
dbe-correct (Lam (_\\_ {bound = Γ'} ψ e₁)) env θ =
  extensionality _ _ λ v →
    let e = Lam (ψ \\ e₁)
        e' ↑ θ' = dbe e
        e₁' ↑ θ₁' = dbe e₁
        (ψ' \\ e₁'') ↑ θ'' = Γ' \\R dbe e₁
        h₁ = dbe-correct e₁ (Cons v env) (ψ ++⊑ θ)
    in
    --   eval e' (θ' ₒ θ) env v
    -- ≡⟨ refl ⟩
      eval e₁'' ((ψ' ₒ ψ) ++⊑ (θ'' ₒ θ)) (Cons v env)
    ≡⟨ {!!} ⟩
      eval e₁' (θ₁' ₒ (ψ ++⊑ θ)) (Cons v env)
    ≡⟨ h₁ ⟩
      eval e₁ (ψ ++⊑ θ) (Cons v env)
    -- ≡⟨ refl ⟩
    --   eval e θ env v
    ∎
dbe-correct (Lam (_\\_ {bound = Γ'} ψ e)) env θ
  with dbe e   | dbe-correct e
...  | e' ↑ θ' | h
  with Γ' ⊣ θ'
...  | ⊣r ϕ₁ ϕ₂ (refl , refl) =
  extensionality _ _ λ v →
      eval e' ((ϕ₁ ₒ ψ) ++⊑ (ϕ₂ ₒ θ)) (Cons v env)
    ≡⟨ cong (λ x → eval e' x (Cons v env)) (law-commute-ₒ++⊑ ϕ₁ ψ ϕ₂ θ) ⟩
      eval e' ((ϕ₁ ++⊑ ϕ₂) ₒ (ψ ++⊑ θ)) (Cons v env)
    ≡⟨ h (Cons v env) (ψ ++⊑ θ) ⟩
      eval e (ψ ++⊑ θ) (Cons v env)
    ∎

dbe-correct (Let {σ} (pair (e₁ ↑ θ₁) (_\\_ {bound = Γ'} ψ e₂ ↑ θ₂) c)) env θ =
  let p = pair (e₁ ↑ θ₁) (_\\_ {bound = Γ'} ψ e₂ ↑ θ₂) c
      p' ↑ θ' = dbe-Let p
      e' ↑ θ'' = let-? p'
  in
    eval e' ((θ'' ₒ θ') ₒ θ) env
  ≡⟨ cong (λ x → eval e' x env) (sym (law-ₒₒ θ'' θ' θ)) ⟩
    eval e' (θ'' ₒ θ' ₒ θ) env
  ≡⟨ sym (lemma-let-?' p' env (θ' ₒ θ)) ⟩
    eval (Let p') (θ' ₒ θ) env
  ≡⟨ dbe-correct-Let (pair (e₁ ↑ θ₁) ((ψ \\ e₂) ↑ θ₂) c) env θ
      (λ envₕ θₕ → dbe-correct e₁ envₕ (θ₁ ₒ θₕ))
      (λ envₕ θₕ → dbe-correct e₂ envₕ (ψ ++⊑ (θ₂ ₒ θₕ))) ⟩
    eval (Let p) θ env
  ∎

dbe-correct (Let {σ} (pair (e₁ ↑ θ₁) (_\\_ {bound = Γ'} ψ e₂ ↑ θ₂) c)) env θ
  with dbe e₁    | dbe e₂    | dbe-correct e₁ | dbe-correct e₂
...  | e₁' ↑ θ₁' | e₂' ↑ θ₂' | h₁             | h₂
  with Γ' ⊣ θ₂'               | cop (θ₁' ₒ θ₁) ({!!} ₒ θ₂)
...  | ⊣r ϕ₁ ϕ₂ (refl , refl) | coproduct Γ' ψ' θ₁'' θ₂'' p₁ p₂ c =
  let h₁ = h₁ env (θ₁ ₒ θ)
      h₂ = h₂ (Cons (eval e₁ (θ₁ ₒ θ) env) env) (ψ ++⊑ (θ₂ ₒ θ))
  in
    {!!}
  ≡⟨ {!!} ⟩
    eval e₂' ((ϕ₁ ++⊑ ϕ₂) ₒ (ψ ++⊑ (θ₂ ₒ θ))) (Cons (eval e₁' (θ₁' ₒ θ₁ ₒ θ) env) env)
  ≡⟨ cong (λ x → eval e₂' _ (Cons x env)) h₁ ⟩
    eval e₂' ((ϕ₁ ++⊑ ϕ₂) ₒ (ψ ++⊑ (θ₂ ₒ θ))) (Cons (eval e₁ (θ₁ ₒ θ) env) env)
  ≡⟨ h₂ ⟩
    eval e₂ (ψ ++⊑ (θ₂ ₒ θ)) (Cons (eval e₁ (θ₁ ₒ θ) env) env)
  ∎

dbe-correct (Val v) env θ = refl

dbe-correct (Plus (pair (e₁ ↑ θ₁) (e₂ ↑ θ₂) cover)) env θ =
  dbe-correct-×R _+_ (pair (e₁ ↑ θ₁) (e₂ ↑ θ₂) cover) env θ
    (λ envₕ θₕ → dbe-correct e₁ envₕ (θ₁ ₒ θₕ))
    (λ envₕ θₕ → dbe-correct e₂ envₕ (θ₂ ₒ θₕ))
