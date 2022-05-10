module Examples where

open import Data.List using (List ; _∷_ ; [])
open import Data.Nat renaming (ℕ to Nat ; zero to Zero ; suc to Succ)
open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import Lang
open import Subset
open import Live

-- Examples

-- let x = 1 in let y = x in 2
ex-unused : Expr Γ NAT
ex-unused = Let (Val 1) (Let (Var Top) (Val 2))

test-ex-unused : {env : Env Γ} → eval ex-unused env ≡ 2
test-ex-unused = refl

count-ex-unused : num-bindings (ex-unused {Γ}) ≡ 2
count-ex-unused = refl

optimize-ex-unused :
  let (Δ , (H , e)) = optimize Empty (ex-unused {[]}) in
    e ≡ Let (Val 1) (Val 2)
optimize-ex-unused = refl

optimize²-ex-unused :
  let (Δ , (H , e)) = optimize Empty (ex-unused {[]}) in
  let (Δ' , (H' , e')) = optimize Δ e in
    e' ≡ Val 2
optimize²-ex-unused = refl

fix-optimize-ex-unused :
  let (Δ , (H , e)) = fix-optimize Empty (ex-unused {[]}) in
    e ≡ Val 2
fix-optimize-ex-unused = refl


-- λ a → let x = a in let y = 1 in let z = x + 5 in y + a
ex-unused-2 : Expr (NAT ∷ Γ) NAT
ex-unused-2 =
  Let (Var Top)
    (Let (Val 1)
      (Let (Var (Pop Top))
        (Plus (Var (Pop Top)) (Var (Pop (Pop (Pop Top)))))))

-- λ a → in let y = 1 in y + a
ex-unused-2-opt : Expr (NAT ∷ Γ) NAT
ex-unused-2-opt =
  Let (Val 1)
    (Plus (Var Top) (Var (Pop (Top))))

test-ex-unused-2 : (env : Env Γ) (n : Nat) → eval ex-unused-2 (Cons n env) ≡ Succ n
test-ex-unused-2 env n = refl

count-ex-unused-2 : num-bindings (ex-unused-2 {Γ}) ≡ 3
count-ex-unused-2 = refl

count-fix-optimize-ex-unused-2 :
  let (Δ , (H , e)) = fix-optimize (Keep Empty) (ex-unused-2 {[]}) in
    e ≡ ex-unused-2-opt {[]}
count-fix-optimize-ex-unused-2 = refl
