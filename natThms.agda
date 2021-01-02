module natThms where

open import lib

-- this function divides a natural number by 2, dropping any remainder
div2 : ℕ → ℕ
div2 0 = 0
div2 1 = 0
div2 (suc (suc x)) = suc (div2 x)

div2-double : ∀(x : ℕ) → (div2 (x * 2)) ≡ x
div2-double zero = refl
div2-double (suc x) rewrite div2-double (x)  = refl

{- Hint: consider the same cases as in the definition of div2: 0, 1, (suc (suc x)).
   The case for 1 is impossible, so you can just drop that case or use the 
   absurd pattern for the proof of is-even 1 ≡ tt. -}
div2-even : ∀(x : ℕ) → is-even x ≡ tt → div2 x ≡ div2 (suc x)
div2-even zero x = refl
div2-even (suc (suc x))y rewrite div2-even x y = refl

-- same hint as for div2-even, except now the 0 case is impossible
div2-odd : ∀(x : ℕ) → is-odd x ≡ tt → div2 (suc x) ≡ suc (div2 x)
div2-odd (suc(suc x))y rewrite div2-odd x y = refl
div2-odd (suc zero) y  = refl

{- hint: do *not* do induction on x.  Look at the definitions of square and pow. 
   There are lemmas about multiplication in the IAL that will help you (nat-thms.agda). -}
square-square : ∀(x : ℕ) → square (square x) ≡ x pow 4
square-square x rewrite *1{x} | *assoc x x ( x * x )  = refl
