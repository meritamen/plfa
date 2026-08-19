module plfa.part1.Induction where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)

-- Exercise operators

-- Logical "and" and "or" have an identity and are associative, commutative, and distribute over one another.
-- String concatenation has an identity and is associative but is not commutative.


_ : (3 + 4) + 5 ≡ 3 + (4 + 5)
_ =
  begin
    (3 + 4) + 5
  ≡⟨⟩
    7 + 5
  ≡⟨⟩
    12
  ≡⟨⟩
    3 + 9
  ≡⟨⟩
    3 + (4 + 5)
  ∎

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p =
  begin
    (zero + n) + p
  ≡⟨⟩
    n + p
  ≡⟨⟩
    zero + (n + p)
  ∎
+-assoc (suc m) n p =
  begin
    (suc m + n) + p
  ≡⟨⟩
    suc (m + n) + p
  ≡⟨⟩
    suc ((m + n) + p)
  ≡⟨ cong suc (+-assoc m n p) ⟩
    suc (m + (n + p))
  ≡⟨⟩
    suc m + (n + p)
  ∎

+-assoc-0 : ∀ (n p : ℕ) → (0 + n) + p ≡ 0 + (n + p)
+-assoc-0 n p =
  begin
    (0 + n) + p
  ≡⟨⟩
    n + p
  ≡⟨⟩
    0 + (n + p)
  ∎

+-assoc-1 : ∀ (n p : ℕ) → (1 + n) + p ≡ 1 + (n + p)
+-assoc-1 n p =
  begin
    (1 + n) + p
  ≡⟨⟩
    suc (0 + n) + p
  ≡⟨⟩
    suc ((0 + n) + p)
  ≡⟨ cong suc (+-assoc-0 n p) ⟩
    suc (0 + (n + p))
  ≡⟨⟩
    1 + (n + p)
  ∎

+-assoc-2 : ∀ (n p : ℕ) → (2 + n) + p ≡ 2 + (n + p)
+-assoc-2 n p =
  begin
    (2 + n) + p
  ≡⟨⟩
    suc (1 + n) + p
  ≡⟨⟩
    suc ((1 + n) + p)
  ≡⟨ cong suc (+-assoc-1 n p) ⟩
    suc (1 + (n + p))
  ≡⟨⟩
    2 + (n + p)
  ∎

+-identityʳ : ∀ (m : ℕ) → m + zero ≡ m
+-identityʳ zero =
  begin
    zero + zero
  ≡⟨⟩
    zero
  ∎
+-identityʳ (suc m) =
  begin
    suc m + zero
  ≡⟨⟩
    suc (m + zero)
  ≡⟨ cong suc (+-identityʳ m) ⟩
    suc m
  ∎

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n =
  begin
    zero + suc n
  ≡⟨⟩
    suc n
  ≡⟨⟩
    suc (zero + n)
  ∎
+-suc (suc m) n =
  begin
    suc m + suc n
  ≡⟨⟩
    suc (m + suc n)
  ≡⟨ cong suc (+-suc m n) ⟩
    suc (suc (m + n))
  ≡⟨⟩
    suc (suc m + n)
  ∎

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
  begin
    m + zero
  ≡⟨ +-identityʳ m ⟩
    m
  ≡⟨⟩
    zero + m
  ∎
+-comm m (suc n) =
  begin
    m + suc n
  ≡⟨ +-suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨⟩
    suc n + m
  ∎

+-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange m n p q =
  begin
    (m + n) + (p + q)
  ≡⟨ sym (+-assoc (m + n) p q) ⟩
    ((m + n) + p) + q
  ≡⟨ cong (_+ q) (+-assoc m n p) ⟩
    (m + (n + p)) + q
  ∎

-- Exercise finite-+-assoc

-- In the beginning, we know nothing about associativity.

-- On the first day, we know zero.
-- 0 : ℕ

-- On the second day, we know one, and associativity of 0.
-- 0 : ℕ
-- 1 : ℕ    (0 + 0) + 0 ≡ 0 + (0 + 0)

-- On the third day, we know two, and associativity of 1 and 0, 1 and 1.
-- 0 : ℕ
-- 1 : ℕ    (0 + 0) + 0 ≡ 0 + (0 + 0)
-- 2 : ℕ    (1 + 1) + 1 ≡ 1 + (1 + 1)
--          (1 + 0) + 0 ≡ 1 + (0 + 0)     ...    (0 + 1) + 0 ≡ 0 + (1 + 0)    ...

-- On the fourth day, we know three, and associativity of 1 and 2, 0 and 2, 2 and 2.
-- 0 : ℕ
-- 1 : ℕ    (0 + 0) + 0 ≡ 0 + (0 + 0)
-- 2 : ℕ    (1 + 1) + 1 ≡ 1 + (1 + 1)
--          (1 + 0) + 0 ≡ 1 + (0 + 0)     ...    (0 + 1) + 0 ≡ 0 + (1 + 0)    ...
-- 3 : ℕ    (2 + 2) + 2 ≡ 2 + (2 + 2)
--          (1 + 2) + 2 ≡ 1 + (2 + 2)     ...    (2 + 1) + 1 ≡ 2 + (1 + 2)    ...
--          (0 + 2) + 2 ≡ 0 + (2 + 2)     ...    (2 + 0) + 0 ≡ 2 + (0 + 0)    ...

+-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc′ zero n p = refl
+-assoc′ (suc m) n p rewrite +-assoc′ m n p = refl

+-identity′ : ∀ (n : ℕ) → n + zero ≡ n
+-identity′ zero = refl
+-identity′ (suc n) rewrite +-identity′ n = refl

+-suc′ : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc′ zero n = refl
+-suc′ (suc m) n rewrite +-suc′ m n = refl

+-comm′ : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm′ m zero rewrite +-identity′ m = refl
+-comm′ m (suc n) rewrite +-suc′ m n | +-comm′ m n = refl

-- Exercise +-swap
+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p rewrite sym (+-assoc m n p) | +-comm m n | +-assoc n m p = refl

-- Exercise *-distrib-+
*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ zero n p = refl
*-distrib-+ (suc m) n p rewrite *-distrib-+ m n p | sym (+-assoc p (m * p) (n * p)) = refl

-- Exercise *-comm

n*0≡0 : ∀ (n : ℕ) → n * 0 ≡ 0
n*0≡0 0 = refl
n*0≡0 (suc n) rewrite n*0≡0 n = refl

*-suc : ∀ m n → m * suc n ≡ m + m * n
*-suc zero n = refl
*-suc (suc m) n rewrite sym (+-assoc m n (m * n)) | +-comm m n | +-assoc n m (m * n) | *-suc m n = refl

*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm m zero rewrite n*0≡0 m =  refl
*-comm m (suc n) rewrite *-suc m n | *-comm m n = refl

-- Exercise 0∸n≡0
0∸n≡0 : ∀ (n : ℕ) → zero ∸ n ≡ zero
0∸n≡0 zero = refl
0∸n≡0 (suc n) = refl

-- Exercise ∸-+-assoc

zero∸p≡zero : ∀ (m : ℕ) → zero ∸ m ≡ zero
zero∸p≡zero zero = refl
zero∸p≡zero (suc m) = refl

∸-+-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-+-assoc m zero p = refl
∸-+-assoc zero (suc n) p rewrite zero∸p≡zero p = refl
∸-+-assoc (suc m) (suc n) p rewrite ∸-+-assoc m n p = refl

-- Exercise +*^

*-assoc : ∀ (m n p : ℕ) → m * n * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p rewrite *-distrib-+ n (m * n) p | *-assoc m n p = refl

^-distribˡ-+-* : ∀ (m n p : ℕ) → m ^ (n + p) ≡ (m ^ n) * (m ^ p)
^-distribˡ-+-* m 0 p rewrite +-comm (m ^ p) 0 = refl
^-distribˡ-+-* m (suc n) p rewrite ^-distribˡ-+-* m n p | *-assoc m (m ^ n) (m ^ p) = refl

^-distribʳ-* : ∀ (m n p : ℕ) → (m * n) ^ p ≡ (m ^ p) * (n ^ p)
^-distribʳ-* m n zero = refl
^-distribʳ-* m n (suc p) rewrite ^-distribʳ-* m n p | *-assoc m n (m ^ p * n ^ p) | *-assoc m (m ^ p) (n * n ^ p) | sym (*-assoc n (m ^ p) (n ^ p)) | sym (*-assoc (m ^ p) n (n ^ p)) | *-comm n (m ^ p) = refl

^-*-assoc : ∀ (m n p : ℕ) → (m ^ n) ^ p ≡ m ^ (n * p)
^-*-assoc m n 0 rewrite *-comm n 0 = refl
^-*-assoc m n (suc p) rewrite ^-*-assoc m n p | *-suc n p | ^-distribˡ-+-* m n (n * p) = refl

-- Exercise Bin-laws
data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (b O) = b I
inc (b I) = inc b O

to : ℕ → Bin
to 0 = ⟨⟩ O
to (suc n) = inc (to n)

from : Bin → ℕ
from ⟨⟩ = 0
from (b O) = 2 * (from b)
from (b I) = 2 * (from b) + 1

from-inc-b≡suc-from-b : ∀ (b : Bin) → from (inc b) ≡ suc (from b)
from-inc-b≡suc-from-b ⟨⟩ = refl
from-inc-b≡suc-from-b (b O) rewrite +-identityʳ (from b) | +-comm (from b + from b) 1 = refl
from-inc-b≡suc-from-b (b I) rewrite +-identityʳ (from (inc b)) | +-identityʳ (from b) | from-inc-b≡suc-from-b b | +-comm (from b + from b) 1 | +-suc (from b) (from b) = refl

-- to (from b) ≡ b doesn't hold
counterexample : to (from (⟨⟩ O O I O I I)) ≡ ⟨⟩ I O I I
counterexample = refl

from-to-n≡n : ∀ (n : ℕ) → from (to n) ≡ n
from-to-n≡n zero = refl
from-to-n≡n (suc n) rewrite from-inc-b≡suc-from-b (to n) | from-to-n≡n n = refl
