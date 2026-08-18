import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; step-≡-∣; _∎)

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

-- Exercise seven
seven : ℕ
seven = suc (suc (suc (suc (suc (suc (suc zero))))))

{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ
zero + n = n
(suc m) + n = suc (m + n)

_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩    -- is shorthand for
    (suc (suc zero)) + (suc (suc (suc zero)))
  ≡⟨⟩    -- inductive case
    suc ((suc zero) + (suc (suc (suc zero))))
  ≡⟨⟩    -- inductive case
    suc (suc (zero + (suc (suc (suc zero)))))
  ≡⟨⟩    -- base case
    suc (suc (suc (suc (suc zero))))
  ≡⟨⟩    -- is longhand for
    5
  ∎

_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩
    suc (1 + 3)
  ≡⟨⟩
    suc (suc (0 + 3))
  ≡⟨⟩
    suc (suc 3)
  ≡⟨⟩
    5
  ∎

_ : 2 + 3 ≡ 5
_ = refl

-- exercise +-example
_ : 3 + 4 ≡ 7
_ =
  begin
    3 + 4
  ≡⟨⟩
    (suc (suc (suc zero))) + (suc (suc (suc (suc zero))))
  ≡⟨⟩
    suc ((suc (suc zero)) + (suc (suc (suc (suc zero)))))
  ≡⟨⟩
    suc (suc ((suc zero) + (suc (suc (suc (suc zero))))))
  ≡⟨⟩
    suc (suc (suc (zero + (suc (suc (suc (suc zero)))))))
  ≡⟨⟩
    suc (suc (suc (suc (suc (suc (suc zero))))))
  ≡⟨⟩
    7
  ∎

_*_ : ℕ → ℕ → ℕ
zero * n = zero
(suc m) * n = n + (m * n)

_ : 2 * 3 ≡ 6
_ =
  begin
    2 * 3
  ≡⟨⟩    -- inductive case
    3 + (1 * 3)
  ≡⟨⟩    -- inductive case
    3 + (3 + (0 * 3))
  ≡⟨⟩    -- base case
    3 + (3 + 0)
  ≡⟨⟩    -- simplify
    6
  ∎

-- exercise *-example
_ =
  begin
    3 * 4
  ≡⟨⟩
    4 + (2 * 4)
  ≡⟨⟩
    4 + (4 + (1 * 4))
  ≡⟨⟩
    4 + (4 + (4 + (0 * 4)))
  ≡⟨⟩
    4 + (4 + (4 + 0))
  ≡⟨⟩
    12
  ∎

-- exercise _^_
_^_ : ℕ → ℕ → ℕ
m ^ 0 = 1
m ^ (suc n) = m * (m ^ n)

_ =
  begin
    3 ^ 4
  ≡⟨⟩
    3 * (3 ^ 3)
  ≡⟨⟩
    3 * (3 * (3 ^ 2))
  ≡⟨⟩
    3 * (3 * (3 * (3 ^ 1)))
  ≡⟨⟩
    3 * (3 * (3 * (3 * (3 ^ 0))))
  ≡⟨⟩
    3 * (3 * (3 * (3 * 1)))
  ≡⟨⟩
    81
  ∎

_∸_ : ℕ → ℕ → ℕ
m ∸ zero = m
zero ∸ suc n = zero
suc m ∸ suc n = m ∸ n

_ =
  begin
    3 ∸ 2
  ≡⟨⟩
    2 ∸ 1
  ≡⟨⟩
    1 ∸ 0
  ≡⟨⟩
    1
  ∎

_ =
  begin
    2 ∸ 3
  ≡⟨⟩
    1 ∸ 2
  ≡⟨⟩
    0 ∸ 1
  ≡⟨⟩
    0
  ∎

-- exercise ∸-example₁ and ∸-example₂
_ =
  begin
    5 ∸ 3
  ≡⟨⟩
    4 ∸ 2
  ≡⟨⟩
    3 ∸ 1
  ≡⟨⟩
    2 ∸ 0
  ≡⟨⟩
    2
  ∎

_ =
  begin
    3 ∸ 5
  ≡⟨⟩
    2 ∸ 4
  ≡⟨⟩
    1 ∸ 3
  ≡⟨⟩
    0 ∸ 2
  ≡⟨⟩
    0
  ∎

infixl 6  _+_  _∸_
infixl 7  _*_

{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _∸_ #-}

-- exercise Bin
data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (⟨⟩ O) = ⟨⟩ I
inc (⟨⟩ I) = ⟨⟩ I O
inc (l O O) = l O I
inc (l I O) = l I I
inc (l O I) = l I O
inc (l I I) = (inc l) O O

_ =
  begin
    inc (⟨⟩ O)
  ≡⟨⟩
    ⟨⟩ I
  ∎

_ =
  begin
    inc (⟨⟩ I)
  ≡⟨⟩
    ⟨⟩ I O
  ∎

_ =
  begin
    inc (⟨⟩ I O)
  ≡⟨⟩
    ⟨⟩ I I
  ∎

_ =
  begin
    inc (⟨⟩ I I)
  ≡⟨⟩
    ⟨⟩ I O O
  ∎

_ =
  begin
    inc (⟨⟩ I O O)
  ≡⟨⟩
    ⟨⟩ I O I
  ∎

to : ℕ → Bin
to 0 = ⟨⟩ O
to (suc n) = inc (to n)

_ =
  begin
    to 0
  ≡⟨⟩
    ⟨⟩ O
  ∎

_ =
  begin
    to 1
  ≡⟨⟩
    ⟨⟩ I
  ∎

_ =
  begin
    to 2
  ≡⟨⟩
    ⟨⟩ I O
  ∎

_ =
  begin
    to 3
  ≡⟨⟩
    ⟨⟩ I I
  ∎

_ =
  begin
    to 4
  ≡⟨⟩
    ⟨⟩ I O O
  ∎

from : Bin → ℕ
from ⟨⟩ = 0
from (⟨⟩ O) = 0
from (⟨⟩ I) = 1
from (l O O) = 4 * from l
from (l O I) = 4 * from l + 1
from (l I O) = 4 * from l + 2
from (l I I) = 4 * from l + 3

_ =
  begin
    from (⟨⟩ O)
  ≡⟨⟩
    0
  ∎

_ =
  begin
    from (⟨⟩ I)
  ≡⟨⟩
    1
  ∎

_ =
  begin
    from (⟨⟩ I O)
  ≡⟨⟩
    2
  ∎

_ =
  begin
    from (⟨⟩ I I)
  ≡⟨⟩
    3
  ∎

_ =
  begin
    from (⟨⟩ I O O)
  ≡⟨⟩
    4
  ∎


-- Representations are not unique due to leading zeros
_ : from (⟨⟩ I O I I) ≡ from (⟨⟩ O O I O I I)
_ = refl
