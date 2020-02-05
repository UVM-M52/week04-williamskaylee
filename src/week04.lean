-- Math 52: Week 4

import .utils.int_refl

-- Lakins Definition 1.2.1:
definition is_even (n : ℤ) := ∃ (k : ℤ), n = 2 * k
definition is_odd (n : ℤ) := ∃ (k : ℤ), n = 2 * k + 1

-- Lakins Definition 2.1.1: Let a, b ∈ ℤ.
-- a divides b if there exists n ∈ ℤ such that b = an.
-- We write a ∣ b for "a divides b" and say that a is 
-- a divisor of b.
definition divides (a b : ℤ) : Prop := ∃ (n : ℤ), a * n = b

-- The notation `a ∣ b` can be used for `divides a b`
local infix ∣ := divides

-- Lakins Example 2.1.2:
example : 3 ∣ 12 :=
begin
unfold divides,
existsi (4:ℤ),
refl,
end

-- Theorem: For every integer a, a ∣ a.
theorem divides_refl : ∀ (a : ℤ), a ∣ a :=
begin
intro a,
unfold divides,
existsi (1:ℤ),
calc a * 1 = a : by rw mul_one,
end
-- Proof: Let a ∈ ℤ be arbitrary. We must show that a ∣ a; 
-- i.e., we must find an integer k such that a = a * k. 
-- Since a = a * 1 and 1 is an integer, we see that
-- a ∣ a is true. □

-- Lakins Proposition 2.1.3: For all integers a, b, c,
-- if a ∣ b and b ∣ c, then a ∣ c.
theorem divides_trans : ∀ (a b c : ℤ), a ∣ b ∧ b ∣ c → a ∣ c :=
begin
sorry
end
-- Proof: Let a,b,c ∈ ℤ be arbitrary and assume that 
-- a ∣ b and b ∣ c. We must show that a ∣ c; i.e., we
-- must find an integer k such that c = a * k.
-- 
-- Since a ∣ b, by Definition 2.1.1 we may fix n ∈ ℤ
-- such that b = a * n. Similarly, since b | c, we may
-- fix m ∈ ℤ such that c = b * m, again by Definition
-- 2.1.1. Then
--   c = b * m = (a * n) * m = a * (n * m),
-- since multiplication of integers is associative
-- (Basic Properties of Integers 1.2.3). Since 
-- n * m ∈ ℤ, we have proved that a ∣ c, by
-- Definition 2.1.1, as desired. 􏰟

-- Lakins Exercise 2.1.1: Let a,b, and c be integers.
-- For all integers m and n, if a ∣ b and a ∣ c, then
-- a ∣ (bm + cn).
theorem L211 : ∀ (a b c m n : ℤ), a ∣ b ∧ a ∣ c → a ∣ (b * m + c * n) :=
begin
sorry
end

-- Theorem: For every integer a, a is even if and only if 2 ∣ a.
theorem is_even_iff_two_divides : ∀ (a : ℤ), is_even a ↔ 2 ∣ a :=
begin
sorry
end

-- We will prove this fact later after we discuss induction.
-- For now we take it as an axiom, i.e., as statement that we
-- take as true without proof.
axiom even_or_odd (a : ℤ) : is_even a ∨ is_odd a

-- Lakins Theorem 2.1.9: For all integers a, a(a + 1) is even.
theorem even_product : ∀ (a : ℤ), is_even (a * (a + 1)) :=
begin
sorry
end
-- Proof: Let a ∈ ℤ. We show that a(a + 1) is even by 
-- considering two cases.
-- 
-- Case I: a is even.
-- Then 2 ∣ a, by Definition 1.2.1. Since a ∣ a(a + 1) 
-- by Definition 2.1.1, we have that 2 ∣ a(a + 1) since 
-- the divisibility relation is transitive (Proposition 
-- 2.1.3). Hence a(a + 1) is even.
--
-- Case II: a is not even.
-- Since a is not even, we know that a is odd. Then
-- a+1 is even by Exercise 1.2.2b. Then, using an 
-- argument similar to that of Case I, we have that
-- 2 ∣ (a+1) and (a+1) ∣ a(a+1), and hence 2 ∣ a(a+1) 
-- by Proposition 2.1.3. Thus a(a + 1) is even.
-- 
-- Hence, since we have considered all possible cases
-- for the integer a, we have proved that for all
-- integers a, a(a + 1) is even. 􏰟
