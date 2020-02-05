-- Math 52: Cheatsheet

--------------------------------
-- BASIC GOAL TRANSFORMATIONS --
--------------------------------

-- Conjunctive Goal
-- Use `split`:
example (P Q : Prop) : P ∧ Q :=
begin
split,
-- you can use braces to separate the two resulting goals
{ sorry },
{ sorry },
end

-- Conditional Goal
-- Use `intro`:
example (P Q : Prop) : P → Q :=
begin
intro H, -- you can give the hypothesis any name you want
sorry,
end

-- Universal Goal
-- Use `intro`:
example (U : Type) (P : U → Prop) : ∀ (x : U), P x :=
begin
intro x, -- you can rename the variable x if necessary
sorry,
end

-- Existential Goal
-- Use `existsi`:
example (U : Type) (P : U → Prop) : ∃ (x : U), P x :=
begin
existsi (sorry : U), -- you need to figure out what to put in
sorry,
end

---------------------------------
-- BASIC GIVEN TRANSFORMATIONS --
---------------------------------

-- Conjunctive Hypothesis
-- Use `cases`:
example (P Q R : Prop) (H : P ∧ Q) : R :=
begin
cases H with H₁ H₂,
sorry,
end

-- Disjunctive Hypothesis
-- Use `cases`:
example (P Q R : Prop) (H : P ∨ Q) : R :=
begin
cases H with H₁ H₂,
-- you can use braces to separate the two resulting goals.
{ sorry },
{ sorry },
end

-- Existential Hypothesis
-- Use `cases`:
example (U : Type) (P : U → Prop) (R : Prop)
  (H : ∃ (x : U), P x) : R :=
begin
cases H with x Hx, -- you can use any name you want for x
sorry,
end

-----------------------
-- COMMON IDENTITIES --
-----------------------

#check add_assoc -- (a + b) + c = a + (b + c)
#check add_comm -- a + b = b + a
#check add_zero -- a + 0 = a
#check zero_add -- 0 + a = a
#check mul_assoc -- (a * b) * c = a * (b * c)
#check mul_comm -- a * b = b * a
#check mul_one -- a * 1 = a
#check one_mul -- 1 * a = a
#check mul_zero -- a * 0 = 0
#check zero_mul -- 0 * a = 0
#check add_mul -- (a + b) * c = a * c + b * c
#check mul_add -- a * (b + c) = a * b + a * c

