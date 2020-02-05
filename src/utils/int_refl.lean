
@[derive decidable_eq]
inductive horner : list int → Type
| cnst : int → horner []
| lift (x : int) {xs : list int} : horner xs → horner (x :: xs)
| mult {x : int} {xs : list int} : horner xs → horner (x :: xs) → horner (x :: xs)
 
run_cmd mk_simp_attr `horner_calc

namespace horner

def sizeof' : Π {xs : list int}, horner xs → nat
| [] (cnst _) := 1
| (_ :: _) (lift _ a) := 1 + sizeof' a
| (_ :: _) (mult a₀ a₁) := 1 + sizeof' a₀ + sizeof' a₁

lemma sizeof_pos' : ∀ {xs : list int} (a : horner xs), 0 < sizeof' a
| [] (cnst _) := nat.zero_lt_one
| (_ :: _) (lift _ a) := by { unfold sizeof', apply nat.lt_add_right, exact nat.zero_lt_one }
| (_ :: _) (mult a₀ a₁) := by { unfold sizeof', apply nat.lt_add_right, apply nat.lt_add_right, exact nat.zero_lt_one }

instance (xs : list int) : has_sizeof (horner xs) := ⟨sizeof'⟩

@[horner_calc, reducible]
def zero : Π {xs : list int}, horner xs
| [] := cnst 0
| (_ :: _) := lift _ zero

@[horner_calc, reducible]
def one : Π {xs : list int}, horner xs
| [] := cnst 1
| (_ :: _) := lift _ one

@[horner_calc, reducible]
def add : Π {xs : list int}, horner xs → horner xs → horner xs
| [] (cnst a) (cnst b) := cnst (a + b)
| (x :: xs) (lift _ a) (lift _ b) := lift x (add a b)
| (x :: xs) (lift _ a) (mult b₀ b₁) := mult (add a b₀) b₁
| (x :: xs) (mult a₀ a₁) (lift _ b) := mult (add a₀ b) a₁
| (x :: xs) (mult a₀ a₁) (mult b₀ b₁) := mult (add a₀ b₀) (add a₁ b₁)

@[horner_calc, reducible]
def neg : Π {xs : list int}, horner xs → horner xs
| [] (cnst a) := cnst (-a)
| (x :: xs) (lift _ a) := lift x (neg a)
| (x :: xs) (mult a₀ a₁) := mult (neg a₀) (neg a₁)

@[horner_calc, reducible]
def sub {xs : list int} (a b : horner xs) := add a (neg b)

@[horner_calc, reducible]
def shl {x : int} {xs : list int} : horner (x :: xs) → horner (x :: xs) := mult zero

@[horner_calc, reducible]
def mul : Π {xs : list int}, horner xs → horner xs → horner xs
| [] (cnst a) (cnst b) := cnst (a * b)
| (x :: xs) (lift _ a) (lift _ b) := lift x (mul a b)
| (x :: xs) (lift _ a) (mult b₀ b₁) :=
  have sizeof b₁ < sizeof (mult b₀ b₁),
  begin
  unfold sizeof,
  unfold has_sizeof.sizeof,
  unfold sizeof',
  apply nat.lt_add_of_pos_left,
  apply nat.lt_add_right,
  apply nat.zero_lt_one,
  end,
  mult (mul a b₀) (mul (lift x a) b₁)
| (x :: xs) (mult a₀ a₁) b := 
  have sizeof (lift x a₀) < sizeof (mult a₀ a₁), 
  begin
  unfold sizeof,
  unfold has_sizeof.sizeof,
  unfold sizeof',
  apply nat.lt_add_of_pos_right,
  apply sizeof_pos',
  end,
  have sizeof a₁ < sizeof (mult a₀ a₁),
  begin
  unfold sizeof,
  unfold has_sizeof.sizeof,
  unfold sizeof',
  apply nat.lt_add_of_pos_left,
  apply nat.lt_add_right,
  apply nat.zero_lt_one,
  end,
  add (mul (lift x a₀) b) (shl $ mul a₁ b)

@[horner_calc, reducible]
def is_zero : Π {xs : list int}, horner xs → Prop
| [] (cnst a) := a = 0
| (_ :: _) (lift _ a) := is_zero a
| (_ :: _) (mult a₀ a₁) := is_zero a₀ ∧ is_zero a₁

@[horner_calc, reducible]
def equiv {xs : list int} (a b : horner xs) : Prop := is_zero (sub a b)

instance is_zero.decidable : Π {xs : list int} (a : horner xs), decidable (is_zero a)
| [] (cnst a) := eq.decidable a 0
| (_ :: _) (lift _ a) := is_zero.decidable a
| (_ :: _) (mult a₀ a₁) := @and.decidable _ _ (is_zero.decidable a₀) (is_zero.decidable a₁)

instance equiv.decidable {xs : list int} (a b : horner xs) : decidable (equiv a b) := is_zero.decidable _

def eval : Π {xs : list int}, horner xs → int
| [] (cnst a) := a
| (x :: xs) (lift _ a) := eval a
| (x :: xs) (mult a₀ a₁) := eval a₀ + x * eval a₁

theorem eval_cnst (a : int) : eval (cnst a) = a := rfl

theorem eval_lift (x : int) {xs : list int} (a : horner xs) : eval (lift x a) = eval a := rfl

theorem eval_mult {x : int} {xs : list int} (a₀ : horner xs) (a₁ : horner (x :: xs)) : eval (mult a₀ a₁) = eval a₀ + x * eval a₁ := rfl

theorem eval_zero : ∀ (xs : list int), eval (zero : horner xs) = 0
| [] := rfl
| (_ :: xs) := eval_zero xs

theorem eval_one : ∀ (xs : list int), eval (one : horner xs) = 1
| [] := rfl
| (_ :: xs) := eval_one xs

theorem eval_neg : ∀ {xs : list int} (a : horner xs), eval (neg a) = - eval a
| [] (cnst _) := rfl
| (x :: xs) (lift _ a) := eval_neg a
| (x :: xs) (mult a₀ a₁) :=
  by { unfold neg, unfold eval, rw neg_add, rw neg_mul_eq_mul_neg, congr, exact eval_neg a₀, exact eval_neg a₁ }

theorem eval_add : ∀ {xs : list int} (a b : horner xs), eval (add a b) = eval a + eval b
| [] (cnst _) (cnst _) := rfl
| (x :: xs) (lift _ a) (lift _ b) := eval_add a b
| (x :: xs) (lift _ a) (mult b₀ b₁) :=
  by { unfold add, unfold eval, rw eval_add a b₀, ac_refl }
| (x :: xs) (mult a₀ a₁) (lift _ b) :=
  by { unfold add, unfold eval, rw eval_add a₀ b, ac_refl }
| (x :: xs) (mult a₀ a₁) (mult b₀ b₁) :=
  by { unfold add, unfold eval, rw eval_add a₀ b₀, rw eval_add a₁ b₁, rw mul_add x, ac_refl }

theorem eval_sub {xs : list int} (a b : horner xs) : eval (sub a b) = eval a - eval b :=
by rw [eval_add, eval_neg, sub_eq_add_neg]

theorem eval_shl (x : int) {xs : list int} (a : horner (x :: xs)) : eval (shl a) = x * eval a :=
by rw [eval_mult, eval_zero, zero_add]

theorem eval_mul : ∀ {xs : list int} (a b : horner xs), eval (mul a b) = eval a * eval b
| [] (cnst _) (cnst _) := rfl
| (x :: xs) (lift _ a) (lift _ b) :=
  begin
  unfold mul,
  unfold eval,
  exact eval_mul a b,
  end
| (_ :: _) (lift x a) (mult b₀ b₁) :=
  have sizeof b₁ < sizeof (mult b₀ b₁),
  begin
  unfold sizeof,
  unfold has_sizeof.sizeof,
  unfold sizeof',
  apply nat.lt_add_of_pos_left,
  apply nat.lt_add_right,
  apply nat.zero_lt_one,
  end,
  begin
  unfold mul,
  unfold eval,
  rw eval_mul a b₀,
  rw eval_mul (lift x a) b₁,
  rw eval_lift x a,
  rw mul_add,
  ac_refl,
  end
| (x :: _) (mult a₀ a₁) b :=
  have sizeof (lift x a₀) < sizeof (mult a₀ a₁), 
  begin
  unfold sizeof,
  unfold has_sizeof.sizeof,
  unfold sizeof',
  apply nat.lt_add_of_pos_right,
  apply sizeof_pos',
  end,
  have sizeof a₁ < sizeof (mult a₀ a₁),
  begin
  unfold sizeof,
  unfold has_sizeof.sizeof,
  unfold sizeof',
  apply nat.lt_add_of_pos_left,
  apply nat.lt_add_right,
  apply nat.zero_lt_one,
  end,
  begin
  unfold mul,
  unfold eval,
  rw eval_add,
  rw eval_shl,
  rw eval_mul (lift x a₀) b,
  rw eval_lift,
  rw eval_mul a₁ b,
  rw add_mul,
  ac_refl,
  end

theorem eval_zero_of_is_zero : Π {xs : list int} {a : horner xs}, is_zero a → eval a = 0
| [] (cnst a) h := h
| (_ :: _) (lift _ a) h := 
  have is_zero a, from h,
  eval_zero_of_is_zero this
| (x :: _) (mult a₀ a₁) h := 
  show eval a₀ + x * eval a₁ = 0,
  by rw [eval_zero_of_is_zero h.left, eval_zero_of_is_zero h.right, zero_add, mul_zero]
  
theorem eval_eq_of_equiv {xs : list int} {a b : horner xs} : equiv a b → eval a = eval b :=
begin
intro h,
have h : eval (sub a b) = 0, 
from eval_zero_of_is_zero h,
rw eval_sub at h,
exact eq_of_sub_eq_zero h,
end

end horner

class int_ring (xs : list int) (a : int) :=
(expr : horner xs)
(eval : expr.eval = a)

namespace int_ring

@[priority 0]
instance cnst (a : int) : int_ring [] a :=
{ expr := horner.cnst a
, eval := rfl
}

instance lift (x : int) (xs : list int) (a : int) [int_ring xs a] : int_ring (x :: xs) a :=
{ expr := horner.lift x (int_ring.expr xs a)
, eval := by rw [horner.eval_lift, int_ring.eval xs a]
}

instance var (x : int) (xs : list int) : int_ring (x :: xs) x :=
{ expr := horner.mult horner.zero horner.one
, eval := by rw [horner.eval_mult, horner.eval_zero, horner.eval_one, zero_add, mul_one]
}

instance add (xs : list int) (a b : int) [int_ring xs a] [int_ring xs b] : int_ring xs (a + b) :=
{ expr := horner.add (int_ring.expr xs a) (int_ring.expr xs b)
, eval := by rw [horner.eval_add, int_ring.eval xs a, int_ring.eval xs b]
}

instance mul (xs : list int) (a b : int) [int_ring xs a] [int_ring xs b] : int_ring xs (a * b) :=
{ expr := horner.mul (int_ring.expr xs a) (int_ring.expr xs b)
, eval := by rw [horner.eval_mul, int_ring.eval xs a, int_ring.eval xs b]
}

instance neg (xs : list int) (a : int) [int_ring xs a] : int_ring xs (-a) :=
{ expr := horner.neg (int_ring.expr xs a)
, eval := by rw [horner.eval_neg, int_ring.eval xs a]
}

instance sub (xs : list int) (a b : int) [int_ring xs a] [int_ring xs b] : int_ring xs (a - b) :=
{ expr := horner.sub (int_ring.expr xs a) (int_ring.expr xs b)
, eval := by rw [horner.eval_sub, int_ring.eval xs a, int_ring.eval xs b]
}

protected theorem eq (xs : list int) {a b : int} [int_ring xs a] [int_ring xs b] : horner.equiv (int_ring.expr xs a) (int_ring.expr xs b) →  a = b :=
begin
intro h,
rw ← int_ring.eval xs a,
rw ← int_ring.eval xs b,
exact horner.eval_eq_of_equiv h,
end

end int_ring

meta def int_refl_default : tactic unit :=
`[unfold int_ring.expr, trace_state, simp only [] with horner_calc, trace_state, repeat { apply and.intro }, all_goals { simp }]

theorem int_refl (xs : list int) {a b : int} [int_ring xs a] [int_ring xs b] (h : horner.equiv (int_ring.expr xs a) (int_ring.expr xs b) . int_refl_default) : a = b :=
begin
rw ← int_ring.eval xs a,
rw ← int_ring.eval xs b,
exact horner.eval_eq_of_equiv h,
end

namespace tactic
open interactive

meta def interactive.int_refl : parse types.texpr → tactic unit :=
λ lst, do {
  `(@eq int %%lhs %%rhs) ← target,
  lhi ← to_expr ``(int_ring %%lst %%lhs) >>= mk_instance,
  rhi ← to_expr ``(int_ring %%lst %%rhs) >>= mk_instance,
  to_expr ``(@int_ring.eq %%lst %%lhs %%rhs %%lhi %%rhi) >>= apply,
  unfold_projs_target,
  `[simp only with horner_calc],
  repeat (do {
    `(and %%l %%r) ← target,
    to_expr ``(and.intro) >>= apply,
    skip
  }),
  all_goals reflexivity  
}

end tactic
