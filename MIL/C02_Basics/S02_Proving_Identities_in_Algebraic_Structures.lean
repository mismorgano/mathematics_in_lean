import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Real.Basic
import MIL.Common

section
variable (R : Type*) [Ring R]

#check (add_assoc : ∀ a b c : R, a + b + c = a + (b + c))
#check (add_comm : ∀ a b : R, a + b = b + a)
#check (zero_add : ∀ a : R, 0 + a = a)
#check (neg_add_cancel : ∀ a : R, -a + a = 0)
#check (mul_assoc : ∀ a b c : R, a * b * c = a * (b * c))
#check (mul_one : ∀ a : R, a * 1 = a)
#check (one_mul : ∀ a : R, 1 * a = a)
#check (mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c)
#check (add_mul : ∀ a b c : R, (a + b) * c = a * c + b * c)

end

section
variable (R : Type*) [CommRing R]
variable (a b c d : R)

example : c * b * a = b * (a * c) := by ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by ring

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by ring

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring

end

namespace MyRing
variable {R : Type*} [Ring R]

theorem add_zero (a : R) : a + 0 = a := by rw [add_comm, zero_add]

theorem add_neg_cancel (a : R) : a + -a = 0 := by rw [add_comm, neg_add_cancel]

#check MyRing.add_zero
#check add_zero

end MyRing

namespace MyRing
variable {R : Type*} [Ring R]

theorem neg_add_cancel_left (a b : R) : -a + (a + b) = b := by
  rw [← add_assoc, neg_add_cancel, zero_add]

-- Prove these: each of them with three rewrites
theorem add_neg_cancel_right (a b : R) : a + b + -b = a := by
  rw [add_assoc, add_neg_cancel, add_zero]

theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by
  rw [← neg_add_cancel_left a b, h, neg_add_cancel_left]
  -- rw [← zero_add b, ← neg_add_cancel a, add_assoc, h, neg_add_cancel_left]

theorem add_right_cancel {a b c : R} (h : a + b = c + b) : a = c := by
  rw [← add_neg_cancel_right a b, h, add_neg_cancel_right]

theorem mul_zero (a : R) : a * 0 = 0 := by
  have h : a * 0 + a * 0 = a * 0 + 0 := by
    rw [← mul_add, add_zero, add_zero]
  rw [add_left_cancel h]

-- replicate the same proof as before
theorem zero_mul (a : R) : 0 * a = 0 := by
  have h: 0 * a + 0 * a = 0 * a + 0 := by
    rw [← add_mul, add_zero, add_zero]
  rw [add_left_cancel h]

-- theorem zero_mul_2 (a : R) : 0 * a = 0 := by
--   rw [mul_comm 0 a, ]
-- we cannot use mul_comm because a ring is not necessarily commutative

theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := by
  -- rw [← neg_add_cancel_left a b, h, add_zero]
  rw [← neg_add_cancel_left a b, h, add_zero]

-- theorem neg_eq_of_add_eq_zero_2 {a b : R} (h : a + b = 0) : -a = b := by
--   rw [add_neg_cancel]
-- I thought that I could write a hypothesis first and start from it,
-- but I necessarily I add to start with the LHS of the Prop.

theorem eq_neg_of_add_eq_zero {a b : R} (h : a + b = 0) : a = -b := by
  rw [← add_neg_cancel_right a b, h, zero_add]

theorem neg_zero : (-0 : R) = 0 := by
  apply neg_eq_of_add_eq_zero -- so here it's not a complete proof is going to apply that result, which is -0 = 0, so to applied it needs to introduce a new goal, (to prove) the hypothesis in this case 0 + 0 = 0
  rw [add_zero] -- which is proved by this line because add_zero says that a + 0 = a, so 0 + 0 = 0
  -- then because the hypothesis is proved the apply tactic applies, that is -0 = 0

theorem neg_neg (a : R) : - -a = a := by
  apply neg_eq_of_add_eq_zero
  rw [neg_add_cancel]

end MyRing

-- Examples.
section
variable {R : Type*} [Ring R]

example (a b : R) : a - b = a + -b :=
  sub_eq_add_neg a b

end

example (a b : ℝ) : a - b = a + -b :=
  rfl

example (a b : ℝ) : a - b = a + -b := by
  rfl

namespace MyRing
variable {R : Type*} [Ring R]

theorem self_sub (a : R) : a - a = 0 := by
  have h: a - a = a + -a :=
    sub_eq_add_neg a a
    -- rw [← zero_add (a - a), add_assoc]
    -- nth_rw 1 [← neg_neg a]
    -- rw [sub_sub]
  rw [h]
  apply add_neg_cancel



theorem one_add_one_eq_two : 1 + 1 = (2 : R) := by
  norm_num

theorem two_mul (a : R) : 2 * a = a + a := by
  rw [← one_add_one_eq_two, add_mul, one_mul]

end MyRing

section
variable (A : Type*) [AddGroup A]

#check (add_assoc : ∀ a b c : A, a + b + c = a + (b + c))
#check (zero_add : ∀ a : A, 0 + a = a)
#check (neg_add_cancel : ∀ a : A, -a + a = 0)

end

section
variable {G : Type*} [Group G]
-- We can note that this are the 'left' axioms for group theory
#check (mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
#check (one_mul : ∀ a : G, 1 * a = a)
#check (inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1)

namespace MyGroup

theorem inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b := by
  rw [← mul_assoc, inv_mul_cancel, one_mul]

-- theorem mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a := by
--   rw [mul_assoc, add_neg_cancel, add_zero]


theorem mul_left_cancel {a b c : G} (h : a * b = a * c) : b = c := by
  rw [← inv_mul_cancel_left a b, h, inv_mul_cancel_left]

-- theorem mul_right_cancel {a b c : G} (h : b * a = c * a) : b = c := by
--   rw [← inv_mul_cancel_left a b, h, inv_mul_cancel_left]

theorem mul_eq_one {a b : G} (h: a * b = a) : b = 1 := by
  rw [← one_mul b, ← inv_mul_cancel a, mul_assoc, h ]

theorem inv_eq_of_mul_eq_one {a b : G} (h : a * b = 1) : a⁻¹ = b := by
  rw [← inv_mul_cancel_left a b ,h, mul_one]
  -- rw [← inv_add_cancel_left a b, h, add_zero]

-- theorem neg_neg (a : R) : - -a = a := by
--   apply neg_eq_of_add_eq_zero
--   rw [neg_add_cancel]

theorem inv_inv (a: G): a⁻¹ ⁻¹ = a := by
  apply inv_eq_of_mul_eq_one
  rw [inv_mul_cancel]

-- So the proof is the same as the proof to show the right axioms
theorem mul_inv_cancel (a : G) : a * a⁻¹ = 1 := by
  nth_rw 1 [← one_mul a]
  rw [← inv_mul_cancel a⁻¹]
  nth_rw 2 [ mul_assoc]
  rw [inv_mul_cancel a]
  rw [mul_assoc]
  rw [one_mul]



  -- nth_rw 1 [← one_mul a]
  -- nth_rw 1 [← inv_mul_cancel a]
  -- nth_rw 2 [mul_assoc]
  -- rw [inv_mul_cancel_left]

  -- rw [← one_mul a, ← mul_assoc, ← inv_mul_cancel a]
  -- rw [ ← mul_assoc]
  -- rw [mul_assoc]
  -- rw [mul_assoc]
  -- apply mul_eq_one (a * a⁻¹)

theorem mul_one (a : G) : a * 1 = a := by
  rw [← inv_mul_cancel a, ← mul_assoc, mul_inv_cancel, one_mul]

-- from the two above we can prove the ones I defined and are totally analogous results to the ones proved for a commutative ring
-- at the beginning of the section
theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
apply inv_eq_of_mul_eq_one
rw [mul_assoc, ← mul_assoc b, mul_inv_cancel b]
rw [one_mul]
rw [mul_inv_cancel]
  -- rw [← one_mul (a * b)⁻¹]

end MyGroup

end
