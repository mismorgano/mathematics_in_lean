import MIL.Common
import Mathlib.Data.Real.Basic

namespace C02S04

section
variable (a b c d : ℝ)

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

example : min a b = min b a := by
  apply le_antisymm
  · show min a b ≤ min b a
    apply le_min
    · apply min_le_right
    apply min_le_left
  · show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    apply min_le_left

example : min a b = min b a := by
  have h : ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min
    apply min_le_right
    apply min_le_left
  apply le_antisymm
  apply h
  apply h

example : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left

-- first proof: using quantifier
example : max a b = max b a := by
  have h: ∀ x y : ℝ , max x y <= max y x := by
    intro x y
    apply max_le
    apply le_max_right
    apply le_max_left
  apply le_antisymm
  apply h
  apply h

-- second proof
example : max a b = max b a := by
  apply le_antisymm
  repeat
    apply max_le
    apply le_max_right
    apply le_max_left

-- apparently we have min_assoc which is the assertion
-- So we're gonna use the above and name a theorem for them ir order to use
-- it clearly is about commutativity so we name it that way but with a _ to differentiate with the surely one in the Mathlib
theorem min_comm_ {a b :ℝ } : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left

#check min_eq_iff


theorem min_eq {a : ℝ } : min a a = a := by
  apply le_antisymm
  apply min_le_left
  apply le_min
  apply le_refl
  apply le_refl
-- theorem min_le {a b : ℝ }: a <= c -> b <= c -> min a b <= c := by

--   rw [min_le_min a b min_eq]

#check min_le_min

example : min (min a b) c = min a (min b c) := by
  have h₁ : ∀ x y z : ℝ, min (min x y) z ≤ x := by
    intro x y z
    apply le_trans
    apply min_le_left (min x y)
    apply min_le_left
  have h₂ : ∀ x y z : ℝ, min (min x y) z ≤ y := by
    intro x y z
    apply le_trans
    apply min_le_left (min x y)
    apply min_le_right

  apply le_antisymm
  . show min (min a b) c ≤ min a (min b c)
    apply le_min
    . apply h₁
    . apply le_min
      . apply h₂
      . apply min_le_right
  . show min a (min b c) ≤ min (min a b) c
    apply le_min
    . apply le_min
      . apply min_le_left
      . apply le_trans
        apply min_le_right
        apply min_le_left
    . apply le_trans
      apply min_le_right
      apply min_le_right

-- example : min (min a b) c = min a (min b c) := by
--   apply le_antisymm
--   repeat
--     apply le_min
--     . show min (min a b) c ≤ a
--       -- apply min_le_left a b

--     --   . apply min_le_left
--     --   . apply min_le_left
--     . show min (min a b) c ≤ min b c
--     --   apply

--       -- . apply min_le_left
--       -- apply min_le_left
--       -- . apply


theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  apply le_min
  . apply add_le_add_right
    apply min_le_left
  . apply add_le_add_right
    apply min_le_right

#check add_neg_cancel_right
example : min a b + c = min (a + c) (b + c) := by
  apply le_antisymm
  . apply aux
  -- . apply aux min (a + c) (b + c)  + -c
  -- . rw [← add_zero (min (a + c) (b + c))]
  --   rw [← add_neg_cancel c]
  --   rw [← add_assoc]
  -- the above does the same as the bottom
  . rw [← neg_add_cancel_right (min (a + c) (b + c)) c]
    apply add_le_add_right
    nth_rw 2 [← add_neg_cancel_right a c]
    nth_rw 2 [← add_neg_cancel_right b c]
    apply aux (a + c) (b + c) (-c)

    -- linarith [aux (a + c) (b + c) (-c)]

-- apparently add_neg_cancel_right, linarith and aux are enough
example : min a b + c = min (a + c) (b + c) := by
  apply le_antisymm
  . apply aux
  . nth_rw 2 [← add_neg_cancel_right a c]
    nth_rw 2 [← add_neg_cancel_right b c]
    linarith [aux (a + c) (b + c) (-c)]



#check (abs_add : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)


#check add_sub_cancel_right

-- first proof
example : |a| - |b| ≤ |a - b| :=
  calc
    |a| - |b| = |a - b + b| - |b| := by
      rw [sub_add_cancel]
    _ ≤ |a - b| + |b| - |b| := by
      apply add_le_add_right
      apply abs_add (a - b ) b
    _ = |a - b| := by ring

#check sub_add_cancel
-- second proof
example : |a| - |b| ≤ |a - b| := by
  have h: |a| ≤ |a - b| + |b| := by -- (sub_add_cancel a b) abs_add
    nth_rw 1 [← sub_add_cancel a b]
    apply abs_add (a-b) b
    -- rw [sub_add_cancel a b]
  rw [← sub_add_cancel |a| |b|]
  linarith


-- third proof
example : |a| - |b| ≤ |a - b| := by
  have h := abs_add (a - b) b
  rw [sub_add_cancel a b] at h
  linarith


end

section
variable (w x y z : ℕ)

example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁

example : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left

example : x ∣ x ^ 2 := by
  apply dvd_mul_left

example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  apply dvd_add
  . apply dvd_add
    . apply dvd_mul_of_dvd_right
      apply dvd_mul_right -- why isn't it inconsistent?? why right if x is left in the expression x*z
    . apply dvd_mul_left
  . apply dvd_trans h
    apply dvd_mul_left

end

section
variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)

example : Nat.gcd m n = Nat.gcd n m := by
  apply dvd_antisymm
  repeat
    apply Nat.dvd_gcd
    apply Nat.gcd_dvd_right
    apply Nat.gcd_dvd_left
-- very analogous to prove the commutativity of min a b = min b a
end
