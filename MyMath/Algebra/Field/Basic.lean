--Imports
import MyMath.Algebra.Field.def

namespace MyMath.Algebra

namespace Field

--New theorems for fields
@[simp]
theorem inv_mul [Field α] (a : α) (h : a ≠ 0) : a⁻¹ * a = 1 :=
  by
  rw[Ring.mul_comm]
  exact mul_inv a h

@[simp]
theorem mul_right_cancel [Field α] (a b c : α) (hc : c ≠ 0) (h : a * c = b * c) : a = b :=
  by
  rw[← Ring.mul_one a, ← Ring.mul_one b, ← mul_inv c hc, ← Ring.mul_assoc, ← Ring.mul_assoc]
  rw[h]

@[simp]
theorem mul_left_cancel [Field α] (a b c : α) (hc : c ≠ 0) (h : c * a = c * b) : a = b :=
  by
  rw[Ring.mul_comm c a, Ring.mul_comm c b] at h
  exact mul_right_cancel a b c hc h

end Field

end MyMath.Algebra
