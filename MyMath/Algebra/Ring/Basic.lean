--Imports
import MyMath.Algebra.Ring.def

namespace MyMath.Algebra

namespace Ring

--New theorems for rings
@[simp]
theorem one_mul [Ring α] (a : α) : 1 * a = a := by simp

@[simp]
theorem mul_left_comm [Ring α] (a b c : α) : a * b * c = b * a * c := by simp

@[simp]
theorem mul_right_comm [Ring α] (a b c : α) : a * b * c = a * c * b :=
  by
  rw[mul_assoc, mul_comm b c, ← mul_assoc]

@[simp]
theorem mul_zero [Ring α] (a : α) : a * 0 = 0 :=
  by
  have h : a * 0 + a * 0 = a * 0 :=
    by
    rw[← mul_distrib, Monoid.add_zero]
  have h2 : a * 0 + a * 0 + -(a*0) = a * 0 + -(a * 0) :=
    congrArg (· + -(a*0)) h
  simp at h2
  exact h2

--Not simp-tagged for same reason as unique_zero
theorem unique_one [Ring α] (o1 : α) (h : ∀a : α, a * o1 = a) : o1 = 1 :=
  by
  have h1 : 1 * o1 = 1 := h 1
  rw [one_mul] at h1
  exact h1


end Ring

end MyMath.Algebra
