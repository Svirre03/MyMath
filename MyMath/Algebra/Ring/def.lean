--Imports
import MyMath.Algebra.Operations.One
import MyMath.Algebra.AbelianGroup.AbelianGroup

namespace MyMath.Algebra

--Define MyRing
class Ring (α : Type) extends AbelianGroup α where
  mul : α → α → α
  one : α
  init_mul_one : ∀a : α, mul a one = a
  init_mul_assoc : ∀a b c : α, mul (mul a b) c = mul a (mul b c)
  init_mul_comm : ∀a b : α, mul a b = mul b a
  init_mul_distrib : ∀a b c : α, mul a (b + c) = (mul a b) + (mul a c)

namespace Ring

--Instance of Mul
instance [Ring α] : Mul α where
  mul := mul

--Instance of One
instance [Ring α] : One α where
  one := one

--Theorems to convert notation
theorem eq_one [self : Ring α] : 1 = self.one := by rfl
theorem eq_mul [Ring α] (a b : α) : a * b = mul a b := by rfl

--Convert init theorems
@[simp] theorem one_eq [self : Ring α] : self.one = 1 := by rfl
@[simp] theorem mul_eq [Ring α] (a b : α) : mul a b = a * b := by rfl

@[simp]
theorem mul_one [Ring α] (a : α) : a * 1 = a :=
  by
  simp only [eq_mul, eq_one, init_mul_one]

@[simp]
theorem mul_assoc [Ring α] (a b c : α) : a * b * c = a * (b * c) :=
  by
  simp only [eq_mul, init_mul_assoc]

@[simp]
theorem mul_comm [Ring α] (a b : α) : a * b = b * a :=
  by
  simp only [eq_mul, init_mul_comm]

@[simp]
theorem mul_distrib [Ring α] (a b c : α) : a * (b + c) = (a * b) + (a * c) :=
  by
  simp only [eq_mul, init_mul_distrib]

end Ring

end MyMath.Algebra
