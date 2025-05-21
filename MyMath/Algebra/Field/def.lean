--Imports
import MyMath.Algebra.Operations.Inv
import MyMath.Algebra.Ring.Ring

namespace MyMath.Algebra

--Define MyField class
class Field (α : Type) extends Ring α where
  inv (a : α) :  α
  init_inv_zero : inv 0 = 0
  init_mul_inv (a : α) (_ : a ≠ 0) :  a * (inv a)  = 1

namespace Field

--instance of inv
instance [Field α] : Inv α where
  inv := inv

--theorems to convert notation
theorem eq_inv [Field α] (a : α) : a⁻¹ = inv a := by rfl

--Convert init_ theorems
@[simp] theorem inv_eq [Field α] (a : α) : inv a = a⁻¹ := by rfl

@[simp]
theorem inv_zero [Field α] : (0 : α)⁻¹ = 0 :=
  by
  simp only [eq_inv, init_inv_zero]

@[simp]
theorem mul_inv [Field α] (a : α) (h : a ≠ 0) : a * a⁻¹ = 1 :=
  by
  simp only[eq_inv, init_mul_inv a h]

end Field

end MyMath.Algebra
