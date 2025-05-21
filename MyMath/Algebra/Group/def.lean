--Imports
import MyMath.Algebra.Monoid.Monoid

namespace MyMath.Algebra

--Define MyGroup class

class Group (α : Type) extends Monoid α where
  neg : α → α
  init_add_neg : ∀a : α, a + (neg a) = 0

namespace Group

--instance of neg
instance [Group α] : Neg α where
  neg := neg

--theorem to use notation `-`
theorem eq_neg [Group α] (a : α) : -a = neg a := by rfl

--Convert init_theorem
@[simp]
theorem add_neg [Group α] (a : α) : a + -a = 0 :=
  by
  rw[eq_neg, init_add_neg]

end Group

end MyMath.Algebra
