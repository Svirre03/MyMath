--Imports
import MyMath.Algebra.Group.Group

namespace MyMath.Algebra

--Define
class AbelianGroup (α : Type) extends Group α where
  init_add_comm : ∀a b : α, a + b = b + a

namespace AbelianGroup

--Convert init to theorems
@[simp]
theorem add_comm [AbelianGroup α] (a b : α) : a + b = b + a :=
  by
  rw[init_add_comm a b]

end AbelianGroup

end MyMath.Algebra
