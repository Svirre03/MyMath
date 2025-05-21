--Imports
import MyMath.Algebra.AbelianGroup.def

namespace MyMath.Algebra

namespace AbelianGroup

  --New theorems for MyAbelianGroup
@[simp]
theorem add_left_comm [AbelianGroup α] (a b c : α) : a + b + c = b + a + c := by simp

@[simp]
theorem add_right_comm [AbelianGroup α] (a b c : α) : a + b + c = a + c + b :=
  by
  rw[Monoid.add_assoc, add_comm b c, ← Monoid.add_assoc]

end AbelianGroup

end MyMath.Algebra
