--imports
import MyMath.Algebra.Monoid.def

namespace MyMath.Algebra

--Basic theorems for Monoids

namespace Monoid
 --New theorems for monoids

theorem unique_zero [Monoid α] (z1 : α) (h : ∀a : α, a + z1 = a) : z1 = 0 :=
  by
  have h : 0 + z1 = 0 := h 0
  rw[zero_add] at h
  exact h

--Construct new monoids
def function_is_monoid (α β: Type) [Monoid α] [Monoid β]: Monoid (α → β) :=
  {add := fun f g => fun a => (f a) + (g a), zero := fun _ => 0, init_add_zero := by intro f; ext a; simp, init_zero_add := by intro f; ext a; simp, init_add_assoc := by intro f g h; ext a; simp}


end Monoid

end MyMath.Algebra
