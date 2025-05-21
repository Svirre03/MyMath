namespace MyMath.Algebra
--Define Monoid class

class Monoid (α : Type) where
  add : α → α → α
  zero : α
  init_add_zero : ∀a : α, add a zero = a
  init_zero_add : ∀a : α, add zero a = a
  init_add_assoc : ∀a b c : α, add (add a b) c = add a (add b c)

namespace Monoid

  --Create instances for add and zero
  instance [Monoid α] : Add α where
    add := add

  instance [Monoid α] : Zero α where
    zero := zero

  --theorems to convert notation
  theorem eq_zero [self : Monoid α] : 0 = self.zero := by rfl
  theorem eq_add [Monoid α] (a b : α) : a + b = add a b := by rfl

  --Convert init_theorems to use notation
  @[simp]
  theorem zero_eq [self : Monoid α] : self.zero = 0 := by rfl

  @[simp]
  theorem add_eq [Monoid α] (a b : α): add a b = a + b := by rfl

  @[simp]
  theorem add_zero [Monoid α] (a : α) : a + 0 = a :=
    by
    rw[eq_zero, eq_add, init_add_zero]

  @[simp]
  theorem zero_add [Monoid α] (a : α) : 0 + a = a :=
    by
    rw[eq_zero, eq_add, init_zero_add]

  @[simp]
  theorem add_assoc [Monoid α] (a b c : α) : a + b + c = a + (b + c) :=
    by
    rw[eq_add a b, eq_add (add a b) c, eq_add a (b + c), eq_add, init_add_assoc]

end Monoid

end MyMath.Algebra
