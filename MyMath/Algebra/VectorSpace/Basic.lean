--Imports
import MyMath.Algebra.VectorSpace.def

namespace MyMath.Algebra

namespace VectorSpace

section Theorems

variable {K V : Type} [Field K] [AbelianGroup V] [VectorSpace K V]

--new theorems for MyVectorspace
@[simp]
theorem zero_smul (v : V) : (0 : K) • v = (0 : V) :=
  by
  have h : (0 : K) • v + (0 : K) • v + -((0 : K) • v) = (0 : K) • v + -((0 : K) • v) :=
    by
    rw[← add_smul, Monoid.add_zero]
  rw[Monoid.add_assoc] at h
  rw[Group.add_neg (0 • v)] at h
  rw[Monoid.add_zero] at h
  exact h

@[simp]
theorem smul_zero (r : K) : r • (0 : V) = (0 : V) :=
  by
  have h : r • (0 : V) + r • 0 + -(r • 0) = r • 0 + -(r • 0) :=
    by
    rw[←smul_add, Monoid.add_zero]
  rw[Monoid.add_assoc, Group.add_neg, Monoid.add_zero] at h
  exact h

@[simp]
theorem neg_one_smul_eq_neg (v : V) : (-1 : K) • v = -v :=
  by
  have h : (1 : K) • v + (-1 : K) • v = (0 : V) :=
    by
    rw[← add_smul, Group.add_neg, zero_smul]
  rw[one_smul] at h
  rw[AbelianGroup.add_comm] at h
  apply Group.eq_neg_of_add_eq_zero
  exact h

end Theorems

end VectorSpace

end MyMath.Algebra
