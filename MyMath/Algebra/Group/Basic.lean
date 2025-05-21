import MyMath.Algebra.Group.def

namespace MyMath.Algebra

namespace Group
--New theorems for MyGroup

--Not in simplifier since it gives max-recursion
theorem eq_neg_of_add_eq_zero [Group α] (a b : α) (h : a + b = 0) : a = -b :=
  by
  have h2 : a + b + -b = 0 + -b := congrArg (· + -b) h
  simp at h2
  exact h2

end Group

end MyMath.Algebra
