--Imports
import MyMath.Algebra.Operations.SMul
import MyMath.Algebra.Field.Field

namespace MyMath.Algebra

--Define MyVectorspace class
class VectorSpace (K V : Type) [Field K] [AbelianGroup V] where
  smul : K → V → V
  init_one_smul : ∀v : V, smul (1 : K) v = v
  init_smul_assoc : ∀(r s : K) (v : V), smul (r * s) v = smul r (smul s v)
  init_smul_add : ∀(r : K) (v w : V), smul r (v + w) = (smul r v) + (smul r w)
  init_add_smul : ∀(r s : K) (v : V), smul (r + s) v = (smul r v) + (smul s v)

namespace VectorSpace

section Theorems

variable {K V : Type} [Field K] [AbelianGroup V] [VectorSpace K V]

--instance of Smul
instance : SMul K V where
  sMul := smul

--theorems to convert notation
theorem eq_smul (r : K) (v : V) : r • v = smul r v := by rfl

--Convert init_ theorems
@[simp]
theorem smul_eq (r : K) (v : V) : smul r v = r • v := by rfl

@[simp]
theorem one_smul (v : V) : (1 : K) • v = v :=
  by
  rw[eq_smul, init_one_smul]

@[simp]
theorem smul_assoc (r s : K) (v : V) : (r * s) • v = r • s • v :=
  by
  simp only [eq_smul, init_smul_assoc]

@[simp]
theorem smul_add (r : K) (v w : V) : r • (v + w) = r • v + r • w :=
  by
  simp only [eq_smul, init_smul_add]

@[simp]
theorem add_smul (r s : K) (v : V) : (r + s) • v = r • v + s • v :=
  by
  simp only [eq_smul, init_add_smul]

end Theorems

end VectorSpace

end MyMath.Algebra
