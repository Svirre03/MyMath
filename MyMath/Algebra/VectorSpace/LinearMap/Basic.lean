--Imports
import MyMath.Algebra.VectorSpace.LinearMap.def

namespace MyMath.Algebra.VectorSpace

namespace LinearMap

section Theorems

variable {K V W : Type} [Field K] [AbelianGroup V] [AbelianGroup W] [VectorSpace K V] [VectorSpace K W]

--new Theorems for linear maps
@[simp]
theorem map_zero (f : LinearMap K V W) : f 0 = 0 :=
  by
  rw[←VectorSpace.smul_zero (0 : K), map_smul, VectorSpace.zero_smul]

@[simp]
theorem id_eq_self (v : V) : (id K V) v = v := by rfl

@[simp]
theorem comp_id (f : LinearMap K V W) : (f ∘ₗ (id K V)) = f := by rfl

@[simp]
theorem id_comp (f : LinearMap K V W) : ((id K W) ∘ₗ f) = f := by rfl

end Theorems

end LinearMap

end MyMath.Algebra.VectorSpace
