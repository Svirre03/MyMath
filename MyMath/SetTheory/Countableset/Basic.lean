--Imports
import MyMath.SetTheory.Countableset.def

namespace MyMath.SetTheory.Countableset

section Theorems

variable {α : Type} (A B C : Countableset α)

theorem eqv_rfl : A ∼ A :=
  by
  rw[←eqv_eq_sim]
  rw[eqv]

  exists id

  apply And.intro
  · exact Function.Bijective.id
  · intro k
    rw[id]

theorem eqv_symm (h_eqv : A ∼ B) : B ∼ A :=
  by
  rw[←eqv_eq_sim, eqv]
  rw[←eqv_eq_sim, eqv] at h_eqv
  

end Theorems

end MyMath.SetTheory.Countableset
