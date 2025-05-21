--Imports
import MyMath.SetTheory.Indexedset.Finite.def

namespace MyMath.SetTheory.Indexedset

open MyMath.Function

--Basic theorems for finite indexed sets
section Theorems

variable {α : Type} (s t r : Indexedset α)

--A finite indexed set is eqv to a set from fin n
theorem isFinite_eqv_fin (h_isFinite : isFinite s) : ∃n : Nat, (∃u : Indexedset α, (u.index = Fin n) ∧ (u ∼ s)) :=
  by

  exists Classical.choose h_isFinite
  exists eqvSet s h_isFinite

  apply And.intro
  --Index eq
  · rfl

  --eqv
  · rw[eqvSet]


    sorry

end Theorems
