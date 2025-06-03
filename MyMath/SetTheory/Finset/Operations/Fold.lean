--Imports
import MyMath.SetTheory.Finset.def
import MyMath.Fin.Fin

namespace MyMath.SetTheory.Finset

section Fold

variable {α : Type} [Zero α] [Add α] (s : Finset α)

def foldl (op : α → α → α) : α :=
  Finfoldl s.elems op

def suml : α :=
  Finsuml s.elems

end Fold

section Tests

def myFinset : Finset Nat where
  card := 100
  elems := fun a => a.val
  inj := by
    intro a a' h
    exact Fin.val_inj.mp h

#eval myFinset.elems ⟨99, Nat.lt_succ_self 99⟩

#eval suml myFinset

end Tests

end MyMath.SetTheory.Finset
