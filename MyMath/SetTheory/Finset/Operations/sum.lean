import MyMath.SetTheory.Finset.def

namespace MyMath.SetTheory.Finset

def sum {α : Type} [Zero α] [Add α] (s : Finset α) : α :=
  match s.card with
  |0 => 0
  |Nat.succ n => s.elems ⟨⟩

end MyMath.SetTheory.Finset
