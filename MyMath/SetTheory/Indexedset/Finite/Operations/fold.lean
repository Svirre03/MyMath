import MyMath.SetTheory.Indexedset.Finite.def

namespace MyMath.SetTheory.Indexedset.Finite.MyMath.SetTheory.Indexedset.Finite.Operations

open MyMath.Function

def dropLast {α : Type} (s : Indexedset α) [Nonempty s.index] (h_isFinite : isFinite s) : Indexedset α :=
  let n : Nat := Classical.choose h_isFinite



def fold {α : Type} [Zero α] (op : α → α → α) (s : Indexedset α) (h_isFinite : isFinite s) : α :=
  let n : Nat := Classical.choose h_isFinite
  match n with
  |0 => 0
  |n+1 => op α (fold )
