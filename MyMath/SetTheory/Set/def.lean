

namespace MyMath.SetTheory

--Define sets
def Set (α : Type) := α → Prop

--Create set of a predicate
def setOf {α : Type} (p : α → Prop) : Set α := p

namespace Set

--Membership in set
def Mem (s : Set α) (a : α): Prop := s a

instance : Membership α (Set α) := ⟨Mem⟩

@[simp]
theorem mem_eq {α : Type} (s : Set α) (a : α) :  s a = (a ∈ s) :=
  by
  rfl

end Set

end MyMath.SetTheory
