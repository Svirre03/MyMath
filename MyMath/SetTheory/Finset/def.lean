--imports
import MyMath.SetTheory.Set.Set
import MyMath.SetTheory.Countableset.def
import MyMath.Function.Function

namespace MyMath.SetTheory

--Define Finset α structure
structure Finset (α : Type) where
  card : Nat
  elems : Fin card → α
  inj : Function.Injective elems

namespace Finset

section Definitions

variable {α : Type} (s t : Finset α)

--Membership definition
def Mem (a : α) : Prop :=
  ∃n : Fin s.card, s.elems n = a

def subFinset : Prop :=
  ∃f : Fin s.card → Fin t.card,  Function.Injective f ∧ (∀k : Fin s.card, t.elems (f k) = s.elems k)

def eqv : Prop :=
  ∃f : Fin s.card → Fin t.card, Function.Bijective f ∧ (∀k : Fin s.card, t.elems (f k) = s.elems k)


--instances
instance : Membership α (Finset α) where
  mem := Mem

instance : Coe (Finset α) (Set α) where
  coe s := fun x => x ∈ s

end Definitions


section RewriteTheorems

variable {α : Type} (s t : Finset α)

theorem mem_eq_in (a : α) : Mem s a = (a ∈ s) :=
  by
  rfl


end RewriteTheorems

end MyMath.SetTheory.Finset
