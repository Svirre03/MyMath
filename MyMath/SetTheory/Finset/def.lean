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

--Membership definition
def Mem {α : Type} (s : Finset α) (a : α) : Prop :=
  ∃n : Fin s.card, s.elems n = a

def subFinset {α : Type} (s t : Finset α) : Prop :=
  ∃f : Fin s.card → Fin t.card,  Function.Injective f ∧ (∀k : Fin s.card, t.elems (f k) = s.elems k)

def eqv {α : Type} (s t : Finset α) : Prop :=
  ∃f : Fin s.card → Fin t.card, Function.Bijective f ∧ (∀k : Fin s.card, t.elems (f k) = s.elems k)

--instances
instance : Membership α (Finset α) where
  mem := Mem

instance : Coe (Finset α) (Set α) where
  coe s := fun x => x ∈ s

theorem mem_eq_in {α : Type} (s : Finset α) (a : α) : Mem s a = (a ∈ s) :=
  by
  rfl

end MyMath.SetTheory.Finset
