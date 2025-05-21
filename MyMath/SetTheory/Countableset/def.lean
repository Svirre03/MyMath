--Imports
import MyMath.SetTheory.Set.Set
import MyMath.SetTheory.Indexedset.Indexedset
import MyMath.Function.Function
import MyMath.Notations

namespace MyMath.SetTheory

--Define countablesets
structure Countableset (α : Type) where
  elems : Nat → α
  inj : Function.Injective elems

namespace Countableset

--Membership
def Mem {α : Type} (s : Countableset α) (a : α) : Prop :=
  ∃n : Nat, s.elems n = a

--Subsets
def Subset {α : Type} (s t : Countableset α) : Prop :=
  ∃f : Nat → Nat, Function.Injective f ∧ (∀k : Nat, s.elems k = t.elems (f k))

--Equivalence
def eqv {α : Type} (s t : Countableset α) : Prop :=
  ∃f : Nat → Nat, Function.Bijective f ∧ (∀k : Nat, s.elems k = t.elems (f k))


--Instances
instance : Membership α (Countableset α) where
  mem := Mem

instance {α : Type} : Coe (Countableset α) (Set α) where
  coe s := fun a => a ∈ s

instance {α : Type} : Eqv (Countableset α) where
  eqv := eqv


--Rewrite theorems
section Rewrite

variable {α : Type}

theorem mem_eq_in (s : Countableset α) (a : α) : Mem s a = (a ∈ s) :=
  by
  rfl

theorem eqv_eq_sim (s t : Countableset α) : eqv s t = (s ∼ t) :=
  by
  rfl

end Rewrite

end MyMath.SetTheory.Countableset
