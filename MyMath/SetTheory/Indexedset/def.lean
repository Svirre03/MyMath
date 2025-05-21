--Imports
import MyMath.Function.Function
import MyMath.Notations

namespace MyMath.SetTheory

--Define Indexed Sets
structure Indexedset (α : Type) where
  index : Type
  elems : index → α
  inj : Function.Injective elems


namespace Indexedset


--Basic definitions for indexed sets
section Definitions

variable {α : Type} (s : Indexedset α) (t : Indexedset α)

def Mem (a : α) : Prop :=
  ∃i : s.index, s.elems i = a

def Subset : Prop :=
  ∃φ : s.index → t.index, (Function.Injective φ) ∧ (∀i : s.index, s.elems i = t.elems (φ i))

def eqv : Prop :=
  ∃φ : s.index → t.index, (Function.Bijective φ) ∧ (∀i : s.index, s.elems i = t.elems (φ i))


--instances
instance : Membership α (Indexedset α) where
  mem := Mem

instance : Subs (Indexedset α) where
  subs := Subset

instance : Eqv (Indexedset α) where
  eqv := eqv

end Definitions



--Basic theorems to rewrite notations
section RewriteTheorems

variable {α : Type} (s t : Indexedset α)

theorem mem_eq_in (a : α) : Mem s a = (a ∈ s) :=
  by
  rfl

theorem subset_eq_sub : Subset s t = (s ⊆ t) :=
  by
  rfl

theorem eqv_eq_sim : eqv s t = (s ∼ t) :=
  by
  rfl

end RewriteTheorems



--Simple tests
section Tests

abbrev MyIndSet : Indexedset Nat where
  index := Nat
  elems := id
  inj := Function.Injective.id

#eval MyIndSet.elems 3


end Tests

end MyMath.SetTheory.Indexedset
