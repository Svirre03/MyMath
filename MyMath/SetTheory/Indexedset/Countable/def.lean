import MyMath.SetTheory.Indexedset.def
import MyMath.SetTheory.Indexedset.Basic

namespace MyMath.SetTheory.Indexedset

open MyMath.Function

def isCountable {α : Type} (s : Indexedset α) :=
  ∃φ : Nat → s.index, (Injective φ)
