import MyMath.SetTheory.Indexedset.def
import MyMath.SetTheory.Indexedset.Basic
import MyMath.SetTheory.Indexedset.Countable.def

namespace MyMath.SetTheory.Indexedset

open MyMath.Function

def isFinite {α : Type} (s : Indexedset α) :=
  ∃n : Nat, (∃φ : Fin n → s.index, Bijective φ)


noncomputable def card {α : Type} (s : Indexedset α) (h_isFinite : isFinite s) :=
  Classical.choose h_isFinite

noncomputable def eqvSet {α : Type} (s : Indexedset α) (h_isFinite : isFinite s) : Indexedset α where
  index := Fin (Classical.choose h_isFinite)
  elems := s.elems ∘ (Classical.choose (Classical.choose_spec h_isFinite))
  inj := Injective.comp (Classical.choose (Classical.choose_spec h_isFinite)) s.elems (Classical.choose_spec (Classical.choose_spec h_isFinite)).left s.inj
