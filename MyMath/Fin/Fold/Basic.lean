--Imports
import MyMath.Fin.Fold.def
import MyMath.Fin.Permutations.Permutations
import MyMath.Function.Function
import MyMath.Fin.Basic

namespace MyMath.Fin

open Function
open Permutation



--Theorems
section PermutationInvariance

--Folding over funciton and function composed with a permutation gives the same result
--if the op satisfies
-- 1. commutativity
-- 2. associativity

--Proven with

variable {n : Nat} {α : Type} [Zero α] [Add α]

variable (op : α → α → α) (h_op_comm : ∀a a' : α, op a a' = op a' a)
(h_op_assoc : ∀a b c : α, op (op a b) c = op a (op b c))

variable (σ : Fin n → Fin n) (h_perm : isPermutation σ)

-- theorem Finfoldl_perm_eq (f : Fin n → α) : Finfoldl f op = Finfoldl (f ∘ σ) op :=
--   by

--   match n with
--   |0 => rfl
--   |a+1 =>
--     simp[Finfoldl]
--     match a with
--     |0 =>
--       rw[Finfoldl_rec, Finfoldl_rec]
--       sorry
--     |b+1 =>
--       rw[Finfoldl_rec, Finfoldl_rec]
--       sorry



end PermutationInvariance

section Tests

def my_fin_func : Fin 2 → Nat := Fin.val

def my_perm : Fin 2 → Fin 2
|⟨0, _⟩ => ⟨1, Nat.one_lt_two⟩
|⟨1, _⟩ => ⟨0, Nat.zero_lt_two⟩

theorem my_perm_involution : ∀a : Fin 2, (my_perm ∘ my_perm) a = id a :=
    by
    intro a
    rw [Function.comp]
    match a with
    |⟨0, _⟩ => rw [my_perm, my_perm, id]
    |⟨1, _⟩ => rw [my_perm, my_perm, id]

theorem my_perm_has_inverse : Function.hasInverse my_perm :=
    by
    exists my_perm
    apply And.intro
    · rw [isLeftInverse]
      exact my_perm_involution
    · rw [isRightInverse]
      exact my_perm_involution


theorem suml_my_perm_invariant (a : Fin 2 → Nat) : Finsuml a = Finsuml (a ∘ my_perm) :=
    by

    -- Unfold recursive definition
    rw [Finsuml, Finfoldl, Finfoldl_rec]
    rw [Finfoldl_rec]

    rw [Finsuml, Finfoldl, Finfoldl_rec]
    rw[Finfoldl_rec]

    --Deal with permutations
    rw [Function.comp, Function.comp]

    rw [my_perm, my_perm]

    --Use commutative operator
    rw [Nat.add_comm]

  theorem suml_fin2_invariant (a : Fin 2 → Nat) (σ : Fin 2 → Fin 2) (h_perm : isPermutation σ) : Finsuml a = Finsuml (a ∘ σ) :=
    by

    --Unfold recursive definition
    rw [Finsuml, Finfoldl, Finfoldl_rec]
    rw [Finfoldl_rec]

    rw [Finsuml, Finfoldl, Finfoldl_rec]
    rw[Finfoldl_rec]

    --Depending on φ use commutativity or not

    have h_perm_zero_values := values_fin_two_2 (σ ⟨0, Nat.zero_lt_two⟩)

    cases h_perm_zero_values with
    |inl h =>
      rw [Function.comp, Function.comp, h]
      sorry
    |inr h =>
      rw[Function.comp, Function.comp, h, Nat.add_comm]
      apply Nat.add_right_cancel_iff.mpr

      sorry


#eval my_perm ⟨1, Nat.one_lt_two⟩

end Tests
