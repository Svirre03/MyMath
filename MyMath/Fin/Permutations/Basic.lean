--Imports
import MyMath.Fin.Permutations.def
import MyMath.Fin.Function.Function
import MyMath.Function.Function

namespace MyMath.Fin.Permutation

open Function

section Variants

variable {n : Nat} (φ : Fin n → Fin n)

theorem isPerm_of_inj (h_inj : Injective φ) : isPermutation φ :=
  by

  have h_surj : Surjective φ := (inj_iff_surj_of_fin n φ).mp h_inj
  have h_bij : Bijective φ := And.intro h_inj h_surj

  rw [isPermutation]

  exact h_bij

end Variants

section NPermutaions

def two_derangement : Fin 2 → Fin 2
|⟨0, _⟩ => ⟨1, Nat.one_lt_two⟩
|⟨1, _⟩ => ⟨0, Nat.zero_lt_two⟩

--Unique 1-permutation
theorem one_perm (σ : Fin 1 → Fin 1) : σ = id :=
  by

  sorry

theorem two_perm (σ : Fin 2 → Fin 2) (h_perm : isPermutation σ) : σ = id ∨ σ = two_derangement :=
  by

  by_cases h_σ_zero : σ ⟨0, Nat.zero_lt_two⟩ = ⟨0, Nat.zero_lt_two⟩
  · have h_σ_one : σ ⟨1, Nat.one_lt_two⟩ = ⟨1, Nat.one_lt_two⟩ := by sorry
    left
    apply funext
    intro a

    sorry

  ·

    sorry

end NPermutaions


end MyMath.Fin.Permutation
