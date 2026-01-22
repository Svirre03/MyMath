--Imports

namespace MyMath.Fin

section Elements

theorem fin_zero_empty (a : Fin 0) : False :=
  by
  have h_a_val_ge_zero : a.val ≥ 0 := Nat.zero_le a
  have h_a_val_ne_lt_zero : ¬a.val < 0 := Nat.not_lt_of_ge h_a_val_ge_zero
  exact h_a_val_ne_lt_zero a.isLt

theorem unique_fin_one (a : Fin 1) : a.val = 0 :=
  by

  if h : a.val = 0 then exact h else
    have h_a_val_gt_zero : a.val > 0 := Nat.zero_lt_of_ne_zero h
    have h_a_val_ge_one : a.val ≥ 1 := Nat.succ_le_of_lt h_a_val_gt_zero
    have h_a_val_ne_lt_one : ¬a.val < 1 := Nat.not_lt_of_ge h_a_val_ge_one
    have h_false : False := h_a_val_ne_lt_one a.isLt
    contradiction

  theorem uniqie_fin_one_2 (a : Fin 1) : a = ⟨0, Nat.zero_lt_one⟩ :=
    by

    have h_a_val_eq : a.val = 0 := unique_fin_one a
    apply Fin.eq_of_val_eq
    rw [h_a_val_eq]

theorem values_fin_two (a : Fin 2) : a.val = 0 ∨ a.val = 1 :=
  by

  sorry

theorem values_fin_two_2 (a : Fin 2) : a = ⟨0, Nat.zero_lt_two⟩ ∨ a = ⟨1, Nat.one_lt_two⟩ :=
  by

  sorry

end Elements

end MyMath.Fin
