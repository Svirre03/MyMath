--Imports


namespace MyMath.Nat

theorem not_eq_of_lt (n m : Nat) (h_lt : n < m) : ¬n = m :=
  by

  by_cases h_eq : n = m
  · symm at h_eq
    have h_ge : n ≥ m := Nat.le_of_eq h_eq
    have h_not_lt : ¬ n < m := Nat.not_lt.mpr h_ge
    contradiction

  · exact h_eq

theorem not_lt_of_eq {n m : Nat} (h_eq : n = m) : ¬n < m :=
  by

  symm at h_eq
  have h_le : n ≥ m := Nat.le_of_eq h_eq
  exact Nat.not_lt.mpr h_le

theorem lt_of_lt_of_lt {n m k : Nat} (h_n_m_lt : n < m) (h_m_k_lt : m < k) : n < k := Nat.lt_of_lt_of_le h_n_m_lt (Nat.le_of_lt h_m_k_lt)

end MyMath.Nat
