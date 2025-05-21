--Imports
import MyMath.Fin.Cast.def
import MyMath.Function.Function

namespace MyMath.Fin

open Function

section Jections

variable {n m : Nat} (h_m_pos : 0 < m)

theorem cast_of_le (a : Fin n) (h_a_lt : a.val < m) : cast h_pos a = ⟨a.val, h_a_lt⟩ :=
  by
  rw[cast]
  simp[h_a_lt]

theorem cast_of_le_eq (a b : Fin n) (h_a_lt : a.val < m) (h_b_lt : b.val < m) (h_eq : @cast n m h_pos a = @cast n m h_pos b) : a = b :=
  by

  rw[cast_of_le a h_a_lt, cast_of_le b h_b_lt] at h_eq
  have h_val_eq : a.val = b.val :=
    by
    rw[Fin.val_eq_of_eq h_eq]

  apply Fin.eq_of_val_eq
  exact h_val_eq

theorem cast_le (h_le : n ≤ m) : Injective (@cast n m h_m_pos) :=
  by
  intro a a' h_eq
  --rw[cast, cast] at h_eq

  have h_a_lt_m : a < m := Nat.lt_of_lt_of_le a.isLt h_le
  have h_a'_lt_m : a' < m := Nat.lt_of_lt_of_le a'.isLt h_le

  have h_cast_a_eq := @cast_of_le n m h_m_pos a h_a_lt_m
  have h_cast_a'_eq := @cast_of_le n m h_m_pos a' h_a'_lt_m

  rw[h_cast_a_eq, h_cast_a'_eq] at h_eq
  have h_val_eq := Fin.val_eq_of_eq h_eq
  rw[Fin.val_mk h_a_lt_m, Fin.val_mk h_a'_lt_m] at h_val_eq

  apply Fin.eq_of_val_eq
  exact h_val_eq


end Jections


--Theorems for values of casts
section Val

variable {n m : Nat} (h_m_pos : 0 < m)

theorem val_eq_of_cast (a : Fin n) (h_a_lt_m : a < m) : a.val = (@cast n m h_m_pos a).val :=
  by
  rw[cast_of_le a h_a_lt_m]

theorem val_eq_of_val_not_lt (a : Fin (n+1)) (h_a_val_not_lt : ¬a.val < n) : a.val = n :=
  by
  have h_a_val_ge : a.val ≥ n := Nat.not_lt.mp h_a_val_not_lt
  have h_a_val_le : a.val ≤ n := Nat.le_of_lt_succ a.isLt
  exact Nat.le_antisymm h_a_val_le h_a_val_ge

theorem val_lt_of_val_not_eq (a : Fin (n+1)) (h_val_not_eq : ¬a = n) : a.val < n := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ a.isLt) h_val_not_eq

theorem val_ne_of_ne (a b : Fin n) (h_ne : ¬a = b) : ¬a.val = b.val :=
  by
  intro h_vals_eq
  have h_eq : a = b := Fin.eq_of_val_eq h_vals_eq
  contradiction


end Val
