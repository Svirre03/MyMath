import MyMath.Function.Properties.def
import MyMath.Fin.Basic

namespace MyMath.Fin

open MyMath.Function

--Define restriction of f: Fin n → α to f|: Fin m → α w.
-- f| a = f ↑a

def FinRestrict {α : Type} {n m : Nat} (h_le : m ≤ n) (f : Fin n → α) : Fin m → α :=
  fun a => f (finToFin (Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt (Nat.zero_le a.val) a.isLt) h_le) a)

--Theorems
section Theorems

variable {α : Type} {n m : Nat}

theorem fun_restr_self (f : Fin n → α) : @FinRestrict α n n (Nat.le_of_eq (h : n = n)) f = f :=
  by
  ext a
  rw [FinRestrict]
  rw [finToFin]
  simp [a.isLt]

theorem fun_restr_eq (h_le : m ≤ n) (f : Fin n → α) (b : Fin m) (a : Fin n) (h_eq : a.val = b.val) : FinRestrict h_le f b = f a :=
  by
  rw[FinRestrict]
  rw[finToFin]

  have hb : b.val < n := Nat.lt_of_lt_of_le b.isLt h_le
  have h_m_pos : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le b) b.isLt
  have h_n_pos : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le a) a.isLt

  simp [hb]
  symm at h_eq
  rw[← finToFin_of_le h_n_pos]
  rw[eq_of_val h_n_pos b a h_eq]


theorem fin_restr_of_inj (h_le : m ≤ n) (f : Fin n → α) (h_inj : Injective f) : (Injective (FinRestrict h_le f)) :=
  by
  intros a a' h_eq
  rw[FinRestrict, FinRestrict] at h_eq

  rw[finToFin, finToFin] at h_eq

  have h_a_le : a.val < n := Nat.lt_of_lt_of_le a.isLt h_le
  have h_a'_le : a'.val < n := Nat.lt_of_lt_of_le a'.isLt h_le

  simp [h_a_le, h_a'_le] at h_eq




end Theorems

--Tests
def MyFinFunc : Fin 2 → Nat :=
  fun a => if a.val = 0 then 4 else if a.val = 1 then 2 else 0

def MyRestrictedFinFunc : Fin 3 → Nat := FinRestrict Nat.zero_lt_two MyFinFunc

end MyMath.Fin
