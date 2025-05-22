
namespace MyMath.Fin

--Definitions
def finToFinPred {n : Nat} (h : 0 < n) (a : Fin (n+1)) : Fin n :=
  if h2: a < n then
    ⟨a.val, h2⟩
  else
    ⟨0, h⟩

def finToFinPredOpt {n : Nat} (a : Fin (n+1)) : Option (Fin n) :=
  if h : 0 < n then
    some (finToFinPred h a)
  else
    none

def finToFin {n m : Nat} (h : 0 < m) (a : Fin n) : Fin m :=
  if h2 : a.val < m then
    ⟨a.val, h2⟩
  else
    ⟨0, h⟩

def finToFinOpt {n m : Nat} (a : Fin n) : Option (Fin m) :=
  if h : 0 < m then
    some (finToFin h a)
  else
    none

--Theorems
section Theorems

variable {n m k : Nat} (h_pos : 0 < m)

theorem finToFin_self (a : Fin n) : finToFinOpt a = some a :=
  by
  have h_a_pos : 0 ≤ a.val :=
    by
    exact Nat.zero_le a.val

  have h_pos : 0 < n :=
    by
    exact Nat.lt_of_le_of_lt h_a_pos a.isLt

  rw[finToFinOpt]
  simp [h_pos]
  rw[finToFin]
  simp [a.isLt]

theorem finToFin_of_le (a : Fin n) (h : a.val < m) : finToFin h_pos a = ⟨a.val, h⟩ :=
  by
  rw[finToFin]
  simp[h]

theorem val_eq_of_less (a : Fin n) (b : Fin m) (h_less : a.val < m) : finToFinOpt a = some b → a.val = b.val :=
  by
  have h_m_pos :  0 < m := Nat.lt_of_le_of_lt (Nat.zero_le b.val) b.isLt

  rw[finToFinOpt]
  simp [h_m_pos]

  rw[finToFin]
  simp [h_less]
  exact Fin.val_eq_of_eq

theorem eq_of_val_opt (a : Fin n) (b : Fin m) (h_eq : a.val = b.val) : finToFinOpt a = some b :=
  by
  rw[finToFinOpt]

  have h_m_pos : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le b.val) b.isLt

  simp [h_m_pos]

  rw[finToFin]

  have h_a_le_m : a.val < m :=
    by
    rw[h_eq]
    exact b.isLt
  simp [h_a_le_m]
  apply Fin.eq_of_val_eq
  rw[Fin.val_mk]
  exact h_eq

  theorem eq_of_val (a : Fin n) (b : Fin m) (h_eq : a.val = b.val) : finToFin h_pos a = b :=
    by
    rw[finToFin]
    have h_a_le : a.val < m := Nat.lt_of_le_of_lt (Nat.le_of_eq h_eq) b.isLt

    simp [h_a_le]

    apply Fin.eq_of_val_eq
    rw[Fin.val_mk]
    exact h_eq

theorem eq_of_nat_less (h_lt_n : k < n) (h_lt_m : k < m) : finToFinOpt (Fin.mk k h_lt_n) = some (Fin.mk k h_lt_m) :=
  by
  have h_m_pos : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le k) h_lt_m

  rw[finToFinOpt]
  simp [h_m_pos]
  rw[finToFin]
  rw[Fin.val_mk h_lt_m]
  simp [h_lt_m]

theorem eq_of_finToFinOpt_eq (a a' : Fin n) (h_less : n ≤ m) : @finToFinOpt n m a = @finToFinOpt n m a' → a = a' :=
  by
  have h_n_pos : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le a) a.isLt
  have h_m_pos : 0 < m := Nat.lt_of_lt_of_le h_n_pos h_less
  have ha : a.val < m := Nat.lt_of_lt_of_le a.isLt h_less
  have ha' : a'.val < m := Nat.lt_of_lt_of_le a'.isLt h_less

  intro h_eq

  rw[finToFinOpt, finToFinOpt] at h_eq
  simp [h_m_pos] at h_eq
  rw[finToFin, finToFin] at h_eq
  simp [ha, ha'] at h_eq

  exact Fin.eq_of_val_eq h_eq


end Theorems

end MyMath.Fin
