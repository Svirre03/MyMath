--Imports


--Sum over function from Fin n
section Definitions

variable {n : Nat} {α : Type} [Zero α] [Add α]

def Finfoldl_rec (f : (Fin n) → α) (op : α → α → α) (sum_to : Fin n) : α :=
  match sum_to with
  |⟨0, h⟩  => f ⟨0, h⟩
  |⟨a+1, h⟩ => op (f sum_to) (Finfoldl_rec f op ⟨a, (Nat.lt_trans (Nat.lt_succ_self a) h)⟩)

def Finfoldl (f : (Fin n) → α) (op : α → α → α) : α :=
  match n with
  |0 => 0
  |n+1 => Finfoldl_rec f op ⟨n, Nat.lt_succ_self n⟩


--Sum with instance of add
def Finsuml (f : (Fin n) → α) : α :=
  Finfoldl f (. + .)

end Definitions

--Tests

section Tests

--#eval @Finfoldl 100 Nat _ (fun a => a.val+1) Nat.add
--#eval @Finsuml 100 Nat _ _ (fun a => a.val+1)

end Tests
