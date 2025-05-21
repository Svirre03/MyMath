--import MyMath
/--
def main : IO Unit :=
  IO.println s!"Hello, {hello}!"


open MyMath.SetTheory


def myFunc (a : Fin 5) : Nat := ↑a

theorem mFunc_Inj : MyMath.Function.Injective myFunc :=
  by
  rw[MyMath.Function.Injective]
  intro a a'
  rw[myFunc]
  rw[myFunc]
  exact Fin.eq_of_val_eq


def myNats : Finset Nat where
  card := 5
  elems := myFunc
  inj := mFunc_Inj

example : 2 ∈ myNats :=
  by
  rw[←Finset.mem_eq_in, Finset.Mem]
  exists (2 : Fin 5)

--/

def abs (k : Int) : Int :=
  if k < 0 then
    -k
  else
    k

theorem abs_of_neg_eq_neg {k : Int} (h : k < 0) : abs k = -k :=
  by
  by_cases h2 : k < 0
  · rw[abs]
    simp [h2]
  · contradiction
