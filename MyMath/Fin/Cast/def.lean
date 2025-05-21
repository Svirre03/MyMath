--Imports

namespace MyMath.Fin

def cast {n m : Nat} (h : 0 < m) (a : Fin n) : Fin m :=
  if h2 : a.val < m then
    ⟨a.val, h2⟩
  else
    ⟨0, h⟩
