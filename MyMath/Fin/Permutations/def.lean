--Imports
import MyMath.Function.Function

namespace MyMath.Fin.Permutation

def isPermutation {n : Nat} (φ : Fin n → Fin n) : Prop :=
  Function.Bijective φ

end MyMath.Fin.Permutation
