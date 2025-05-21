--Imports
import MyMath.Algebra.VectorSpace.VectorSpace

namespace MyMath.Algebra.VectorSpace

--Define MyLinearMaps structure
structure LinearMap (K V W : Type) [Field K] [AbelianGroup V] [AbelianGroup W] [VectorSpace K V] [VectorSpace K W] where
  toFun : V → W
  init_map_add : ∀(x y : V), toFun (x + y) = toFun x + toFun y
  init_map_smul : ∀(r : K)(v : V), toFun (r • v) = r • toFun v


namespace LinearMap

section Theorems

variable {K U V W : Type} [Field K] [AbelianGroup U] [AbelianGroup V] [AbelianGroup W] [VectorSpace K U] [VectorSpace K V] [VectorSpace K W]

--instence CoeFun
instance : CoeFun (LinearMap K V W) (fun _ => V → W) where
  coe := toFun

--Convert init_ theorems
@[simp]
theorem toFun_eq (f : LinearMap K V W) (v : V) : f.toFun v = f v := by rfl

@[simp]
theorem map_add (f : LinearMap K V W) (v w : V) : f (v + w) = f v + f w :=
  by
  rw[init_map_add]

@[simp]
theorem map_smul (f : LinearMap K V W) (r : K) (v : V) : f (r • v) = r • f v :=
  by
  rw[init_map_smul]

--Definitions
def comp (g : LinearMap K V W) (f : LinearMap K U V) : LinearMap K U W :=
  {toFun := g.toFun ∘ f.toFun, init_map_add := by intro v w; simp only [Function.comp, map_add]  , init_map_smul := by intro r v; simp only [Function.comp, map_smul]}

def id (K V: Type) [Field K] [AbelianGroup V] [VectorSpace K V] : LinearMap K V V :=
  {toFun := fun v => v, init_map_add := by intro v w; rfl, init_map_smul := by intro r v; rfl}

infixr:80 "∘ₗ" => comp

end Theorems

end LinearMap

end MyMath.Algebra.VectorSpace
