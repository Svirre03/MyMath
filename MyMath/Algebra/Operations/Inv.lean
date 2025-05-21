
namespace MyMath.Algebra

--Define inv type class
class Inv (α : Type) where
  inv : α → α

notation x "⁻¹" => Inv.inv x


end MyMath.Algebra
