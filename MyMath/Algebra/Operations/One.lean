
namespace MyMath.Algebra

--Define One type class
class One (α : Type) where
  one : α

namespace One

  --Instance of 1
  instance [One α] : OfNat α 1 where
    ofNat := one

end One

end MyMath.Algebra
