
namespace MyMath.Algebra

class SMul (α β : Type) where
  sMul : α → β → β

infixr:73 "•" => SMul.sMul

end MyMath.Algebra
