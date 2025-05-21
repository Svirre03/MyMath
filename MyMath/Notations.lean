--Imports

--Define equivalence class using ∼ notation

class Eqv (α : Type u) where
  eqv : α → α → Prop

infixr:50 " ∼ " => Eqv.eqv

class Subs (α : Type u) where
  subs : α → α → Prop

infixr:50 " ⊆ " => Subs.subs

--Define function inverses
class FunInv (α : Type) (β : Type) where
  inv : (α → β) → (β → α)

notation f"⁻¹" => FunInv.inv f
