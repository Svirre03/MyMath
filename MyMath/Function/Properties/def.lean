--imports
import MyMath.Notations

namespace MyMath.Function

--define injective, surjecitve, bijective as a proposition
def Injective {α β : Type} (f : α → β) : Prop :=
  ∀a a' : α, f a = f a' → a = a'

def Surjective {α β : Type} (f : α → β) : Prop :=
  ∀b : β, ∃a : α, f a = b

def Bijective {α β : Type} (f : α → β) : Prop :=
  (Injective f ∧ Surjective f)

--Inverses
section Inverses

variable {α β : Type} (f : α → β) (g : β → α)

--Left Inverse
def isLeftInverse : Prop :=
  ∀a : α, g (f a) = a

def hasLeftInverse : Prop :=
  ∃g : β → α, isLeftInverse f g


--Right Inverse
def isRightInverse : Prop :=
  ∀b : β, f (g b) = b

def hasRightInverse : Prop :=
  ∃g : β → α, isRightInverse f g


--Full Inverse
def isInverse : Prop :=
  (isLeftInverse f g) ∧ (isRightInverse f g)

def hasInverse : Prop :=
  ∃g : β → α, (isLeftInverse f g) ∧ (isRightInverse f g)


--Noncomputable inverses of has


noncomputable def LeftInverse (h_left_inv : hasLeftInverse f) : β → α :=
  Classical.choose h_left_inv

noncomputable def RightInverse (h_right_inv : hasRightInverse f) : β → α :=
  Classical.choose h_right_inv

noncomputable def Inverse (h_inv : hasInverse f) : β → α :=
  Classical.choose h_inv

--Define a weak inverse for all functions from non empty types
attribute [local instance] Classical.propDecidable

noncomputable def weakInverse [inst : Nonempty α] : β → α :=
  fun b => if h : ∃a : α, f a = b then Classical.choose h else Classical.choice inst


end Inverses


end MyMath.Function
