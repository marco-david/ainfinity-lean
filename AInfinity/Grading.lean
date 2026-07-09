module

public import Mathlib

@[expose] public section

open ChainComplex CategoryTheory DirectSum GradedMonoid GradedObject

namespace AInfinityTheory

universe u v w

abbrev Parity := ZMod 2

class Grading (β : Type u) extends AddCommGroup β where
  ofInt : ℤ →+ β
  sign : β →+ Parity
  sign_ofInt: ∀ n : ℤ, sign (ofInt n) = (n : Parity)


def shift_ofInt {β} [Grading β] (n : ℤ) : β :=
  Grading.ofInt n

/-- The integers form a grading, with `ofInt = id` and sign `n ↦ n mod 2`. -/
instance instGradingInt : Grading ℤ where
  ofInt := AddMonoidHom.id ℤ
  sign := Int.castAddHom (ZMod 2)
  sign_ofInt _ := rfl

/-- For the `Grading ℤ` instance, `shift_ofInt` is the identity. -/
@[simp]
lemma shift_ofInt_int (n : ℤ) : (shift_ofInt (β := ℤ) n) = n := rfl

variable {β : Type v} [Grading β]

abbrev GradedRModule (R : Type u) [CommRing R] :=
  GradedObject β (ModuleCat.{u} R)

/-- The graded `R`-module of morphisms between two objects. -/
class RLinearGQuiver (R : Type u) [CommRing R] (Obj : Type w) where
  Hom : Obj → Obj → GradedRModule (β := β) (R := R)

end AInfinityTheory
