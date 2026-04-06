import Mathlib

open ChainComplex CategoryTheory DirectSum GradedMonoid GradedObject


namespace AInfinityCategoryTheory

abbrev Parity := ZMod 2

class Grading (β : Type u) extends AddCommGroup β where
  ofInt: ℤ →+ β
  sign : β →+ Parity
  sign_ofInt: ∀ n : ℤ, sign (ofInt n) = (n : Parity)


def shift_ofInt {β} [Grading β] (n : ℤ) : β :=
  Grading.ofInt n

end AInfinityCategoryTheory
