module

public import Mathlib

@[expose] public section

open ChainComplex CategoryTheory DirectSum GradedMonoid GradedObject

namespace AInfinityCategoryTheory

universe u v w

abbrev Parity := ZMod 2

class Grading (β : Type u) extends AddCommGroup β where
  ofInt : ℤ →+ β
  sign : β →+ Parity
  sign_ofInt: ∀ n : ℤ, sign (ofInt n) = (n : Parity)


def shift_ofInt {β} [Grading β] (n : ℤ) : β :=
  Grading.ofInt n

class GQuiver (β : Type u) (obj : Type v) where
  /-- The type of morphisms between a given source and target. -/
  data : obj → obj → GradedObject β (Type w)

end AInfinityCategoryTheory
