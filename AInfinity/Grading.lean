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

--TODO make beta explicit
def shift_ofInt {β} [Grading β] (n : ℤ) : β :=
  Grading.ofInt n

variable (β : Type v) [Grading β]

abbrev GradedRModule (R : Type u) [CommRing R] :=
  GradedObject β (ModuleCat.{u} R)

/-- The graded R-module of morphisms between two objects. -/
class RLinearGQuiver (R : Type u) [CommRing R] (Obj : Type w) where
  -- TODO: Rename to GHom' and make protected
  Hom : Obj → Obj → GradedRModule β R

def GHom (R : Type u) [CommRing R] {Obj : Type w} [RLinearGQuiver β R Obj] (X Y : Obj) : GradedRModule β R :=
  RLinearGQuiver.Hom X Y

end AInfinityTheory
