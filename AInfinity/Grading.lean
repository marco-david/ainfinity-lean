module

public import Mathlib

@[expose] public section

open ChainComplex CategoryTheory DirectSum GradedMonoid GradedObject

namespace AInfinityTheory

universe u v w

/-- A grading index is an additive commutative group with a distinguished unit
element, together with a parity map to `ZMod 2`. The distinguished unit is used
to realize integer degree shifts via the canonical map `ℤ →+ β`. -/
class GradingIndex (β : Type u) extends AddCommGroupWithOne β where
  protected parity : β →+ ZMod 2
  protected parity_one : parity 1 = 1

/-- The parity homomorphism attached to a grading index. -/
def parity {β : Type u} [GradingIndex β] : β →+ ZMod 2 :=
  GradingIndex.parity

/-- The canonical additive homomorphism from `ℤ` into a grading index. -/
def GradingIndex.ofInt {β : Type u} [GradingIndex β] : ℤ →+ β :=
  Int.castAddHom β

/-- The parity of the distinguished unit is odd. -/
@[simp]
theorem parity_one {β : Type u} [GradingIndex β] : parity (1 : β) = 1 :=
  GradingIndex.parity_one

/-- The parity map agrees with integer casts modulo `2`. -/
@[simp]
theorem parity_intCast {β : Type u} [GradingIndex β] (n : ℤ) :
    parity (n : β) = (n : ZMod 2) := by
  rw [← zsmul_one n, map_zsmul, parity_one, zsmul_one]

/-- The canonical degree shift by an integer. Keeping this wrapper makes degree
formulas read naturally throughout the project. -/
def shift_ofInt {β} [GradingIndex β] (n : ℤ) : β :=
  GradingIndex.ofInt n

variable (β : Type v) [GradingIndex β]

abbrev GradedRModule (R : Type u) [CommRing R] :=
  GradedObject β (ModuleCat.{u} R)

/-- The graded R-module of morphisms between two objects. -/
class RLinearGQuiver (R : Type u) [CommRing R] (Obj : Type w) where
  protected GHom' : Obj → Obj → GradedRModule β R

def GHom (R : Type u) [CommRing R] {Obj : Type w} [RLinearGQuiver β R Obj] (X Y : Obj) : GradedRModule β R :=
  RLinearGQuiver.GHom' X Y

end AInfinityTheory
