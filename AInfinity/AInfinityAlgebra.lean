module

public import Mathlib
public import AInfinity.AInfinityCategory

@[expose] public section

open CategoryTheory Finset AInfinityTheory AInfinityCategoryTheory

noncomputable section

namespace AInfinityAlgebraTheory

universe u v
variable {β : Type v} [Grading β]
variable {n : ℕ+}

abbrev OneObj : Type := PUnit

structure AInfinityAlgStruct (R : Type u) [CommRing R]
    (A : GradedRModule (β := β) (R := R)) where
  m :
    {n : ℕ+} →
    (deg : Fin (n : ℕ) → β) →
    MultilinearMap R (fun i : Fin (n : ℕ) => A (deg i))
      (A (operationTargetDeg deg))

namespace AInfinityAlgStruct

variable {R : Type u} [CommRing R]
variable {A : GradedRModule (β := β) (R := R)}

/-- View an A∞-algebra as a one-object A∞-precategory. -/
def toPreCategory
    (X : AInfinityAlgStruct (β := β) R A) :
    AInfinityPreCategory (β := β) R OneObj where
  Hom _ _ := A
  m := by
    intro n obj deg
    simpa [composableHomType] using X.m deg

/-- The full Stasheff sum in arity `n`, with Koszul signs. -/
def stasheffSum
    (X : AInfinityAlgStruct (β := β) R A)
    (n : ℕ+)
    (deg : Fin (n : ℕ) → β)
    (x : ∀ i : Fin (n : ℕ), A (deg i)) :
    A (stasheffTargetDeg deg) :=
  X.toPreCategory.stasheffSum (fun _ => (PUnit.unit : OneObj)) deg x

/-- The Stasheff identities as a property of the raw A∞ data. -/
def satisfiesStasheff
    (X : AInfinityAlgStruct (β := β) R A) : Prop :=
  ∀ (n : ℕ+) (deg : Fin (n : ℕ) → β) (x : ∀ i : Fin (n : ℕ), A (deg i)),
    X.stasheffSum n deg x = 0

end AInfinityAlgStruct

/-- An A∞-algebra is raw data together with the Stasheff identities. -/
class AInfinityAlgebra (R : Type u) [CommRing R]
    (A : GradedRModule (β := β) (R := R))
    extends AInfinityAlgStruct (β := β) R A where
  stasheff :
    AInfinityAlgStruct.satisfiesStasheff
      (β := β) toAInfinityAlgStruct

namespace AInfinityAlgebra

variable {R : Type u} [CommRing R]
variable {A : GradedRModule (β := β) (R := R)}

/-- Re-export the Stasheff identity in a convenient form. -/
lemma stasheff_eq_zero
    (X : AInfinityAlgebra (β := β) R A)
    (n : ℕ+)
    (deg : Fin (n : ℕ) → β)
    (x : ∀ i : Fin (n : ℕ), A (deg i)) :
    X.toAInfinityAlgStruct.stasheffSum n deg x = 0 :=
  X.stasheff n deg x

/-- View an A∞-algebra as a one-object A∞-precategory. -/
def toPreCategory
    (X : AInfinityAlgebra (β := β) R A) :
    AInfinityPreCategory (β := β) R OneObj :=
  X.toAInfinityAlgStruct.toPreCategory

end AInfinityAlgebra

end AInfinityAlgebraTheory
