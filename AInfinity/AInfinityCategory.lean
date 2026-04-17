module

public import Mathlib
public import AInfinity.Stasheff

@[expose] public section

open CategoryTheory Finset AInfinityTheory

noncomputable section

namespace AInfinityCategoryTheory

universe u v w
variable {β : Type v} [Grading β]

structure AInfinityCategoryData
    (R : Type u) [CommRing R] (Obj : Type w)
    extends RLinearGQuiver (β := β) R Obj where
  m :
    {n : ℕ+} →
    (obj : Fin ((n : ℕ) + 1) → Obj) →
    (deg : Fin (n : ℕ) → β) →
    MultilinearMap R
      (fun i : Fin (n : ℕ) => composableHomType toRLinearGQuiver.Hom obj deg i)
      (operationTargetType toRLinearGQuiver.Hom obj deg)

namespace AInfinityCategoryData

variable {R : Type u} [CommRing R]
variable {Obj : Type w}

/-- The full Stasheff sum in arity `n`, with Koszul signs. -/
def stasheffSum
    (X : AInfinityCategoryData (β := β) R Obj)
    {n : ℕ+}
    (obj : Fin ((n : ℕ) + 1) → Obj)
    (deg : Fin (n : ℕ) → β)
    (x : ∀ i : Fin (n : ℕ), composableHomType X.Hom obj deg i) :
    X.Hom (obj 0) (obj (Fin.last (n : ℕ))) (stasheffTargetDeg deg) :=
  indexedStasheffSum X.Hom X.m obj deg x

/-- The Stasheff identities as a property of the raw A∞ category data. -/
def satisfiesStasheff
    (X : AInfinityCategoryData (β := β) R Obj) : Prop :=
  indexedSatisfiesStasheff X.Hom X.m

end AInfinityCategoryData

structure AInfinityCategory
    (R : Type u) [CommRing R] (Obj : Type w)
    extends AInfinityCategoryData (β := β) R Obj where
  stasheff :
    AInfinityCategoryData.satisfiesStasheff
      (β := β) toAInfinityCategoryData

namespace AInfinityCategory

variable {R : Type u} [CommRing R]
variable {Obj : Type w}

lemma stasheff_eq_zero
    (X : AInfinityCategory (β := β) R Obj)
    {n : ℕ+}
    (obj : Fin ((n : ℕ) + 1) → Obj)
    (deg : Fin (n : ℕ) → β)
    (x : ∀ i : Fin (n : ℕ), composableHomType X.Hom obj deg i) :
    X.toAInfinityCategoryData.stasheffSum obj deg x = 0 :=
  X.stasheff n obj deg x

end AInfinityCategory

end AInfinityCategoryTheory
