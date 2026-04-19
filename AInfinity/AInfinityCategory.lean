module

public import Mathlib
public import AInfinity.Stasheff

@[expose] public section

open CategoryTheory Finset AInfinityTheory

noncomputable section

namespace AInfinityCategoryTheory

universe u v w
variable (β : Type v) [Grading β]

--TODO: change n to N and then take in extra parameter  → [NeZero n]
class AInfinityCategoryData
    (R : Type u) [CommRing R] (Obj : Type w)
    extends RLinearGQuiver (β := β) R Obj where
  m :
    {n : ℕ} → [NeZero n] →
    (obj : Fin ((n : ℕ) + 1) → Obj) →
    (deg : Fin (n : ℕ) → β) →
    MultilinearMap R
      (fun i : Fin (n : ℕ) => composableHomType (GHom β R) obj deg i)
      (operationTargetType (GHom β R) obj deg)

namespace AInfinityCategoryData

variable (R : Type u) [CommRing R]
variable (Obj : Type w)

/-- The full Stasheff sum in arity n, with Koszul signs. -/
def stasheffSum
    (X : AInfinityCategoryData β R Obj)
    {n : ℕ}
    (obj : Fin (n + 1) → Obj)
    (deg : Fin n → β)
    (x : ∀ i : Fin n, composableHomType X.Hom obj deg i) :
    X.Hom (obj 0) (obj (Fin.last n)) (stasheffTargetDeg deg) :=
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
      β R Obj toAInfinityCategoryData

namespace AInfinityCategory

variable (R : Type u) [CommRing R]
variable (Obj : Type w)

end AInfinityCategory

end AInfinityCategoryTheory
