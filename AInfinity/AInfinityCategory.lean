module

public import Mathlib
public import AInfinity.Stasheff

@[expose] public section

open CategoryTheory Finset AInfinityTheory

noncomputable section

namespace AInfinityTheory

universe u v w
variable (β : Type v) [GradingIndex β]

class AInfinityCategoryStruct
    (R : Type u) [CommRing R] (Obj : Type w)
    extends RLinearGQuiver (β := β) R Obj where
  m :
    {n : ℕ} → [NeZero n] →
    (obj : Fin (n + 1) → Obj) →
    (deg : Fin n → β) →
    MultilinearMap R
      (fun i : Fin n => ComposableHomType (GHom β R) obj deg i)
      (operationTargetType (GHom β R) obj deg)

namespace AInfinityCategoryStruct

variable (R : Type u) [CommRing R]
variable (Obj : Type w)

/-- The full Stasheff sum in arity n, with Koszul signs. -/
def stasheffSum
    [AInfinityCategoryStruct β R Obj]
    {n : ℕ}
    (obj : Fin (n + 1) → Obj)
    (deg : Fin n → β)
    (x : ∀ i : Fin n, ComposableHomType (GHom β R) obj deg i) :
    (GHom β R) (obj 0) (obj (Fin.last n)) (stasheffTargetDeg deg) :=
  indexedStasheffSum (GHom β R) m obj deg x

/-- The Stasheff identities as a property of the raw A∞ category data. -/
def SatisfiesStasheff
    [AInfinityCategoryStruct (β := β) R Obj] : Prop :=
  indexedSatisfiesStasheff β R (Obj := Obj) (GHom β R) m

end AInfinityCategoryStruct

class AInfinityCategory
    (R : Type u) [CommRing R] (Obj : Type w)
    extends AInfinityCategoryStruct (β := β) R Obj where
  satisfiesStasheff :
    AInfinityCategoryStruct.SatisfiesStasheff (β := β) R Obj

namespace AInfinityCategory

variable (R : Type u) [CommRing R]
variable (Obj : Type w)

end AInfinityCategory

end AInfinityTheory
