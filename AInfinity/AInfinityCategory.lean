module

public import Mathlib
public import AInfinity.Stasheff

@[expose] public section

open CategoryTheory Finset AInfinityTheory

noncomputable section

namespace AInfinityCategoryTheory

universe u v w
variable {β : Type v} [Grading β]

structure AInfinityPreCategory
    (R : Type u) [CommRing R] (Obj : Type w)
    extends RLinearGQuiver (β := β) R Obj where
  m :
    {n : ℕ} →
    (obj : Fin (n + 1) → Obj) →
    (deg : Fin n → β) →
    MultilinearMap R
      (fun i : Fin n => composableHomType toRLinearGQuiver.Hom obj deg i)
      (operationTargetType toRLinearGQuiver.Hom obj deg)

namespace AInfinityPreCategory

variable {R : Type u} [CommRing R]
variable {Obj : Type w}

structure Chain (X : AInfinityPreCategory (β := β) R Obj) where
  n : ℕ
  obj : Fin (n + 1) → Obj
  deg : Fin n → β

namespace Chain

variable {X : AInfinityPreCategory (β := β) R Obj}

def source (ch : X.Chain) : Obj := ch.obj 0

def target (ch : X.Chain) : Obj := ch.obj (Fin.last ch.n)

abbrev link (ch : X.Chain) (i : Fin ch.n) : ModuleCat R :=
  composableHomType X.Hom ch.obj ch.deg i

abbrev operationTarget (ch : X.Chain) : ModuleCat R :=
  operationTargetType X.Hom ch.obj ch.deg

end Chain

/-- The full Stasheff sum in arity `n`, with Koszul signs. -/
def stasheffSum
    (X : AInfinityPreCategory (β := β) R Obj)
    {n : ℕ}
    (obj : Fin (n + 1) → Obj)
    (deg : Fin n → β)
    (x : ∀ i : Fin n, composableHomType X.Hom obj deg i) :
    X.Hom (obj 0) (obj (Fin.last n)) (stasheffTargetDeg deg) :=
  indexedStasheffSum X.Hom X.m obj deg x

/-- The Stasheff identities as a property of the raw A∞ category data. -/
def satisfiesStasheff
    (X : AInfinityPreCategory (β := β) R Obj) : Prop :=
  indexedSatisfiesStasheff X.Hom X.m

end AInfinityPreCategory

structure AInfinityCategory
    (R : Type u) [CommRing R] (Obj : Type w)
    extends AInfinityPreCategory (β := β) R Obj where
  stasheff :
    AInfinityPreCategory.satisfiesStasheff
      (β := β) toAInfinityPreCategory

namespace AInfinityCategory

variable {R : Type u} [CommRing R]
variable {Obj : Type w}

lemma stasheff_eq_zero
    (X : AInfinityCategory (β := β) R Obj)
    {n : ℕ}
    (obj : Fin (n + 1) → Obj)
    (deg : Fin n → β)
    (x : ∀ i : Fin n, composableHomType X.Hom obj deg i) :
    X.toAInfinityPreCategory.stasheffSum obj deg x = 0 :=
  X.stasheff n obj deg x

end AInfinityCategory

end AInfinityCategoryTheory
