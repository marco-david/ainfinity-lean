/-
Copyright (c) 2026 Annie Yao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Annie Yao, Marco David, Zhan Shi
-/
module

public import AInfinity.Stasheff

/-! # A∞-categories

An `A∞`-category is a graded `R`-linear quiver together with higher compositions
`mₙ : Hom(X₀, X₁) ⊗ ⋯ ⊗ Hom(Xₙ₋₁, Xₙ) → Hom(X₀, Xₙ)` of degree `2 - n`, one for each `n ≥ 1`,
satisfying the Stasheff identities.

## Main definitions

* `AInfinityTheory.GradedLinearQuiver β R Obj`: a quiver on `Obj` whose morphisms of each
  degree `i : β` form an `R`-module.
* `AInfinityTheory.AInfinityCategoryStruct β R Obj`: a graded `R`-linear quiver with higher
  compositions `mₙ`, not yet subject to any relations.
* `AInfinityTheory.AInfinityCategory β R Obj`: an `A∞`-category structure whose higher
  compositions satisfy the Stasheff identities.

## Implementation notes

Neither the hom spaces `GradedLinearQuiver.Hom X Y i` nor the values of the operations
`AInfinityCategoryStruct.m` mention the ring `R` in their types. To let instance search find
these structures without `R` being supplied by hand, `R` is an `outParam` of all three classes.
As a consequence, an object type carries a single ring of scalars.
-/

@[expose] public section

namespace AInfinityTheory

universe u v w w'

section

variable (β : Type v)
variable (R : outParam (Type u)) [CommRing R]
variable (Obj : Type w)

/-- A graded `R`-linear quiver: for objects `X Y` and a degree `i`, the morphisms of degree `i`
from `X` to `Y` form an `R`-module `Hom X Y i`. -/
class GradedLinearQuiver where
  /-- The morphisms of degree `i` from `X` to `Y`. -/
  Hom : Obj → Obj → β → Type w'
  /-- Each graded piece of a hom space is an abelian group. -/
  homGroup : ∀ X Y i, AddCommGroup (Hom X Y i) := by infer_instance
  /-- Each graded piece of a hom space is an `R`-module. -/
  homModule : ∀ X Y i, Module R (Hom X Y i) := by infer_instance

attribute [instance_reducible, instance] GradedLinearQuiver.homGroup
  GradedLinearQuiver.homModule

variable [AddCommGroup β] [GradingType β]

/-- The data of an `A∞`-category: a graded `R`-linear quiver together with, for each `n ≥ 1`,
a higher composition `mₙ` of degree `2 - n`. No relations are imposed. -/
class AInfinityCategoryStruct extends GradedLinearQuiver β R Obj where
  /-- The higher compositions `mₙ`. -/
  m : AInfinityComposition R Hom

/-- An `A∞`-category: an `A∞`-category structure whose higher compositions satisfy the
Stasheff identities in every arity. -/
class AInfinityCategory extends AInfinityCategoryStruct β R Obj where
  /-- The higher compositions satisfy the Stasheff identities. -/
  stasheff : indexedSatisfiesStasheff m

end

namespace AInfinityCategory

variable {β : Type v} [AddCommGroup β] [GradingType β] {R : Type u} [CommRing R] {Obj : Type w}
  [AInfinityCategory β R Obj]

/-- In an `A∞`-category, the Stasheff sum of any composable string of morphisms vanishes. -/
theorem indexedStasheffSum_eq_zero {n : ℕ} [NeZero n] {obj : Fin (n + 1) → Obj}
    {deg : Fin n → β} (x : ∀ i, ComposableHomType GradedLinearQuiver.Hom obj i (deg i)) {d : β}
    (hd : stasheffTargetDeg deg = d) :
    indexedStasheffSum AInfinityCategoryStruct.m x d hd = 0 :=
  stasheff n obj deg x d hd

end AInfinityCategory

end AInfinityTheory
