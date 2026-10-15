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

* `AInfinityTheory.AInfinityCategoryStruct β R Obj`: a graded `R`-linear quiver with higher
  compositions `mₙ`, not yet subject to any relations.
* `AInfinityTheory.AInfinityCategory β R Obj`: an `A∞`-category structure whose higher
  compositions satisfy the Stasheff identities.

## Implementation notes

The ring of scalars `R` is an ordinary class parameter, so an object type may carry several
rings of scalars. It is passed explicitly wherever it cannot be inferred from later arguments:
to the hom spaces `(X →ᵍ[R] Y) i`, `ComposableHomType`, `AInfinityComposition` and `homCongr`.
-/

@[expose] public section

namespace AInfinityTheory

universe u v w w'

section

variable (β : Type v)
variable (R : Type u) [CommRing R]
variable (Obj : Type w)
variable [AddCommGroup β] [GradingType β]

/-- The data of an `A∞`-category: a graded `R`-linear quiver together with, for each `n ≥ 1`,
a higher composition `mₙ` of degree `2 - n`. No relations are imposed. -/
class AInfinityCategoryStruct extends GradedLinearQuiver β R Obj where
  /-- The higher compositions `mₙ`. -/
  m : AInfinityComposition β R Obj

/-- An `A∞`-category: an `A∞`-category structure whose higher compositions satisfy the
Stasheff identities in every arity. -/
class AInfinityCategory extends AInfinityCategoryStruct β R Obj where
  /-- The higher compositions satisfy the Stasheff identities. -/
  stasheff : indexedSatisfiesStasheff m

end

namespace AInfinityCategory

open GradedLinearQuiver

variable {β : Type v} [AddCommGroup β] [GradingType β] {R : Type u} [CommRing R] {Obj : Type w}
  [AInfinityCategory β R Obj]

/-- In an `A∞`-category, the Stasheff sum of any composable string of morphisms vanishes. -/
theorem indexedStasheffSum_eq_zero {n : ℕ} [NeZero n] {obj : Fin (n + 1) → Obj}
    {deg : Fin n → β} (x : ∀ i, ComposableHomType R obj i (deg i)) {d : β}
    (hd : stasheffTargetDeg deg = d) :
    indexedStasheffSum AInfinityCategoryStruct.m x d hd = 0 :=
  stasheff n obj deg x d hd

end AInfinityCategory

end AInfinityTheory
