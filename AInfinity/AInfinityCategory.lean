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

* `AInfinityTheory.AInfinityCategory β R Obj`: an `A∞`-category structure whose higher
  compositions satisfy the Stasheff identities.
-/

@[expose] public section

namespace AInfinityTheory

universe u v w

section

variable (β : Type v)
variable (R : Type u) [CommRing R]
variable (Obj : Type w)
variable [AddCommGroup β] [GradingType β]

/-- An `A∞`-category: an `A∞`-category structure whose higher compositions satisfy the
Stasheff identities in every arity. -/
class AInfinityCategory extends AInfinityCategoryStruct β R Obj where
  /-- The higher compositions satisfy the Stasheff identities: in every arity `n ≥ 1`, the
  Stasheff sum of any composable string of morphisms vanishes. -/
  indexedStasheffSum_eq_zero {n : ℕ} [NeZero n] {X : Fin (n + 1) → Obj} {deg : Fin n → β}
    (x : ∀ i : Fin n, GradedLinearQuiver.ComposableHom β R X i (deg i)) {d : β}
    (hd : stasheffTargetDeg deg = d) :
    indexedStasheffSum x d hd = 0

end

end AInfinityTheory
