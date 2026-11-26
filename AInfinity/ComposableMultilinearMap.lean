/-
Copyright (c) 2026 Zhan Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhan Shi
-/
module

public import AInfinity.AInfinityCategoryStruct

/-! # Composable multilinear maps

A composable multilinear map Φ from a graded `R`-linear quiver graded by `β` to one graded by `β'`
consists of a map on objects, a homomorphism of gradings `β →+ᵍ β'` and, for each n ≥ 1 and
each composable string of objects X₀, …, Xₙ, a graded multilinear map
$$\Phi_n : \operatorname{Hom}(X_0, X_1) \otimes \dots \otimes \operatorname{Hom}(X_{n-1}, X_n)
  \to \operatorname{Hom}(\Phi X_0, \Phi X_n)$$
of degree (s - n) · 1, for a fixed integer `s`. No relations are imposed.

Both kinds of higher structure maps of A∞-theory are composable multilinear maps:

* the components φₙ of an A∞-functor, of degree 1 - n, are a composable multilinear map with
  `s = 1` (see `AInfinityTheory.AInfinityFunctorData`);
* the higher compositions mₙ of an A∞-category, of degree 2 - n, are a composable multilinear
  map with `s = 2` from the category to itself, acting as the identity on objects and degrees
  (`AInfinityTheory.AInfinityCategoryStruct.toComposableMultilinearMap`).

In reduced degrees ‖a‖ = |a| - 1, the component Φₙ has degree s - 1 for every n: a composable
multilinear map is the family of Taylor coefficients of a map of degree s - 1 between bar
constructions. The integer `s` is the degree an arity-zero component would have; the curvature
m₀ of a curved A∞-category has degree 2. A composable multilinear map Φ can be composed with
A∞-functor data `F` (with `s = 1`) by
$$(\Phi \circ F)_n = \sum_{i_1 + \dots + i_k = n} \Phi_k(F_{i_1}, \dots, F_{i_k}),$$
see `AInfinityTheory.ComposableMultilinearMap.comp`. With Φ the operations of the target, this is
the right-hand side of the A∞-functor equation; with Φ an A∞-functor, it is the composition of
A∞-functors.

## Main definitions

* `AInfinityTheory.ComposableMultilinearMap`: a composable multilinear map.
* `AInfinityTheory.AInfinityCategoryStruct.toComposableMultilinearMap`: the operations mₙ of an
  A∞-category structure, as a composable multilinear map with `s = 2`.

## Main results

* `AInfinityTheory.ComposableMultilinearMap.map_v_congr`: congruence for the components of a
  composable multilinear map along equalities of arities, objects, degrees and inputs.

## Implementation notes

The degree of Φₙ is written `(s - n : ℤ) • degOne`, so that for `s = 2` it is syntactically the
degree `(2 - n : ℤ) • degOne` of an operation. The degree of Φₙ(a₁, …, aₙ) is
`AInfinityTheory.targetDeg deg s`.

As for A∞-functors, the inputs of Φₙ are graded by `β` and its output by `β'`, so the output
family is read through `degMap`. All degree arithmetic happens in `β`.
-/

@[expose] public section

noncomputable section

namespace AInfinityTheory

open GradedLinearQuiver

variable {n : ℕ}

/-! ### Composable multilinear maps -/

/-- A composable multilinear map Φ between graded `R`-linear quivers: a map on objects, a
homomorphism of gradings and, for each n ≥ 1 and each composable string of objects X₀, …, Xₙ, a
multilinear map Φₙ : Hom(X₀, X₁) ⊗ ⋯ ⊗ Hom(Xₙ₋₁, Xₙ) → Hom(Φ X₀, Φ Xₙ) of degree (s - n) · 1.
In reduced degrees, every Φₙ has degree s - 1. The components of A∞-functors are the case
`s = 1` and the operations of A∞-categories are the case `s = 2`. No relations are imposed. -/
structure ComposableMultilinearMap (β β' : Type*) [AddCommGroup β] [Grading β]
    [AddCommGroup β'] [Grading β'] (R : Type*) [Semiring R] (Obj Obj' : Type*)
    [GradedLinearQuiver β R Obj] [GradedLinearQuiver β' R Obj'] (s : ℤ) where
  /-- The action on objects. -/
  obj : Obj → Obj'
  /-- The homomorphism of gradings translating source degrees into target degrees. -/
  degMap : β →+ᵍ β'
  /-- The components Φₙ, of degree (s - n) · 1, landing in the hom spaces of the target in the
  translated degrees. -/
  map {n : ℕ} [NeZero n] (X : Fin (n + 1) → Obj) :
    GradedMultilinearMap R (ComposableHom β R X)
      (fun b : β ↦ (obj (X 0) →ᵍ[R] obj (X (Fin.last n))) (degMap b))
      ((s - n : ℤ) • degOne)

namespace ComposableMultilinearMap

variable {β β' : Type*} [AddCommGroup β] [Grading β] [AddCommGroup β'] [Grading β']
  {R : Type*} [Semiring R] {Obj Obj' : Type*} [GradedLinearQuiver β R Obj]
  [GradedLinearQuiver β' R Obj'] {s : ℤ}

/-- Congruence for the components of a composable multilinear map along an equality of arities,
object strings, degrees and inputs. -/
lemma map_v_congr (Φ : ComposableMultilinearMap β β' R Obj Obj' s) {k k' : ℕ} [NeZero k]
    [NeZero k'] (e : k = k') {Y : Fin (k + 1) → Obj} {Y' : Fin (k' + 1) → Obj}
    (hY : ∀ i, Y i = Y' (i.cast (by rw [e]))) {δ : Fin k → β} {δ' : Fin k' → β}
    (hδ : ∀ i, δ i = δ' (i.cast e)) {j j' : β} (hj : targetDeg s δ = j)
    (hj' : targetDeg s δ' = j') {b : ∀ i, ComposableHom β R Y i (δ i)}
    {b' : ∀ i, ComposableHom β R Y' i (δ' i)}
    (hb : ∀ i, homCongr R (hY i.castSucc) (hY i.succ) (hδ i) (b i) = b' (i.cast e)) :
    homCongr R (congrArg Φ.obj ((hY 0).trans (congrArg Y' (Fin.cast_zero _))))
      (congrArg Φ.obj ((hY _).trans (congrArg Y' Fin.cast_last)))
      (congrArg Φ.degMap (hj.symm.trans ((targetDeg_congr s e hδ).trans hj')))
      ((Φ.map Y).v δ j hj b) = (Φ.map Y').v δ' j' hj' b' := by
  subst e
  obtain rfl : Y = Y' := funext hY
  obtain rfl : δ = δ' := funext hδ
  obtain rfl : b = b' := funext hb
  subst hj hj'
  rfl

/-- Congruence for the components of a composable multilinear map in the type of all morphisms:
only the arities and the inputs are compared. The object strings and the degrees are determined
by the inputs. -/
theorem total_map_congr (Φ : ComposableMultilinearMap β β' R Obj Obj' s) {k k' : ℕ} [NeZero k]
    [NeZero k'] (e : k = k') {Y : Fin (k + 1) → Obj} {Y' : Fin (k' + 1) → Obj} {δ : Fin k → β}
    {δ' : Fin k' → β} {j j' : β} (hj : targetDeg s δ = j) (hj' : targetDeg s δ' = j')
    {b : ∀ i, ComposableHom β R Y i (δ i)} {b' : ∀ i, ComposableHom β R Y' i (δ' i)}
    (hb : ∀ i, Total.of (b i) = Total.of (b' (i.cast e))) :
    Total.of ((Φ.map Y).v δ j hj b) = Total.of ((Φ.map Y').v δ' j' hj' b') := by
  subst hj hj'
  exact Total.congr_composable (fun k _ Y δ b ↦ Total.of ((Φ.map Y).v δ _ rfl b)) e hb

end ComposableMultilinearMap

/-! ### The operations of an A∞-category structure -/

namespace AInfinityCategoryStruct

variable {β : Type*} [AddCommGroup β] [Grading β] {R : Type*} [Semiring R] {Obj : Type*}
  [AInfinityCategoryStruct β R Obj]

variable (β R Obj) in
/-- The higher compositions mₙ of an A∞-category structure, of degree 2 - n, as a composable
multilinear map with `s = 2` from the category to itself, acting as the identity on objects and
degrees. -/
def toComposableMultilinearMap : ComposableMultilinearMap β β R Obj Obj 2 where
  obj := id
  degMap := GradingHom.id β
  map X := m X

@[simp]
lemma toComposableMultilinearMap_obj : (toComposableMultilinearMap β R Obj).obj = id :=
  rfl

@[simp]
lemma toComposableMultilinearMap_degMap :
    (toComposableMultilinearMap β R Obj).degMap = GradingHom.id β :=
  rfl

@[simp]
lemma toComposableMultilinearMap_map {n : ℕ} [NeZero n] (X : Fin (n + 1) → Obj) :
    (toComposableMultilinearMap β R Obj).map X = m X :=
  rfl

end AInfinityCategoryStruct

end AInfinityTheory
