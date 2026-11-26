/-
Copyright (c) 2026 Zhan Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhan Shi, Marco David
-/
module

public import AInfinity.AInfinityCategoryStruct

/-! # Composable multilinear maps

Fix a map on objects `obj : Obj → Obj'` between graded `R`-linear quivers and a homomorphism of
gradings `degMap : β →+ᵍ β'`. A composable multilinear map Φ over `obj` and `degMap` consists of,
for each n ≥ 1 and each composable string of objects X₀, …, Xₙ, a graded multilinear map
$$\Phi_n : \operatorname{Hom}(X_0, X_1) \otimes \dots \otimes \operatorname{Hom}(X_{n-1}, X_n)
  \to \operatorname{Hom}(\operatorname{obj} X_0, \operatorname{obj} X_n)$$
of degree (s - n) · 1, for a fixed integer `s`. No relations are imposed.

In reduced degrees ‖a‖ = |a| - 1, the component Φₙ has degree s - 1 for every n: a composable
multilinear map is the family of Taylor coefficients of a map of degree s - 1 between bar
constructions, along the map `obj` on objects. The structure maps of A∞-theory are of this form:

* the components φₙ of an A∞-functor `F`, of degree 1 - n, are a composable multilinear map
  with `s = 1` over `F.obj` and `F.degMap`
  (`AInfinityTheory.AInfinityFunctorData.toComposableMultilinearMap`);
* the higher compositions mₙ of an A∞-category, of degree 2 - n, are a composable multilinear
  map with `s = 2` over the identity
  (`AInfinityTheory.AInfinityCategoryStruct.toComposableMultilinearMap`);
* for an A∞-functor `F` to an A∞-category with operations m', both sides m' ∘ F and F ∘ m of
  the A∞-functor equation are composable multilinear maps with `s = 2` over `F.obj` and
  `F.degMap`.

The last example is the reason why the maps `obj` and `degMap` are parameters of the type, and not
fields: composable multilinear maps of different degrees `s` over the same `obj` and `degMap` can
be fed to the same outer map, see `AInfinityTheory.ComposableMultilinearMap.compMarked` in
`AInfinity.FunctorComposition.Defs`.

## Main definitions

* `AInfinityTheory.ComposableMultilinearMap R obj degMap s`: a composable multilinear map.
* `AInfinityTheory.ComposableMultilinearMap.id`: the identity, with `s = 1`: its unary component
  is the identity and its other components vanish.
* `AInfinityTheory.AInfinityCategoryStruct.toComposableMultilinearMap`: the operations mₙ of an
  A∞-category structure, as a composable multilinear map with `s = 2`.

## Main results

* `AInfinityTheory.ComposableMultilinearMap.total_map_congr`: congruence for the components of a
  composable multilinear map in the type of all morphisms. Only the arities and the inputs are
  compared.

## Implementation notes

The degree of Φₙ is written `(s - n : ℤ) • degOne`, so that for `s = 2` it is syntactically the
degree `(2 - n : ℤ) • degOne` of an operation. The degree of Φₙ(a₁, …, aₙ) is
`AInfinityTheory.targetDeg s deg`.

The inputs of Φₙ are graded by `β` and its output by `β'`, so the output family is read through
`degMap`. All degree arithmetic happens in `β`.

Composites of maps on objects are written `fun X ↦ g (f X)` and the identity `fun X ↦ X`, so that
they reduce when applied. The laws `GradingHom.comp_id`, `GradingHom.id_comp` and
`GradingHom.comp_assoc` hold by `rfl`, so composable multilinear maps over both sides of these
laws have the same type.
-/

@[expose] public section

noncomputable section

namespace AInfinityTheory

open GradedLinearQuiver

variable {n : ℕ}

/-- A composable multilinear map Φ over a map on objects `obj` and a homomorphism of gradings
`degMap`: for each n ≥ 1 and each composable string of objects X₀, …, Xₙ, a multilinear map
Φₙ : Hom(X₀, X₁) ⊗ ⋯ ⊗ Hom(Xₙ₋₁, Xₙ) → Hom(obj X₀, obj Xₙ) of degree (s - n) · 1. In reduced
degrees, every Φₙ has degree s - 1. The components of A∞-functors are the case `s = 1` and the
operations of A∞-categories are the case `s = 2`. No relations are imposed. -/
structure ComposableMultilinearMap (R : Type*) [Semiring R] {β β' : Type*} [AddCommGroup β]
    [Grading β] [AddCommGroup β'] [Grading β'] {Obj Obj' : Type*} [GradedLinearQuiver β R Obj]
    [GradedLinearQuiver β' R Obj'] (obj : Obj → Obj') (degMap : β →+ᵍ β') (s : ℤ) where
  /-- The components Φₙ, of degree (s - n) · 1, landing in the hom spaces of the target in the
  translated degrees. -/
  map {n : ℕ} [NeZero n] (X : Fin (n + 1) → Obj) :
    GradedMultilinearMap R (ComposableHom β R X)
      (fun b : β ↦ (obj (X 0) →ᵍ[R] obj (X (Fin.last n))) (degMap b))
      ((s - n : ℤ) • degOne)

namespace ComposableMultilinearMap

variable {β β' : Type*} [AddCommGroup β] [Grading β] [AddCommGroup β'] [Grading β']
  {R : Type*} [Semiring R] {Obj Obj' : Type*} [GradedLinearQuiver β R Obj]
  [GradedLinearQuiver β' R Obj'] {obj : Obj → Obj'} {degMap : β →+ᵍ β'} {s : ℤ}

/-- Two composable multilinear maps are equal if their components agree on all composable
strings of inputs. -/
@[ext]
lemma ext {Φ Ψ : ComposableMultilinearMap R obj degMap s}
    (h : ∀ {n : ℕ} [NeZero n] {X : Fin (n + 1) → Obj} {deg : Fin n → β}
      (a : ∀ i, ComposableHom β R X i (deg i)) {j : β} (hj : targetDeg s deg = j),
      (Φ.map X).v deg j hj a = (Ψ.map X).v deg j hj a) : Φ = Ψ := by
  obtain ⟨Φ⟩ := Φ
  obtain ⟨Ψ⟩ := Ψ
  congr 1
  funext n _ X
  exact GradedMultilinearMap.ext fun deg j hj ↦ MultilinearMap.ext fun a ↦ h a hj

/-- Congruence for the components of a composable multilinear map in the type of all morphisms:
only the arities and the inputs are compared. The object strings and the degrees are determined
by the inputs. -/
theorem total_map_congr (Φ : ComposableMultilinearMap R obj degMap s) {k k' : ℕ} [NeZero k]
    [NeZero k'] (e : k = k') {Y : Fin (k + 1) → Obj} {Y' : Fin (k' + 1) → Obj} {δ : Fin k → β}
    {δ' : Fin k' → β} {j j' : β} (hj : targetDeg s δ = j) (hj' : targetDeg s δ' = j')
    {b : ∀ i, ComposableHom β R Y i (δ i)} {b' : ∀ i, ComposableHom β R Y' i (δ' i)}
    (hb : ∀ i, Total.of (b i) = Total.of (b' (i.cast e))) :
    Total.of ((Φ.map Y).v δ j hj b) = Total.of ((Φ.map Y').v δ' j' hj' b') := by
  subst hj hj'
  exact Total.congr_composable (fun k _ Y δ b ↦ Total.of ((Φ.map Y).v δ _ rfl b)) e hb

/-! ### The identity -/

section Identity

variable (X : Fin (1 + 1) → Obj)

lemma idMap_deg {deg : Fin 1 → β} {j : β} (hj : targetDeg 1 deg = j) :
    deg 0 = GradingHom.id β j := by
  simpa [targetDeg] using hj

/-- The unary component of the identity composable multilinear map: the identity of
Hom(X₀, X₁). -/
def idMap : GradedMultilinearMap R (ComposableHom β R X)
    (fun b : β ↦ (X 0 →ᵍ[R] X (Fin.last 1)) (GradingHom.id β b))
    (((1 : ℤ) - ((1 : ℕ) : ℤ)) • degOne) :=
  .mk fun deg j hj ↦
    { toFun := fun a ↦ homCongr R rfl rfl (idMap_deg hj) (a 0)
      map_update_add' := fun m i x y ↦ by
        obtain rfl : i = 0 := Subsingleton.elim _ _
        simp only [Function.update_self]
        exact map_add _ x y
      map_update_smul' := fun m i c x ↦ by
        obtain rfl : i = 0 := Subsingleton.elim _ _
        simp only [Function.update_self]
        exact map_smul _ c x }

lemma idMap_v_apply {deg : Fin 1 → β} (a : ∀ i, ComposableHom β R X i (deg i)) {j : β}
    (hj : targetDeg 1 deg = j) :
    (idMap X).v deg j hj a = homCongr R rfl rfl (idMap_deg hj) (a 0) :=
  rfl

/-- The component of arity n of the identity composable multilinear map: the identity for
n = 1, and zero otherwise. -/
def idComponent {n : ℕ} [NeZero n] (X : Fin (n + 1) → Obj) :
    GradedMultilinearMap R (ComposableHom β R X)
      (fun b : β ↦ (X 0 →ᵍ[R] X (Fin.last n)) (GradingHom.id β b)) (((1 : ℤ) - n) • degOne) :=
  match n with
  | 1 => idMap X
  | _ => 0

variable (β R Obj) in
/-- The identity composable multilinear map, with `s = 1`: its unary component is the identity
and its components of higher arity vanish. These are the components of the identity
A∞-functor. -/
protected def id : ComposableMultilinearMap R (fun X : Obj ↦ X) (GradingHom.id β) 1 where
  map X := idComponent X

@[simp]
lemma id_map_one : (ComposableMultilinearMap.id β R Obj).map X = idMap X :=
  rfl

lemma id_map_eq_zero [NeZero n] (hn : n ≠ 1) (X : Fin (n + 1) → Obj) :
    (ComposableMultilinearMap.id β R Obj).map X = 0 := by
  change idComponent X = 0
  unfold idComponent
  split
  · exact absurd rfl hn
  · rfl

end Identity

end ComposableMultilinearMap

/-! ### The operations of an A∞-category structure -/

namespace AInfinityCategoryStruct

variable {β : Type*} [AddCommGroup β] [Grading β] {R : Type*} [Semiring R] {Obj : Type*}
  [AInfinityCategoryStruct β R Obj]

variable (β R Obj) in
/-- The higher compositions mₙ of an A∞-category structure, of degree 2 - n, as a composable
multilinear map with `s = 2` over the identity. -/
def toComposableMultilinearMap :
    ComposableMultilinearMap R (fun X : Obj ↦ X) (GradingHom.id β) 2 where
  map X := m X

@[simp]
lemma toComposableMultilinearMap_map {n : ℕ} [NeZero n] (X : Fin (n + 1) → Obj) :
    (toComposableMultilinearMap β R Obj).map X = m X :=
  rfl

end AInfinityCategoryStruct

end AInfinityTheory
