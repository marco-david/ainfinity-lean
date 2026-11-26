/-
Copyright (c) 2026 Annie Yao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Annie Yao, Marco David, Zhan Shi
-/
module

public import Mathlib.Algebra.Module.Equiv.Defs

/-! # Graded linear quivers

A graded `R`-linear quiver on a type of objects `Obj` assigns to each pair of objects `X` and
`Y` and each degree `i : β` an `R`-module `Hom R X Y i` of morphisms of degree `i`. It is the
underlying data of an A∞-category, before any compositions are chosen.

## Main definitions

* `AInfinityTheory.GradedLinearQuiver β R Obj`: a graded `R`-linear quiver.
* `AInfinityTheory.GradedLinearQuiver.ComposableHom`: the graded hom space containing the
  `i`-th morphism of a composable string of objects.
* `AInfinityTheory.GradedLinearQuiver.homCongr`: transport between graded hom spaces along
  equalities of the source, target and degree.

## Notation

* `X →ᵍ[R] Y`: the graded family `GradedLinearQuiver.Hom R X Y : β → Type*` of morphisms from
  `X` to `Y`, so that `(X →ᵍ[R] Y) i` is the `R`-module of morphisms of degree `i`. The variant
  `X →ᵍ[R, β] Y` names the type of degrees explicitly. Both are scoped to
  `AInfinityTheory.GradedLinearQuiver`.
-/

@[expose] public section

namespace AInfinityTheory

universe u v w w'

/-- A graded `R`-linear quiver: for objects `X` and `Y` and a degree `i`, the morphisms of
degree `i` from `X` to `Y` form an `R`-module `Hom R X Y i`. -/
class GradedLinearQuiver (β : Type v) (R : Type u) [Semiring R] (Obj : Type w) where
  /-- The morphisms of degree `i` from `X` to `Y`. The ring `R` is an explicit argument so that
  the notation `X →ᵍ[R] Y` can display it. -/
  Hom (R) : Obj → Obj → β → Type w'
  /-- Each graded piece of a hom space is an abelian group. -/
  homGroup : ∀ X Y i, AddCommGroup (Hom X Y i) := by infer_instance
  /-- Each graded piece of a hom space is an `R`-module. -/
  homModule : ∀ X Y i, Module R (Hom X Y i) := by infer_instance

attribute [instance_reducible, instance] GradedLinearQuiver.homGroup
  GradedLinearQuiver.homModule

namespace GradedLinearQuiver

variable {β : Type v} {R : Type u} [Semiring R] {Obj : Type w} [GradedLinearQuiver β R Obj]
variable {n : ℕ}

/-- `X →ᵍ[R] Y` is the graded family of `R`-modules of morphisms from `X` to `Y` in a graded
`R`-linear quiver, so `(X →ᵍ[R] Y) i` is the module of morphisms of
degree `i`. -/
scoped notation:25 X " →ᵍ[" R:25 "] " Y:0 => GradedLinearQuiver.Hom R X Y

/-- `X →ᵍ[R, β] Y` is `X →ᵍ[R] Y` with the type of degrees `β` given explicitly, for use when `β`
cannot be inferred from a degree or the expected type. -/
scoped notation:25 X " →ᵍ[" R:25 ", " B "] " Y:0 =>
  GradedLinearQuiver.Hom (β := B) R X Y

variable (β R) in
/-- The graded hom space containing the `i`-th morphism of a composable string of objects
`X 0`, …, `X n`: the graded family `X i.castSucc →ᵍ[R] X i.succ`. -/
abbrev ComposableHom (X : Fin (n + 1) → Obj) (i : Fin n) : β → Type w' :=
  X i.castSucc →ᵍ[R] X i.succ

variable (R) in
/-- Transport between graded hom spaces along equalities of the source, target and degree.
This is the three-index form of `LinearEquiv.cast`. -/
def homCongr {X X' Y Y' : Obj} {i i' : β} (hX : X = X') (hY : Y = Y') (hi : i = i') :
    (X →ᵍ[R] Y) i ≃ₗ[R] (X' →ᵍ[R] Y') i' := by
  subst hX hY hi
  exact LinearEquiv.refl R _

@[simp]
lemma homCongr_refl (X Y : Obj) (i : β) :
    homCongr R (rfl : X = X) (rfl : Y = Y) (rfl : i = i) = LinearEquiv.refl R _ :=
  rfl

@[simp]
lemma homCongr_symm {X X' Y Y' : Obj} {i i' : β} (hX : X = X') (hY : Y = Y') (hi : i = i') :
    (homCongr R hX hY hi).symm = homCongr R hX.symm hY.symm hi.symm := by
  subst hX hY hi
  rfl

@[simp]
lemma homCongr_trans {X X' X'' Y Y' Y'' : Obj} {i i' i'' : β} (hX : X = X') (hY : Y = Y')
    (hi : i = i') (hX' : X' = X'') (hY' : Y' = Y'') (hi' : i' = i'') :
    (homCongr R hX hY hi).trans (homCongr R hX' hY' hi') =
      homCongr R (hX.trans hX') (hY.trans hY') (hi.trans hi') := by
  subst hX hY hi hX' hY' hi'
  rfl

/-! ### The type of all morphisms -/

variable (β R Obj) in
/-- The type of all morphisms of a graded linear quiver: a morphism bundled with its source, its
target and its degree. Two morphisms in hom spaces that are only propositionally equal can be
compared in this type without transporting either of them. -/
structure Total where
  /-- The source of the morphism. -/
  src : Obj
  /-- The target of the morphism. -/
  tgt : Obj
  /-- The degree of the morphism. -/
  deg : β
  /-- The morphism. -/
  hom : (src →ᵍ[R] tgt) deg

namespace Total

/-- A morphism of degree `d` from `X` to `Y`, as an element of the type of all morphisms. -/
def of {X Y : Obj} {d : β} (x : (X →ᵍ[R] Y) d) : Total β R Obj :=
  ⟨X, Y, d, x⟩

/-- Transports along equalities of the source, target and degree are invisible in the type of
all morphisms. -/
@[simp]
lemma of_homCongr {X X' Y Y' : Obj} {d d' : β} (hX : X = X') (hY : Y = Y') (hd : d = d')
    (x : (X →ᵍ[R] Y) d) : of (homCongr R hX hY hd x) = of x := by
  subst hX hY hd
  rfl

@[simp]
lemma of_inj {X Y : Obj} {d : β} {x y : (X →ᵍ[R] Y) d} : of x = of y ↔ x = y :=
  ⟨fun h ↦ by cases h; rfl, congrArg of⟩

/-- An equality in the type of all morphisms gives the equality with a transport, for any proofs
of the equalities of the sources, targets and degrees. -/
lemma homCongr_eq_of_of_eq {X X' Y Y' : Obj} {d d' : β} {x : (X →ᵍ[R] Y) d}
    {y : (X' →ᵍ[R] Y') d'} (h : of x = of y) (hX : X = X') (hY : Y = Y') (hd : d = d') :
    homCongr R hX hY hd x = y :=
  of_inj.1 ((of_homCongr hX hY hd x).trans h)

/-- A composable string of at least one morphism determines its objects. -/
lemma obj_eq_of_of_eq {k : ℕ} [NeZero k] {Y Y' : Fin (k + 1) → Obj} {δ δ' : Fin k → β}
    {b : ∀ i, ComposableHom β R Y i (δ i)} {b' : ∀ i, ComposableHom β R Y' i (δ' i)}
    (hb : ∀ i, of (b i) = of (b' i)) : Y = Y' := by
  funext i
  induction i using Fin.cases with
  | zero => exact congrArg src (hb 0)
  | succ i => exact congrArg tgt (hb i)

/-- A function of a composable string of at least one morphism only depends on the morphisms, as
elements of the type of all morphisms: no hypothesis on the objects or on the degrees is
needed. -/
theorem congr_composable {α : Sort*}
    (Ψ : ∀ (k : ℕ) [NeZero k] (Y : Fin (k + 1) → Obj) (δ : Fin k → β),
      (∀ i, ComposableHom β R Y i (δ i)) → α)
    {k k' : ℕ} [NeZero k] [NeZero k'] (e : k = k') {Y : Fin (k + 1) → Obj}
    {Y' : Fin (k' + 1) → Obj} {δ : Fin k → β} {δ' : Fin k' → β}
    {b : ∀ i, ComposableHom β R Y i (δ i)} {b' : ∀ i, ComposableHom β R Y' i (δ' i)}
    (hb : ∀ i, of (b i) = of (b' (i.cast e))) : Ψ k Y δ b = Ψ k' Y' δ' b' := by
  subst e
  obtain rfl : Y = Y' := obj_eq_of_of_eq hb
  obtain rfl : δ = δ' := funext fun i ↦ congrArg deg (hb i)
  obtain rfl : b = b' := funext fun i ↦ of_inj.1 (hb i)
  rfl

end Total

end GradedLinearQuiver

end AInfinityTheory
