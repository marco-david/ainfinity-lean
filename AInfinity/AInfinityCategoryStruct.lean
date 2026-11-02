/-
Copyright (c) 2026 Annie Yao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Annie Yao, Marco David, Zhan Shi
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import AInfinity.Grading
public import AInfinity.GradedLinearAlgebra
public import AInfinity.GradedLinearQuiver
public import AInfinity.MultilinearMap

/-! # A∞-category structures

An `A∞`-category structure on a graded `R`-linear quiver consists of higher compositions
`mₙ : Hom(X₀, X₁) ⊗ ⋯ ⊗ Hom(Xₙ₋₁, Xₙ) → Hom(X₀, Xₙ)` of degree `2 - n`, one for each `n ≥ 1`.
This file defines such structures, and constructors for operations, such as those of DG
categories and of linear categories, that vanish above arity two.

## Main definitions

* `AInfinityTheory.AInfinityOperation β R X`: the `n`-ary operations of degree `2 - n` on a
  composable string of objects `X`.
* `AInfinityTheory.AInfinityCategoryStruct β R Obj`: a graded `R`-linear quiver with higher
  compositions `mₙ`, not yet subject to any relations.
* `AInfinityTheory.AInfinityOperation.ofGradedLinearMap`: a unary operation from a graded
  linear map of degree `1`.
* `AInfinityTheory.AInfinityOperation.ofBilinear`: a binary operation from a family of bilinear
  maps of degree `0`.
* `AInfinityTheory.AInfinityOperation.ofArityLeTwo`: the family of operations with given unary
  and binary operations that vanish in arity at least three.

## Implementation notes

`ofGradedLinearMap` and `ofBilinear` take their inputs in terms of the hom spaces
`(X →ᵍ[R] Y) p`, and hide both `ComposableHom` and the degree arithmetic
`(∑ k, deg k) + shift (2 - n) = j` from the user.

The ring of scalars `R` is an ordinary class parameter, so an object type may carry several
rings of scalars. It is passed explicitly wherever it cannot be inferred from later arguments:
to the hom spaces `(X →ᵍ[R] Y) i`, `ComposableHom`, `AInfinityOperation` and `homCongr`. The
type of degrees `β` is passed explicitly to `ComposableHom` and `AInfinityOperation` as well.
-/
@[expose] public section

namespace AInfinityTheory

universe u v w

open GradedLinearQuiver

variable {β : Type v} [AddCommGroup β] [Grading β]
variable {R : Type u} [CommRing R] {Obj : Type w}

section

variable [GradedLinearQuiver β R Obj]

variable (β R) in
/-- The `n`-ary `A∞` operations on a composable string of objects `X`: graded multilinear
maps of degree `2 - n` from the composable hom spaces to the hom space from `X 0` to
`X (Fin.last n)`. -/
abbrev AInfinityOperation {n : ℕ} (X : Fin (n + 1) → Obj) :=
  GradedMultilinearMap R (ComposableHom β R X) (X 0 →ᵍ[R] X (Fin.last n))
    (shift (2 - (n : ℤ)))

end

variable (β R Obj) in
/-- The data of an `A∞`-category: a graded `R`-linear quiver together with, for each `n ≥ 1`
and each composable string of objects `X`, a higher composition `mₙ` of degree `2 - n` from the
composable hom spaces to the hom space from `X 0` to `X (Fin.last n)`. No relations are
imposed. -/
class AInfinityCategoryStruct extends GradedLinearQuiver β R Obj where
  /-- The higher compositions `mₙ`. -/
  m {n : ℕ} [NeZero n] (X : Fin (n + 1) → Obj) : AInfinityOperation β R X

variable [GradedLinearQuiver β R Obj]

namespace AInfinityOperation

/-- The unary operation given by a graded linear map `f` of degree `1` on the morphisms from
`X 0` to `X 1`, such as the differential of a DG category. -/
def ofGradedLinearMap {X : Fin (1 + 1) → Obj}
    (f : GradedLinearMap R (X 0 →ᵍ[R, β] X 1) (X 0 →ᵍ[R] X 1) (shift 1)) :
    AInfinityOperation β R X :=
  .mk fun deg j h ↦ MultilinearMap.ofSubsingletonₗ' 0 (f.v (deg 0) j (by simpa using h))

@[simp]
theorem ofGradedLinearMap_v_apply {X : Fin (1 + 1) → Obj}
    (f : GradedLinearMap R (X 0 →ᵍ[R, β] X 1) (X 0 →ᵍ[R] X 1) (shift 1)) (deg : Fin 1 → β)
    (j : β) (h : (∑ k, deg k) + shift (2 - ((1 : ℕ) : ℤ)) = j)
    (x : ∀ k, ComposableHom β R X k (deg k)) :
    (ofGradedLinearMap f).v deg j h x = f.v (deg 0) j (by simpa using h) (x 0) :=
  rfl

/-- The binary operation given by a family of bilinear maps `f p q j`, sending morphisms of
degrees `p` and `q` to a morphism of degree `j = p + q`, such as the composition of a DG
category. -/
def ofBilinear {X : Fin (2 + 1) → Obj}
    (f : ∀ p q j : β, p + q = j →
      (X 0 →ᵍ[R, β] X 1) p →ₗ[R] (X 1 →ᵍ[R] X 2) q →ₗ[R] (X 0 →ᵍ[R] X 2) j) :
    AInfinityOperation β R X :=
  .mk fun deg j h ↦
    LinearMap.uncurryFinTwo (f (deg 0) (deg 1) j (by simpa [Fin.sum_univ_two] using h))

@[simp]
theorem ofBilinear_v_apply {X : Fin (2 + 1) → Obj}
    (f : ∀ p q j : β, p + q = j →
      (X 0 →ᵍ[R, β] X 1) p →ₗ[R] (X 1 →ᵍ[R] X 2) q →ₗ[R] (X 0 →ᵍ[R] X 2) j)
    (deg : Fin 2 → β) (j : β) (h : (∑ k, deg k) + shift (2 - ((2 : ℕ) : ℤ)) = j)
    (x : ∀ k, ComposableHom β R X k (deg k)) :
    (ofBilinear f).v deg j h x =
      f (deg 0) (deg 1) j (by simpa [Fin.sum_univ_two] using h) (x 0) (x 1) :=
  rfl

variable (m₁ : ∀ X : Fin (1 + 1) → Obj, AInfinityOperation β R X)
  (m₂ : ∀ X : Fin (2 + 1) → Obj, AInfinityOperation β R X)

/-- The family of operations with unary operations `m₁` and binary operations `m₂`, and
vanishing operations in every arity `n ≥ 3`. -/
def ofArityLeTwo {n : ℕ} [NeZero n] (X : Fin (n + 1) → Obj) : AInfinityOperation β R X :=
  match n with
    | 1 => m₁ X
    | 2 => m₂ X
    | _ => 0

@[simp]
theorem ofArityLeTwo_one (X : Fin (1 + 1) → Obj) : ofArityLeTwo m₁ m₂ X = m₁ X :=
  rfl

@[simp]
theorem ofArityLeTwo_two (X : Fin (2 + 1) → Obj) : ofArityLeTwo m₁ m₂ X = m₂ X :=
  rfl

theorem ofArityLeTwo_eq_zero {n : ℕ} [NeZero n] (h₁ : n ≠ 1) (h₂ : n ≠ 2)
    (X : Fin (n + 1) → Obj) : ofArityLeTwo m₁ m₂ X = 0 := by
  unfold ofArityLeTwo
  split <;> simp_all

end AInfinityOperation

end AInfinityTheory
