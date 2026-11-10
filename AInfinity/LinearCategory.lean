/-
Copyright (c) 2026 Zhan Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhan Shi
-/
module

public import AInfinity.ArityLeTwo
public import Mathlib.Algebra.Module.Basic
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.LinearAlgebra.BilinearMap

/-! # Linear categories as A∞-categories

An `R`-linear category `C` is an A∞-category for any grading `β`: all morphisms sit in degree
`0`, m₂ is composition, and m₁ = m₃ = m₄ = ⋯ = 0. The only nontrivial Stasheff identity is the
one in arity 3, which says that composition is associative.

## Main definitions

* `AInfinityTheory.GradedLinearQuiver.ofLinearCategory β R C`: the graded `R`-linear quiver of a
  linear category `C`, concentrated in degree `0`.
* `AInfinityTheory.GradedLinearQuiver.ofLinearCategory.composition`: the composition of `C` as a
  bilinear map of degree `0` between graded hom spaces.
* `AInfinityTheory.AInfinityCategory.ofLinearCategory β R C`: the A∞-category with m₂ the
  composition of `C` and all other operations zero, built with `AInfinityCategory.ofArityLeTwo`.

## Implementation notes

The morphisms of degree `i` from `X` to `Y` are the submodule ⨅ (_ : i ≠ 0), ⊥ of `X ⟶ Y`: all
of `X ⟶ Y` in degree `0`, and zero otherwise. Using a submodule for every degree avoids casts
along `i = 0`. It also forces the ring of scalars to be a ring rather than a semiring: a
submodule over a semiring need not be an additive group. The quiver is a definition rather than
a global instance, since it would apply to every linear category and conflict with other graded
structures on the same objects, such as that of a DG category.
-/

@[expose] public section

namespace AInfinityTheory

universe u v w w'

open CategoryTheory GradedLinearQuiver

variable (β : Type v) [AddCommGroup β] (R : Type u) [CommRing R] (C : Type w)
  [Category.{w'} C] [Preadditive C] [Linear R C]

/-- The graded `R`-linear quiver of an `R`-linear category `C`, concentrated in degree `0`: the
morphisms of degree `0` from `X` to `Y` are all of `X ⟶ Y`, and there are no nonzero morphisms
in any other degree. -/
abbrev GradedLinearQuiver.ofLinearCategory : GradedLinearQuiver β R C where
  Hom X Y i := ↥(⨅ _ : i ≠ 0, (⊥ : Submodule R (X ⟶ Y)))

namespace GradedLinearQuiver.ofLinearCategory

attribute [local instance] GradedLinearQuiver.ofLinearCategory

variable {β R C}

lemma val_eq_zero_of_ne_zero {X Y : C} {i : β} (hi : i ≠ 0) (a : (X →ᵍ[R] Y) i) :
    Subtype.val a = 0 :=
  (Submodule.mem_bot R).1 <| (Submodule.mem_iInf _).1 a.2 hi

lemma eq_zero_of_ne_zero {X Y : C} {i : β} (hi : i ≠ 0) (a : (X →ᵍ[R] Y) i) : a = 0 :=
  Subtype.ext (val_eq_zero_of_ne_zero hi a)

/-- The composite of morphisms of degrees `p` and `q` has degree `p + q`. -/
lemma comp_mem {X Y Z : C} {p q i : β} (h : p + q = i) (a : (X →ᵍ[R] Y) p)
    (b : (Y →ᵍ[R] Z) q) :
    Subtype.val a ≫ Subtype.val b ∈ ⨅ _ : i ≠ 0, (⊥ : Submodule R (X ⟶ Z)) := by
  refine (Submodule.mem_iInf _).2 fun hi ↦ (Submodule.mem_bot R).2 ?_
  rcases eq_or_ne p 0 with rfl | hp
  · rw [val_eq_zero_of_ne_zero (by simpa [← h] using hi) b, Limits.comp_zero]
  · rw [val_eq_zero_of_ne_zero hp a, Limits.zero_comp]

variable (R) in
/-- The composition of a linear category, as a bilinear map sending morphisms of degrees `p`
and `q` to their composite, of degree `i = p + q`. -/
def composition (X Y Z : C) (p q i : β) (h : p + q = i) :
    (X →ᵍ[R] Y) p →ₗ[R] (Y →ᵍ[R] Z) q →ₗ[R] (X →ᵍ[R] Z) i :=
  .mk₂ R (fun a b ↦ ⟨a.1 ≫ b.1, comp_mem h a b⟩)
    (fun a a' b ↦ Subtype.ext (Preadditive.add_comp _ _ _ a.1 a'.1 b.1))
    (fun c a b ↦ Subtype.ext (Linear.smul_comp _ _ _ c a.1 b.1))
    (fun a b b' ↦ Subtype.ext (Preadditive.comp_add _ _ _ a.1 b.1 b'.1))
    (fun c a b ↦ Subtype.ext (Linear.comp_smul _ _ _ a.1 c b.1))

@[simp]
lemma composition_apply_val (X Y Z : C) (p q i : β) (h : p + q = i) (a : (X →ᵍ[R] Y) p)
    (b : (Y →ᵍ[R] Z) q) :
    Subtype.val (composition R X Y Z p q i h a b) = Subtype.val a ≫ Subtype.val b :=
  rfl

variable [Grading β]

/-- The composition is associative, in the form of the arity-three Stasheff identity: the
Koszul sign (-1)^(r - 1) of `c` is `-1` when `c` has degree `r = 0`, and `c` vanishes
otherwise. -/
lemma composition_composition (W X Y Z : C) {p q r e e' d : β} (h : p + q = e)
    (h' : q + r = e') (h₁ : e + r = d) (a : (W →ᵍ[R] X) p) (b : (X →ᵍ[R] Y) q)
    (c : (Y →ᵍ[R] Z) r) :
    (sign (r - degOne)).toMul • composition R W Y Z e r d h₁ (composition R W X Y p q e h a b) c +
      composition R W X Z p e' d (h' ▸ h₁ ▸ h ▸ (add_assoc p q r).symm) a
        (composition R X Y Z q r e' h' b c) = 0 := by
  rcases eq_or_ne r 0 with rfl | hr
  · have hs : (sign (0 - degOne : β)).toMul = -1 := by simp [Grading.sign_degOne]
    rw [hs, Units.neg_smul, one_smul, neg_add_eq_zero]
    exact Subtype.ext (Category.assoc _ _ _)
  · simp [eq_zero_of_ne_zero hr c]

end GradedLinearQuiver.ofLinearCategory

variable [Grading β]

open GradedLinearQuiver.ofLinearCategory in
/-- A (strict) `R`-linear category is an A∞-category, for any grading `β`: all morphisms sit in
degree `0`, m₂ is composition and m₁ = m₃ = m₄ = ⋯ = 0. The only nontrivial Stasheff identity
is the one in arity 3, which says that composition is associative. -/
abbrev AInfinityCategory.ofLinearCategory : AInfinityCategory β R C :=
  letI := GradedLinearQuiver.ofLinearCategory β R C
  .ofArityLeTwo 0 (composition R) (by intros; simp) (by intros; simp) composition_composition

end AInfinityTheory
