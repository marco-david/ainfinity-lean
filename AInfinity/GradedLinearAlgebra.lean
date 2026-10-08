/-
Copyright (c) 2026 Zhan Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhan Shi
-/
module

public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.LinearAlgebra.Multilinear.Basic

/-! # Graded linear maps

This file defines graded linear maps of a fixed degree between externally graded modules,
i.e. families of modules `M N : β → Type*` indexed by a grading type `β`.

A graded linear map `f` of degree `d` consists of one linear map `M i →ₗ[R] N j` for each pair of
degrees with `i + d = j`.

## Main definitions

* `AInfinityTheory.GradedLinearMap R M N d`: graded `R`-linear maps of degree `d` from `M` to `N`.
* `AInfinityTheory.GradedLinearMap.id`: the identity graded linear map, of degree `0`.
* `AInfinityTheory.GradedLinearMap.comp`: the composite of graded linear maps of degrees `d` and
  `e`, of any degree `de` with `d + e = de`.
* `AInfinityTheory.GradedMultilinearMap R M N d`: graded `R`-multilinear maps of degree `d` from
  the families `M j`, `j : ι`, to `N`. For input degrees `deg : ι → β`, the component lands in
  any degree `i` with `(∑ j, deg j) + d = i`.

## Main results

* `GradedLinearMap` and `GradedMultilinearMap` are additive commutative monoids (groups if `N`
  is), and modules over any semiring `S` whose action on each `N i` commutes with that of `R`.
* `GradedLinearMap.comp_assoc`, `GradedLinearMap.id_comp`, `GradedLinearMap.comp_id`: graded
  linear maps compose associatively and unitally.

## Implementation notes

Following `CochainComplex.HomComplex.Cochain`, components are indexed by a source degree `i`, a
target degree `j` and a proof of `i + d = j`, rather than by `i` alone with target `N (i + d)`.
The terms `i + 0` and `i + d + e` are not definitionally equal to `i` and `i + (d + e)`, so the
latter choice would force casts into `id` and `comp`. With the proof as an argument, any two
choices of proof are definitionally equal, and a composite factors through any middle degree
(`GradedLinearMap.comp_apply`).

The algebraic structure is transferred from a `Pi` type along `toPi`, which reindexes the
components by the type of pairs `(i, j)` with `i + d = j`; the `Pi` instances in Mathlib do not
apply to the `Prop`-valued binder `i + d = j` directly.

The structures only need an addition on `β`; `comp` needs `AddSemigroup β` and `id` needs
`AddZeroClass β`.
-/

@[expose] public section

namespace AInfinityTheory

universe u v w₁ w₂ w₃ w₄

/-- A graded `R`-linear map of degree `d` from `M` to `N` is a family of `R`-linear maps
`M i →ₗ[R] N j`, one for each pair of degrees with `i + d = j`. It raises the degree of every
homogeneous element by `d`. -/
structure GradedLinearMap (R : Type u) [Semiring R] {β : Type v} [Add β]
    (M : β → Type w₁) (N : β → Type w₂)
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)] (d : β) where
  /-- The component of the graded linear map from degree `i` to degree `j`, where
  `i + d = j`. -/
  toLinearMap : ∀ i j, i + d = j → M i →ₗ[R] N j

namespace GradedLinearMap

variable {R : Type u} [Semiring R] {β : Type v}
variable {M : β → Type w₁} {N : β → Type w₂} {P : β → Type w₃} {Q : β → Type w₄}
variable [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
variable [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]
variable [∀ i, AddCommMonoid (P i)] [∀ i, Module R (P i)]
variable [∀ i, AddCommMonoid (Q i)] [∀ i, Module R (Q i)]

section Add

variable [Add β] {d : β}

/-- A graded linear map is applied to degrees `i` and `j` with `i + d = j` to get its linear
component from degree `i` to degree `j`. -/
instance : CoeFun (GradedLinearMap R M N d) (fun _ ↦ ∀ i j, i + d = j → M i →ₗ[R] N j) :=
  ⟨toLinearMap⟩

attribute [coe] toLinearMap

@[simp]
theorem toLinearMap_eq_coe (f : GradedLinearMap R M N d) : f.toLinearMap = ⇑f :=
  rfl

@[simp]
theorem coe_mk (f : ∀ i j, i + d = j → M i →ₗ[R] N j) :
    ⇑(⟨f⟩ : GradedLinearMap R M N d) = f :=
  rfl

/-- A graded linear map is determined by its components. -/
theorem coe_injective : Function.Injective (fun f : GradedLinearMap R M N d ↦ ⇑f) :=
  fun ⟨_⟩ ⟨_⟩ h ↦ congrArg mk h

/-- Two graded linear maps are equal if they agree on every homogeneous element. -/
@[ext]
theorem ext {f g : GradedLinearMap R M N d} (h : ∀ i j hij x, f i j hij x = g i j hij x) :
    f = g :=
  coe_injective <| funext fun i ↦ funext fun j ↦ funext fun hij ↦ LinearMap.ext (h i j hij)

/-- The components of a graded linear map, indexed by the type of pairs of degrees `(i, j)`
with `i + d = j`. The `Pi` instances apply to this indexing, so it is used to transfer algebraic
structure to graded linear maps. -/
def toPi (f : GradedLinearMap R M N d) (p : {p : β × β // p.1 + d = p.2}) :
    M p.1.1 →ₗ[R] N p.1.2 :=
  f p.1.1 p.1.2 p.2

@[simp]
theorem toPi_apply (f : GradedLinearMap R M N d) (p : {p : β × β // p.1 + d = p.2}) :
    f.toPi p = f p.1.1 p.1.2 p.2 :=
  rfl

theorem toPi_injective : Function.Injective (toPi : GradedLinearMap R M N d → _) :=
  fun _ _ h ↦ ext fun i j hij ↦ LinearMap.congr_fun (congr_fun h ⟨(i, j), hij⟩)

section AddCommMonoid

/-- The zero graded linear map sends every homogeneous element to zero. -/
instance : Zero (GradedLinearMap R M N d) :=
  ⟨⟨fun _ _ _ ↦ 0⟩⟩

/-- Graded linear maps of the same degree are added componentwise. -/
instance : Add (GradedLinearMap R M N d) :=
  ⟨fun f g ↦ ⟨fun i j hij ↦ f i j hij + g i j hij⟩⟩

/-- Scalar multiplication on graded linear maps is defined componentwise. -/
instance {S : Type*} [Monoid S] [∀ i, DistribMulAction S (N i)]
    [∀ i, SMulCommClass R S (N i)] : SMul S (GradedLinearMap R M N d) :=
  ⟨fun c f ↦ ⟨fun i j hij ↦ c • f i j hij⟩⟩

@[simp]
theorem zero_apply (i j : β) (hij : i + d = j) : (0 : GradedLinearMap R M N d) i j hij = 0 :=
  rfl

@[simp]
theorem add_apply (f g : GradedLinearMap R M N d) (i j : β) (hij : i + d = j) :
    (f + g) i j hij = f i j hij + g i j hij :=
  rfl

@[simp]
theorem smul_apply {S : Type*} [Monoid S] [∀ i, DistribMulAction S (N i)]
    [∀ i, SMulCommClass R S (N i)] (c : S) (f : GradedLinearMap R M N d) (i j : β)
    (hij : i + d = j) : (c • f) i j hij = c • f i j hij :=
  rfl

/-- The components of the natural-number multiple `n • f` are the multiples `n • f i j hij`. -/
instance : SMul ℕ (GradedLinearMap R M N d) :=
  ⟨fun n f ↦ ⟨fun i j hij ↦ n • f i j hij⟩⟩

/-- Graded linear maps of degree `d` form an additive commutative monoid under componentwise
addition. -/
instance : AddCommMonoid (GradedLinearMap R M N d) :=
  toPi_injective.addCommMonoid _ rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

/-- Graded linear maps of degree `d` form a module over any semiring `S` acting on the target
compatibly with `R`. -/
instance {S : Type*} [Semiring S] [∀ i, Module S (N i)] [∀ i, SMulCommClass R S (N i)] :
    Module S (GradedLinearMap R M N d) :=
  toPi_injective.module S ⟨⟨toPi, rfl⟩, fun _ _ ↦ rfl⟩ fun _ _ ↦ rfl

end AddCommMonoid

section AddCommGroup

variable {N : β → Type w₂} [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]

/-- The negation of a graded linear map is taken componentwise. -/
instance : Neg (GradedLinearMap R M N d) :=
  ⟨fun f ↦ ⟨fun i j hij ↦ -f i j hij⟩⟩

/-- The difference of two graded linear maps is taken componentwise. -/
instance : Sub (GradedLinearMap R M N d) :=
  ⟨fun f g ↦ ⟨fun i j hij ↦ f i j hij - g i j hij⟩⟩

/-- The components of the integer multiple `n • f` are the multiples `n • f i j hij`. -/
instance : SMul ℤ (GradedLinearMap R M N d) :=
  ⟨fun n f ↦ ⟨fun i j hij ↦ n • f i j hij⟩⟩

@[simp]
theorem neg_apply (f : GradedLinearMap R M N d) (i j : β) (hij : i + d = j) :
    (-f) i j hij = -f i j hij :=
  rfl

@[simp]
theorem sub_apply (f g : GradedLinearMap R M N d) (i j : β) (hij : i + d = j) :
    (f - g) i j hij = f i j hij - g i j hij :=
  rfl

/-- Graded linear maps of degree `d` into a family of additive groups form an additive
commutative group. -/
instance : AddCommGroup (GradedLinearMap R M N d) :=
  toPi_injective.addCommGroup _ rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

end AddCommGroup

end Add

section Composition

variable [AddSemigroup β] {d e de : β}

/-- The composite of graded linear maps of degrees `d` and `e` is a graded linear map of any
degree `de` with `d + e = de`. Its component from degree `i` factors through degree `i + d`. -/
def comp (g : GradedLinearMap R N P e) (f : GradedLinearMap R M N d) (h : d + e = de) :
    GradedLinearMap R M P de :=
  ⟨fun i k hik ↦ (g (i + d) k (by rw [add_assoc, h, hik])).comp (f i (i + d) rfl)⟩

/-- A component of a composite of graded linear maps factors through any middle degree `j`. -/
theorem comp_apply (g : GradedLinearMap R N P e) (f : GradedLinearMap R M N d) (h : d + e = de)
    {i j k : β} (hij : i + d = j) (hjk : j + e = k) (hik : i + de = k) :
    g.comp f h i k hik = (g j k hjk).comp (f i j hij) := by
  subst hij
  rfl

/-- Composition of graded linear maps is associative, for any choice of degrees of the
intermediate composites. -/
theorem comp_assoc {d₁ d₂ d₃ d₁₂ d₂₃ d₁₂₃ : β} (f₁ : GradedLinearMap R M N d₁)
    (f₂ : GradedLinearMap R N P d₂) (f₃ : GradedLinearMap R P Q d₃) (h₁₂ : d₁ + d₂ = d₁₂)
    (h₂₃ : d₂ + d₃ = d₂₃) (h₁₂₃ : d₁₂ + d₃ = d₁₂₃) (h₁₂₃' : d₁ + d₂₃ = d₁₂₃) :
    (f₃.comp f₂ h₂₃).comp f₁ h₁₂₃' = f₃.comp (f₂.comp f₁ h₁₂) h₁₂₃ := by
  ext i l hil x
  exact LinearMap.congr_fun (comp_apply f₃ (f₂.comp f₁ h₁₂) h₁₂₃ (j := i + d₁ + d₂)
    (by rw [← h₁₂, add_assoc]) (by rw [← hil, ← h₁₂₃', ← h₂₃]; simp only [add_assoc]) hil).symm x

end Composition

section Identity

variable [AddZeroClass β]

/-- The identity graded linear map, of degree `0`. Its component from degree `i` to degree `j`
is the identity, transported along `i = i + 0 = j`. -/
def id : GradedLinearMap R M M 0 :=
  ⟨fun i j h ↦ by obtain rfl : i = j := (add_zero i).symm.trans h; exact LinearMap.id⟩

@[simp]
theorem id_apply (i : β) (h : i + 0 = i := add_zero i) :
    (id : GradedLinearMap R M M 0) i i h = LinearMap.id :=
  rfl

end Identity

section Monoid

variable [AddMonoid β] {d : β}

@[simp]
theorem id_comp (f : GradedLinearMap R M N d) :
    (id : GradedLinearMap R N N 0).comp f (add_zero d) = f := by
  ext i k hik x
  rw [comp_apply _ _ _ hik (add_zero k) hik, id_apply, LinearMap.id_comp]

@[simp]
theorem comp_id (f : GradedLinearMap R M N d) :
    f.comp (id : GradedLinearMap R M M 0) (zero_add d) = f := by
  ext i k hik x
  rw [comp_apply _ _ _ (add_zero i) hik hik, id_apply, LinearMap.comp_id]

end Monoid

end GradedLinearMap

/-- A graded `R`-multilinear map of degree `d` from the families `M j` (for `j : ι`) to `N`
consists of, for each choice of input degrees `deg : ι → β` and each output degree `i` with
`(∑ j, deg j) + d = i`, an `R`-multilinear map from `∀ j, M j (deg j)` to `N i`. The output
degree is the total input degree shifted by `d`. -/
structure GradedMultilinearMap (R : Type u) [Semiring R] {ι : Type*} [Fintype ι]
    {β : Type v} [AddCommMonoid β] (M : ι → β → Type w₁) (N : β → Type w₂)
    [∀ j i, AddCommMonoid (M j i)] [∀ j i, Module R (M j i)]
    [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)] (d : β) where
  /-- The component of the graded multilinear map with input degrees `deg` and output degree
  `i`, where `(∑ j, deg j) + d = i`. -/
  toMultilinearMap :
    ∀ (deg : ι → β) (i : β), (∑ j, deg j) + d = i →
      MultilinearMap R (fun j ↦ M j (deg j)) (N i)

namespace GradedMultilinearMap

variable {R : Type u} [Semiring R] {ι : Type*} [Fintype ι] {β : Type v} [AddCommMonoid β]
variable {M : ι → β → Type w₁} {N : β → Type w₂}
variable [∀ j i, AddCommMonoid (M j i)] [∀ j i, Module R (M j i)]
variable [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)] {d : β}

/-- A graded multilinear map is applied to input degrees `deg` and an output degree `i` with
`(∑ j, deg j) + d = i` to get the corresponding multilinear component. -/
instance : CoeFun (GradedMultilinearMap R M N d) (fun _ ↦ ∀ (deg : ι → β) (i : β),
    (∑ j, deg j) + d = i → MultilinearMap R (fun j ↦ M j (deg j)) (N i)) :=
  ⟨toMultilinearMap⟩

attribute [coe] toMultilinearMap

@[simp]
theorem toMultilinearMap_eq_coe (f : GradedMultilinearMap R M N d) :
    f.toMultilinearMap = ⇑f :=
  rfl

@[simp]
theorem coe_mk (f : ∀ (deg : ι → β) (i : β), (∑ j, deg j) + d = i →
    MultilinearMap R (fun j ↦ M j (deg j)) (N i)) :
    ⇑(⟨f⟩ : GradedMultilinearMap R M N d) = f :=
  rfl

/-- A graded multilinear map is determined by its components. -/
theorem coe_injective : Function.Injective (fun f : GradedMultilinearMap R M N d ↦ ⇑f) :=
  fun ⟨_⟩ ⟨_⟩ h ↦ congrArg mk h

/-- Two graded multilinear maps are equal if they agree on every tuple of homogeneous
elements. -/
@[ext]
theorem ext {f g : GradedMultilinearMap R M N d}
    (h : ∀ deg i hi x, f deg i hi x = g deg i hi x) : f = g :=
  coe_injective <| funext fun deg ↦ funext fun i ↦ funext fun hi ↦ MultilinearMap.ext (h deg i hi)

/-- The components of a graded multilinear map, indexed by the type of pairs `(deg, i)` with
`(∑ j, deg j) + d = i`. The `Pi` instances apply to this indexing, so it is used to transfer
algebraic structure to graded multilinear maps. -/
def toPi (f : GradedMultilinearMap R M N d) (p : {p : (ι → β) × β // (∑ j, p.1 j) + d = p.2}) :
    MultilinearMap R (fun j ↦ M j (p.1.1 j)) (N p.1.2) :=
  f p.1.1 p.1.2 p.2

@[simp]
theorem toPi_apply (f : GradedMultilinearMap R M N d)
    (p : {p : (ι → β) × β // (∑ j, p.1 j) + d = p.2}) : f.toPi p = f p.1.1 p.1.2 p.2 :=
  rfl

theorem toPi_injective : Function.Injective (toPi : GradedMultilinearMap R M N d → _) :=
  fun _ _ h ↦ ext fun deg i hi ↦ MultilinearMap.congr_fun (congr_fun h ⟨(deg, i), hi⟩)

section AddCommMonoid

/-- The zero graded multilinear map sends every tuple of homogeneous elements to zero. -/
instance : Zero (GradedMultilinearMap R M N d) :=
  ⟨⟨fun _ _ _ ↦ 0⟩⟩

/-- Graded multilinear maps of the same degree are added componentwise. -/
instance : Add (GradedMultilinearMap R M N d) :=
  ⟨fun f g ↦ ⟨fun deg i hi ↦ f deg i hi + g deg i hi⟩⟩

/-- Scalar multiplication on graded multilinear maps is defined componentwise. -/
instance {S : Type*} [∀ i, DistribSMul S (N i)] [∀ i, SMulCommClass R S (N i)] :
    SMul S (GradedMultilinearMap R M N d) :=
  ⟨fun c f ↦ ⟨fun deg i hi ↦ c • f deg i hi⟩⟩

@[simp]
theorem zero_apply (deg : ι → β) (i : β) (hi : (∑ j, deg j) + d = i) :
    (0 : GradedMultilinearMap R M N d) deg i hi = 0 :=
  rfl

@[simp]
theorem add_apply (f g : GradedMultilinearMap R M N d) (deg : ι → β) (i : β)
    (hi : (∑ j, deg j) + d = i) : (f + g) deg i hi = f deg i hi + g deg i hi :=
  rfl

@[simp]
theorem smul_apply {S : Type*} [∀ i, DistribSMul S (N i)] [∀ i, SMulCommClass R S (N i)]
    (c : S) (f : GradedMultilinearMap R M N d) (deg : ι → β) (i : β)
    (hi : (∑ j, deg j) + d = i) : (c • f) deg i hi = c • f deg i hi :=
  rfl

/-- The components of the natural-number multiple `n • f` are the multiples `n • f deg i hi`. -/
instance : SMul ℕ (GradedMultilinearMap R M N d) :=
  ⟨fun n f ↦ ⟨fun deg i hi ↦ n • f deg i hi⟩⟩

/-- Graded multilinear maps of degree `d` form an additive commutative monoid under
componentwise addition. -/
instance : AddCommMonoid (GradedMultilinearMap R M N d) :=
  toPi_injective.addCommMonoid _ rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

/-- Graded multilinear maps of degree `d` form a module over any semiring `S` acting on the
target compatibly with `R`. -/
instance {S : Type*} [Semiring S] [∀ i, Module S (N i)] [∀ i, SMulCommClass R S (N i)] :
    Module S (GradedMultilinearMap R M N d) :=
  toPi_injective.module S ⟨⟨toPi, rfl⟩, fun _ _ ↦ rfl⟩ fun _ _ ↦ rfl

end AddCommMonoid

section AddCommGroup

variable {N : β → Type w₂} [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]

/-- The negation of a graded multilinear map is taken componentwise. -/
instance : Neg (GradedMultilinearMap R M N d) :=
  ⟨fun f ↦ ⟨fun deg i hi ↦ -f deg i hi⟩⟩

/-- The difference of two graded multilinear maps is taken componentwise. -/
instance : Sub (GradedMultilinearMap R M N d) :=
  ⟨fun f g ↦ ⟨fun deg i hi ↦ f deg i hi - g deg i hi⟩⟩

/-- The components of the integer multiple `n • f` are the multiples `n • f deg i hi`. -/
instance : SMul ℤ (GradedMultilinearMap R M N d) :=
  ⟨fun n f ↦ ⟨fun deg i hi ↦ n • f deg i hi⟩⟩

@[simp]
theorem neg_apply (f : GradedMultilinearMap R M N d) (deg : ι → β) (i : β)
    (hi : (∑ j, deg j) + d = i) : (-f) deg i hi = -f deg i hi :=
  rfl

@[simp]
theorem sub_apply (f g : GradedMultilinearMap R M N d) (deg : ι → β) (i : β)
    (hi : (∑ j, deg j) + d = i) : (f - g) deg i hi = f deg i hi - g deg i hi :=
  rfl

/-- Graded multilinear maps of degree `d` into a family of additive groups form an additive
commutative group. -/
instance : AddCommGroup (GradedMultilinearMap R M N d) :=
  toPi_injective.addCommGroup _ rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

end AddCommGroup

end GradedMultilinearMap

end AInfinityTheory
