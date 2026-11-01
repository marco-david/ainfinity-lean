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

* `AInfinityTheory.GradedLinearMap.Index d`: the pairs of degrees `(i, j)` with `i + d = j`.
* `AInfinityTheory.GradedLinearMap R M N d`: graded `R`-linear maps of degree `d` from `M` to `N`.
* `AInfinityTheory.GradedLinearMap.id`: the identity graded linear map, of degree `0`.
* `AInfinityTheory.GradedLinearMap.comp`: the composite of graded linear maps of degrees `d` and
  `e`, of any degree `de` with `d + e = de`.
* `AInfinityTheory.GradedMultilinearMap.Index ι d`: the input degrees `deg : ι → β` together with
  an output degree `j` with `(∑ k, deg k) + d = j`.
* `AInfinityTheory.GradedMultilinearMap R M N d`: graded `R`-multilinear maps of degree `d` from
  the families `M k`, `k : ι`, to `N`.

## Main results

* `GradedLinearMap` and `GradedMultilinearMap` are additive commutative monoids (groups if `N`
  is), and modules over any semiring `S` whose action on each `N i` commutes with that of `R`.
* `GradedLinearMap.comp_assoc`, `GradedLinearMap.id_comp`, `GradedLinearMap.comp_id`: graded
  linear maps compose associatively and unitally.

## Implementation notes

Following `CochainComplex.HomComplex.Cochain` and `CochainComplex.HomComplex.Triplet`, a graded
linear map of degree `d` is a dependent function on the structure `GradedLinearMap.Index d` of
triples `⟨i, j, hij⟩` with `hij : i + d = j`, rather than a function of `i` alone with target
`N (i + d)`. The terms `i + 0` and `i + d + e` are not definitionally equal to `i` and
`i + (d + e)`, so the latter choice would force casts into `id` and `comp`. With the proof as part
of the index, any two choices of proof are definitionally equal, and a composite factors through
any middle degree (`GradedLinearMap.comp_v`).

Bundling the proof into a structure makes graded linear maps a `Pi` type, so their additive
group and module structures are inherited from Mathlib's `Pi` instances. Components are
constructed with `GradedLinearMap.mk` and read off with `GradedLinearMap.v`, as for `Cochain`.
`GradedMultilinearMap` follows the same pattern with `GradedMultilinearMap.Index`.

The structures only need an addition on `β`; `comp` needs `AddSemigroup β` and `id` needs
`AddZeroClass β`.
-/

@[expose] public section

namespace AInfinityTheory

universe u v w₁ w₂ w₃ w₄

/-- An index of degree `d` is a pair of degrees `(i, j)` with `i + d = j`: a graded linear map of
degree `d` has one component from degree `i` to degree `j` for each such index. -/
structure GradedLinearMap.Index {β : Type v} [Add β] (d : β) where
  /-- The source degree. -/
  i : β
  /-- The target degree. -/
  j : β
  /-- The target degree is the source degree shifted by `d`. -/
  hij : i + d = j

/-- A graded `R`-linear map of degree `d` from `M` to `N` is a family of `R`-linear maps
`M i →ₗ[R] N j`, one for each pair of degrees with `i + d = j`. It raises the degree of every
homogeneous element by `d`. -/
def GradedLinearMap (R : Type u) [Semiring R] {β : Type v} [Add β]
    (M : β → Type w₁) (N : β → Type w₂)
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)] (d : β) :=
  ∀ T : GradedLinearMap.Index d, M T.i →ₗ[R] N T.j
deriving AddCommMonoid

namespace GradedLinearMap

variable {R : Type u} [Semiring R] {β : Type v}
variable {M : β → Type w₁} {N : β → Type w₂} {P : β → Type w₃} {Q : β → Type w₄}
variable [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
variable [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]
variable [∀ i, AddCommMonoid (P i)] [∀ i, Module R (P i)]
variable [∀ i, AddCommMonoid (Q i)] [∀ i, Module R (Q i)]

section Add

variable [Add β] {d : β}

/-- The graded linear map with component `v i j hij` from degree `i` to degree `j`, for each
pair of degrees with `i + d = j`. -/
def mk (v : ∀ i j, i + d = j → M i →ₗ[R] N j) : GradedLinearMap R M N d :=
  fun ⟨i, j, hij⟩ ↦ v i j hij

/-- The component of a graded linear map from degree `i` to degree `j`, where `i + d = j`. -/
def v (f : GradedLinearMap R M N d) (i j : β) (hij : i + d = j) : M i →ₗ[R] N j :=
  f ⟨i, j, hij⟩

@[simp]
theorem mk_v (v : ∀ i j, i + d = j → M i →ₗ[R] N j) (i j : β) (hij : i + d = j) :
    (mk v).v i j hij = v i j hij :=
  rfl

theorem congr_v {f g : GradedLinearMap R M N d} (h : f = g) (i j : β) (hij : i + d = j) :
    f.v i j hij = g.v i j hij := by
  rw [h]

/-- Two graded linear maps are equal if all their components are. -/
@[ext]
theorem ext {f g : GradedLinearMap R M N d} (h : ∀ i j hij, f.v i j hij = g.v i j hij) :
    f = g := by
  funext ⟨i, j, hij⟩
  exact h i j hij

section AddCommMonoid

/-- Graded linear maps of degree `d` form a module over any semiring `S` acting on the target
compatibly with `R`. -/
instance {S : Type*} [Semiring S] [∀ i, Module S (N i)] [∀ i, SMulCommClass R S (N i)] :
    Module S (GradedLinearMap R M N d) :=
  inferInstanceAs <| Module S (∀ _, _)

@[simp]
theorem zero_v (i j : β) (hij : i + d = j) : (0 : GradedLinearMap R M N d).v i j hij = 0 :=
  rfl

@[simp]
theorem add_v (f g : GradedLinearMap R M N d) (i j : β) (hij : i + d = j) :
    (f + g).v i j hij = f.v i j hij + g.v i j hij :=
  rfl

@[simp]
theorem smul_v {S : Type*} [Semiring S] [∀ i, Module S (N i)]
    [∀ i, SMulCommClass R S (N i)] (c : S) (f : GradedLinearMap R M N d) (i j : β)
    (hij : i + d = j) : (c • f).v i j hij = c • f.v i j hij :=
  rfl

@[simp]
theorem nsmul_v (n : ℕ) (f : GradedLinearMap R M N d) (i j : β) (hij : i + d = j) :
    (n • f).v i j hij = n • f.v i j hij :=
  rfl

end AddCommMonoid

section AddCommGroup

variable {N : β → Type w₂} [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]

/-- Graded linear maps of degree `d` into a family of additive groups form an additive
commutative group. -/
instance : AddCommGroup (GradedLinearMap R M N d) :=
  inferInstanceAs <| AddCommGroup (∀ _, _)

@[simp]
theorem neg_v (f : GradedLinearMap R M N d) (i j : β) (hij : i + d = j) :
    (-f).v i j hij = -f.v i j hij :=
  rfl

@[simp]
theorem sub_v (f g : GradedLinearMap R M N d) (i j : β) (hij : i + d = j) :
    (f - g).v i j hij = f.v i j hij - g.v i j hij :=
  rfl

@[simp]
theorem zsmul_v (n : ℤ) (f : GradedLinearMap R M N d) (i j : β) (hij : i + d = j) :
    (n • f).v i j hij = n • f.v i j hij :=
  rfl

end AddCommGroup

end Add

section Composition

variable [AddSemigroup β] {d e de : β}

/-- The composite of graded linear maps of degrees `d` and `e` is a graded linear map of any
degree `de` with `d + e = de`. Its component from degree `i` factors through degree `i + d`. -/
def comp (g : GradedLinearMap R N P e) (f : GradedLinearMap R M N d) (h : d + e = de) :
    GradedLinearMap R M P de :=
  mk fun i k hik ↦ (g.v (i + d) k (by rw [add_assoc, h, hik])).comp (f.v i (i + d) rfl)

/-- A component of a composite of graded linear maps factors through any middle degree `j`. -/
theorem comp_v (g : GradedLinearMap R N P e) (f : GradedLinearMap R M N d) (h : d + e = de)
    {i j k : β} (hij : i + d = j) (hjk : j + e = k) (hik : i + de = k) :
    (g.comp f h).v i k hik = (g.v j k hjk).comp (f.v i j hij) := by
  subst hij
  rfl

/-- Composition of graded linear maps is associative, for any choice of degrees of the
intermediate composites. -/
theorem comp_assoc {d₁ d₂ d₃ d₁₂ d₂₃ d₁₂₃ : β} (f₁ : GradedLinearMap R M N d₁)
    (f₂ : GradedLinearMap R N P d₂) (f₃ : GradedLinearMap R P Q d₃) (h₁₂ : d₁ + d₂ = d₁₂)
    (h₂₃ : d₂ + d₃ = d₂₃) (h₁₂₃ : d₁₂ + d₃ = d₁₂₃) (h₁₂₃' : d₁ + d₂₃ = d₁₂₃) :
    (f₃.comp f₂ h₂₃).comp f₁ h₁₂₃' = f₃.comp (f₂.comp f₁ h₁₂) h₁₂₃ := by
  ext i l hil x
  exact LinearMap.congr_fun (comp_v f₃ (f₂.comp f₁ h₁₂) h₁₂₃ (j := i + d₁ + d₂)
    (by rw [← h₁₂, add_assoc]) (by rw [← hil, ← h₁₂₃', ← h₂₃]; simp only [add_assoc]) hil).symm x

end Composition

section Identity

variable [AddZeroClass β]

/-- The identity graded linear map, of degree `0`. Its component from degree `i` to degree `j`
is the identity, transported along `i = i + 0 = j`. -/
def id : GradedLinearMap R M M 0 :=
  mk fun i j h ↦ by obtain rfl : i = j := (add_zero i).symm.trans h; exact LinearMap.id

@[simp]
theorem id_v (i : β) (h : i + 0 = i := add_zero i) :
    (id : GradedLinearMap R M M 0).v i i h = LinearMap.id :=
  rfl

end Identity

section Monoid

variable [AddMonoid β] {d : β}

@[simp]
theorem id_comp (f : GradedLinearMap R M N d) :
    (id : GradedLinearMap R N N 0).comp f (add_zero d) = f := by
  ext i k hik x
  rw [comp_v _ _ _ hik (add_zero k) hik, id_v, LinearMap.id_comp]

@[simp]
theorem comp_id (f : GradedLinearMap R M N d) :
    f.comp (id : GradedLinearMap R M M 0) (zero_add d) = f := by
  ext i k hik x
  rw [comp_v _ _ _ (add_zero i) hik hik, id_v, LinearMap.comp_id]

end Monoid

end GradedLinearMap

/-- An index of degree `d` for a graded multilinear map with inputs indexed by `ι` consists of
input degrees `deg : ι → β` and an output degree `j` with `(∑ k, deg k) + d = j`: a graded
multilinear map of degree `d` has one component for each such index. -/
structure GradedMultilinearMap.Index (ι : Type*) [Fintype ι] {β : Type v} [AddCommMonoid β]
    (d : β) where
  /-- The input degrees. -/
  deg : ι → β
  /-- The output degree. -/
  j : β
  /-- The output degree is the total input degree shifted by `d`. -/
  hdeg : (∑ k, deg k) + d = j

/-- A graded `R`-multilinear map of degree `d` from the families `M k` (for `k : ι`) to `N`
consists of, for each choice of input degrees `deg : ι → β` and each output degree `j` with
`(∑ k, deg k) + d = j`, an `R`-multilinear map from `∀ k, M k (deg k)` to `N j`. The output
degree is the total input degree shifted by `d`. -/
def GradedMultilinearMap (R : Type u) [Semiring R] {ι : Type*} [Fintype ι]
    {β : Type v} [AddCommMonoid β] (M : ι → β → Type w₁) (N : β → Type w₂)
    [∀ k i, AddCommMonoid (M k i)] [∀ k i, Module R (M k i)]
    [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)] (d : β) :=
  ∀ T : GradedMultilinearMap.Index ι d, MultilinearMap R (fun k ↦ M k (T.deg k)) (N T.j)
deriving AddCommMonoid

namespace GradedMultilinearMap

variable {R : Type u} [Semiring R] {ι : Type*} [Fintype ι] {β : Type v} [AddCommMonoid β]
variable {M : ι → β → Type w₁} {N : β → Type w₂}
variable [∀ k i, AddCommMonoid (M k i)] [∀ k i, Module R (M k i)]
variable [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)] {d : β}

/-- The graded multilinear map with component `v deg j hdeg` for input degrees `deg` and output
degree `j`, for each such choice with `(∑ k, deg k) + d = j`. -/
def mk (v : ∀ (deg : ι → β) (j : β), (∑ k, deg k) + d = j →
    MultilinearMap R (fun k ↦ M k (deg k)) (N j)) : GradedMultilinearMap R M N d :=
  fun ⟨deg, j, hdeg⟩ ↦ v deg j hdeg

/-- The component of a graded multilinear map with input degrees `deg` and output degree `j`,
where `(∑ k, deg k) + d = j`. -/
def v (f : GradedMultilinearMap R M N d) (deg : ι → β) (j : β) (hdeg : (∑ k, deg k) + d = j) :
    MultilinearMap R (fun k ↦ M k (deg k)) (N j) :=
  f ⟨deg, j, hdeg⟩

@[simp]
theorem mk_v (v : ∀ (deg : ι → β) (j : β), (∑ k, deg k) + d = j →
    MultilinearMap R (fun k ↦ M k (deg k)) (N j)) (deg : ι → β) (j : β)
    (hdeg : (∑ k, deg k) + d = j) : (mk v).v deg j hdeg = v deg j hdeg :=
  rfl

theorem congr_v {f g : GradedMultilinearMap R M N d} (h : f = g) (deg : ι → β) (j : β)
    (hdeg : (∑ k, deg k) + d = j) : f.v deg j hdeg = g.v deg j hdeg := by
  rw [h]

/-- Two graded multilinear maps are equal if all their components are. -/
@[ext]
theorem ext {f g : GradedMultilinearMap R M N d}
    (h : ∀ deg j hdeg, f.v deg j hdeg = g.v deg j hdeg) : f = g := by
  funext ⟨deg, j, hdeg⟩
  exact h deg j hdeg

section AddCommMonoid

/-- Graded multilinear maps of degree `d` form a module over any semiring `S` acting on the
target compatibly with `R`. -/
instance {S : Type*} [Semiring S] [∀ i, Module S (N i)] [∀ i, SMulCommClass R S (N i)] :
    Module S (GradedMultilinearMap R M N d) :=
  inferInstanceAs <| Module S (∀ _, _)

@[simp]
theorem zero_v (deg : ι → β) (j : β) (hdeg : (∑ k, deg k) + d = j) :
    (0 : GradedMultilinearMap R M N d).v deg j hdeg = 0 :=
  rfl

@[simp]
theorem add_v (f g : GradedMultilinearMap R M N d) (deg : ι → β) (j : β)
    (hdeg : (∑ k, deg k) + d = j) : (f + g).v deg j hdeg = f.v deg j hdeg + g.v deg j hdeg :=
  rfl

@[simp]
theorem smul_v {S : Type*} [Semiring S] [∀ i, Module S (N i)] [∀ i, SMulCommClass R S (N i)]
    (c : S) (f : GradedMultilinearMap R M N d) (deg : ι → β) (j : β)
    (hdeg : (∑ k, deg k) + d = j) : (c • f).v deg j hdeg = c • f.v deg j hdeg :=
  rfl

@[simp]
theorem nsmul_v (n : ℕ) (f : GradedMultilinearMap R M N d) (deg : ι → β) (j : β)
    (hdeg : (∑ k, deg k) + d = j) : (n • f).v deg j hdeg = n • f.v deg j hdeg :=
  rfl

end AddCommMonoid

section AddCommGroup

variable {N : β → Type w₂} [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]

/-- Graded multilinear maps of degree `d` into a family of additive groups form an additive
commutative group. -/
instance : AddCommGroup (GradedMultilinearMap R M N d) :=
  inferInstanceAs <| AddCommGroup (∀ _, _)

@[simp]
theorem neg_v (f : GradedMultilinearMap R M N d) (deg : ι → β) (j : β)
    (hdeg : (∑ k, deg k) + d = j) : (-f).v deg j hdeg = -f.v deg j hdeg :=
  rfl

@[simp]
theorem sub_v (f g : GradedMultilinearMap R M N d) (deg : ι → β) (j : β)
    (hdeg : (∑ k, deg k) + d = j) : (f - g).v deg j hdeg = f.v deg j hdeg - g.v deg j hdeg :=
  rfl

@[simp]
theorem zsmul_v (n : ℤ) (f : GradedMultilinearMap R M N d) (deg : ι → β) (j : β)
    (hdeg : (∑ k, deg k) + d = j) : (n • f).v deg j hdeg = n • f.v deg j hdeg :=
  rfl

end AddCommGroup

end GradedMultilinearMap

end AInfinityTheory
