/-
Copyright (c) 2026 Annie Yao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Annie Yao, Marco David, Jason Dong, Zhan Shi
-/
module

public import AInfinity.AInfinityCategory
public import Mathlib.Combinatorics.Enumerative.Composition

/-! # A∞-functors

An A∞-functor F between A∞-categories consists of a map on objects together with, for each
n ≥ 1, a multilinear map φₙ : Hom(X₀, X₁) ⊗ ⋯ ⊗ Hom(Xₙ₋₁, Xₙ) → Hom(F X₀, F Xₙ) of degree
1 - n, satisfying the A∞-functor equations
$$\sum_{r + s + t = n,\ s \ge 1} (-1)^{\|a_{r+s+1}\| + \dots + \|a_n\|}
  \varphi_{r+1+t}(a_1, \dots, a_r, m_s(a_{r+1}, \dots, a_{r+s}), a_{r+s+1}, \dots, a_n)
= \sum_{k \ge 1} \sum_{i_1 + \dots + i_k = n}
  m'_k(\varphi_{i_1}(a_1, \dots, a_{i_1}), \dots, \varphi_{i_k}(a_{n-i_k+1}, \dots, a_n)),$$
where m and m' are the higher compositions of the source and the target.

The sign on the left is the Koszul sign `stasheffSign` of the Stasheff identities. There is no
sign on the right: in reduced degrees ‖a‖ = |a| - 1 every φᵢ has degree 0, so no Koszul
sign arises from moving it past the inputs (compare equation (1.6) in Seidel's book, see the
references below).

The source and target may be graded by different gradings `β` and `β'`; the functor then
carries a homomorphism of gradings `β →+ᵍ β'`, which preserves the degree one
and the Koszul signs.

## Main definitions

* `AInfinityTheory.AInfinityFunctorData β β' R Obj Obj'`: a map on objects, a grading
  homomorphism and functor components φₙ, not yet subject to any relations.
* `AInfinityTheory.AInfinityFunctorData.mapCompSum`: the left-hand side of the arity-n
  functor equation.
* `AInfinityTheory.AInfinityFunctorData.compMapSum`: the right-hand side of the arity-n
  functor equation.
* `AInfinityTheory.AInfinityFunctor β β' R Obj Obj'`: an A∞-functor between
  A∞-categories.

## Implementation notes

A `GradedMultilinearMap` has a single type of degrees for its inputs, its output and its degree.
The inputs of φₙ are graded by `β` and its output by `β'`, so the output family is
read through `degMap`: for input degrees `deg`, the component of φₙ lands in
Hom(F X₀, F Xₙ) in degree `degMap (functorTargetDeg deg)`. All degree arithmetic
happens in `β`, and φₙ is only ever evaluated in target degrees of the form
`degMap b`.

Both sides of the functor equation are stated pointwise on composable inputs
a₁, …, aₙ of degrees `deg`, in degree `degMap d` for any `d` equal to the degree
`operationTargetDeg deg` of mₙ(a₁, …, aₙ), as for `stasheffSum`. The left-hand side is
a `signedStasheffSum`, like the Stasheff sum. The decompositions i₁ + ⋯ + iₖ = n on the
right-hand side are Mathlib's `Composition n`. Changes of objects are transported with `homCongr`.

`mapCompSum` and `compMapSum` are named in order of application: a functor component applied
to a composition, and a composition of functor components.

## References

* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, Zurich Lectures in Advanced
  Mathematics, European Mathematical Society, 2008.
-/

@[expose] public section

noncomputable section

namespace AInfinityTheory

open GradedLinearQuiver

variable {n : ℕ}

section Degrees

variable {β : Type*} [AddCommGroup β] [Grading β]
variable (deg : Fin n → β)

/-- The degree of φₙ(a₁, …, aₙ) for inputs aᵢ of degrees `deg i`, where
φₙ itself has degree 1 - n. -/
abbrev functorTargetDeg : β :=
  (∑ i, deg i) + (1 - n : ℤ) • degOne

lemma operationTargetDeg_eq_functorTargetDeg_add_degOne :
    operationTargetDeg deg = functorTargetDeg deg + degOne := by
  module

/-- The term of the left-hand side of the functor equation indexed by p = (r, s, t), in which
the functor component of arity r + 1 + t is applied to the inner output and the remaining
inputs, has the degree of mₙ(a₁, …, aₙ). -/
lemma functorTargetDeg_stasheffDegOut (p : StasheffIndex n) :
    functorTargetDeg (stasheffDegOut deg p) = operationTargetDeg deg := by
  apply add_right_cancel (b := (degOne : β))
  rw [← operationTargetDeg_eq_functorTargetDeg_add_degOne, stasheffDegOut_sum,
    stasheffTargetDeg_eq_operationTargetDeg_add_degOne]

/-- The term of the right-hand side of the functor equation indexed by a composition
c = (i₁, …, iₖ) of `n`, in which m'ₖ is applied to the values of the functor components on the
k blocks of c, has the degree of mₙ(a₁, …, aₙ). -/
lemma operationTargetDeg_functorTargetDeg_embedding (c : Composition n) :
    operationTargetDeg (fun l ↦ functorTargetDeg fun j ↦ deg (c.embedding l j)) =
      operationTargetDeg deg := by
  simp only [operationTargetDeg, functorTargetDeg, Finset.sum_add_distrib,
    c.sum_sum_apply_embedding, add_assoc, ← GradingHom.ofInt_apply, ← map_sum, ← map_add,
    Finset.sum_sub_distrib, ← Nat.cast_sum]
  simp

end Degrees

section CompositionBlock

/-! ### Blocks of a composition

A composition c = (i₁, …, iₖ) of `n` cuts a composable string of `n` inputs into k
blocks: the `l`-th block has size iₗ, which is `c.blocksFun l`, and starts at
position `c.sizeUpTo l`. In the right-hand side of the functor equation, the functor component
of arity iₗ is applied to the `l`-th block and the outer operation m'ₖ to the resulting k
values, so both the sizes of the blocks and their number must be positive. The lemmas and
instances on `Composition` below are stated without reference to functors. -/

variable {Obj : Type*} (X : Fin (n + 1) → Obj) (c : Composition n) (l : Fin c.length)

lemma _root_.Composition.sizeUpTo_add_blocksFun_le : c.sizeUpTo l + c.blocksFun l ≤ n :=
  (c.sizeUpTo_succ' l).symm.trans_le (c.sizeUpTo_le _)

/-- Every block of a composition is nonempty. -/
instance _root_.Composition.neZero_blocksFun : NeZero (c.blocksFun l) :=
  NeZero.of_pos (c.one_le_blocksFun l)

/-- A composition of a positive integer has at least one block. -/
instance _root_.Composition.neZero_length [NeZero n] : NeZero c.length :=
  NeZero.of_pos (c.length_pos_of_pos (NeZero.pos n))

/-- The object string of the `l`-th block of a composition `c` of `n`: its `i`-th object is
`X (c.sizeUpTo l + i)`, for `i ≤ c.blocksFun l`. -/
def compositionBlockObj : Fin (c.blocksFun l + 1) → Obj :=
  fun i ↦ X ((i.natAdd (c.sizeUpTo l)).castLE (Nat.succ_le_succ (c.sizeUpTo_add_blocksFun_le l)))

@[simp]
lemma compositionBlockObj_zero :
    compositionBlockObj X c l 0 = X (c.boundary l.castSucc) := by
  unfold compositionBlockObj
  congr 1

@[simp]
lemma compositionBlockObj_last :
    compositionBlockObj X c l (Fin.last (c.blocksFun l)) = X (c.boundary l.succ) := by
  unfold compositionBlockObj Composition.boundary
  congr 1
  ext
  simp [Composition.sizeUpTo_succ']

end CompositionBlock

/-- The data of an A∞-functor between graded `R`-linear quivers: a map on objects, a
homomorphism of gradings and, for each n ≥ 1, a functor component φₙ of degree
1 - n.
No relations are imposed. -/
structure AInfinityFunctorData (β β' : Type*) [AddCommGroup β] [Grading β]
    [AddCommGroup β'] [Grading β'] (R : Type*) [Semiring R] (Obj Obj' : Type*)
    [GradedLinearQuiver β R Obj] [GradedLinearQuiver β' R Obj'] where
  /-- The action of the functor on objects. -/
  obj : Obj → Obj'
  /-- The homomorphism of gradings translating source degrees into target degrees. -/
  degMap : β →+ᵍ β'
  /-- The action of the functor on hom spaces, i.e. the functor components φₙ, of
  degree 1 - n, landing in the hom spaces of the target in the translated degrees. -/
  map {n : ℕ} [NeZero n] (X : Fin (n + 1) → Obj) :
    GradedMultilinearMap R (ComposableHom β R X)
      (fun b : β ↦ (obj (X 0) →ᵍ[R] obj (X (Fin.last n))) (degMap b))
      ((1 - n : ℤ) • degOne)

namespace AInfinityFunctorData

variable {β β' : Type*} [AddCommGroup β] [Grading β] [AddCommGroup β']
  [Grading β'] {R : Type*} [Semiring R] {Obj Obj' : Type*}

section GradedLinearQuiver

variable [GradedLinearQuiver β R Obj] [GradedLinearQuiver β' R Obj']
variable (F : AInfinityFunctorData β β' R Obj Obj')
variable {X : Fin (n + 1) → Obj} {deg : Fin n → β}
variable (a : ∀ i : Fin n, ComposableHom β R X i (deg i))

lemma operationTargetDeg_degMap {k : ℕ} (b : Fin k → β) :
    operationTargetDeg (fun i ↦ F.degMap (b i)) = F.degMap (operationTargetDeg b) := by
  simp only [operationTargetDeg, map_add, map_sum, map_zsmul, GradingHom.map_degOne]

/-- `operationTargetDeg_functorTargetDeg_embedding` translated along `degMap`: the term
of the right-hand side of the functor equation indexed by a composition of `n` has degree
`degMap d`, where `d` is the degree of mₙ(a₁, …, aₙ). -/
lemma operationTargetDeg_degMap_functorTargetDeg_embedding (c : Composition n) (d : β)
    (hd : operationTargetDeg deg = d) :
    operationTargetDeg (fun l ↦ F.degMap (functorTargetDeg fun j ↦ deg (c.embedding l j))) =
      F.degMap d :=
  (F.operationTargetDeg_degMap _).trans
    (congrArg F.degMap ((operationTargetDeg_functorTargetDeg_embedding deg c).trans hd))

/-- The value of the functor component of arity iₗ on the `l`-th block of a composition
c = (i₁, …, iₖ) of `n`, as the `l`-th input of the outer operation m'ₖ. -/
def compositionBlockMap (c : Composition n) (l : Fin c.length) :
    ComposableHom β' R (fun k ↦ F.obj (X (c.boundary k))) l
      (F.degMap (functorTargetDeg fun j ↦ deg (c.embedding l j))) :=
  homCongr R (congrArg F.obj (compositionBlockObj_zero X c l))
    (congrArg F.obj (compositionBlockObj_last X c l)) rfl
    ((F.map (compositionBlockObj X c l)).v (fun j ↦ deg (c.embedding l j)) _ rfl
      fun j ↦ a (c.embedding l j))

end GradedLinearQuiver

section AInfinityCategoryStruct

variable [AInfinityCategoryStruct β R Obj] [AInfinityCategoryStruct β' R Obj']
variable (F : AInfinityFunctorData β β' R Obj Obj')
variable {X : Fin (n + 1) → Obj} {deg : Fin n → β}
variable (a : ∀ i : Fin n, ComposableHom β R X i (deg i))

/-! ### The left-hand side of the functor equation -/

/-- The term of the left-hand side of the functor equation indexed by p = (r, s, t): the
functor component of arity r + 1 + t applied to the first r inputs, the inner output
mₛ(…) and the last t inputs, in degree `F.degMap d` for any `d` equal to the degree of
mₙ(a₁, …, aₙ). -/
def mapCompTerm (p : StasheffIndex n) (d : β) (hd : operationTargetDeg deg = d) :
    (F.obj (X 0) →ᵍ[R] F.obj (X (Fin.last n))) (F.degMap d) :=
  homCongr R (congrArg F.obj (stasheffObjOut_zero X p))
    (congrArg F.obj (stasheffObjOut_last X p)) rfl
    ((F.map (stasheffObjOut X p)).v (stasheffDegOut deg p) d
      ((functorTargetDeg_stasheffDegOut deg p).trans hd) (stasheffInputsOut a p))

/-- The left-hand side of the arity-n functor equation, with the Koszul signs of the Stasheff
identities, in degree `F.degMap d` for any `d` equal to the degree of mₙ(a₁, …, aₙ). -/
def mapCompSum (d : β) (hd : operationTargetDeg deg = d) :
    (F.obj (X 0) →ᵍ[R] F.obj (X (Fin.last n))) (F.degMap d) :=
  signedStasheffSum deg fun p ↦ F.mapCompTerm a p d hd

/-! ### The right-hand side of the functor equation -/

/-- The term of the right-hand side of the functor equation indexed by a composition
c = (i₁, …, iₖ) of `n`: the operation m'ₖ of the target applied to the values of the functor
components on the k blocks of c, in degree `F.degMap d` for any `d` equal to the degree of
mₙ(a₁, …, aₙ). -/
def compMapTerm [NeZero n] (c : Composition n) (d : β) (hd : operationTargetDeg deg = d) :
    (F.obj (X 0) →ᵍ[R] F.obj (X (Fin.last n))) (F.degMap d) :=
  homCongr R (congrArg (fun k ↦ F.obj (X k)) c.boundary_zero)
    (congrArg (fun k ↦ F.obj (X k)) c.boundary_last) rfl
    ((AInfinityCategoryStruct.m (fun k ↦ F.obj (X (c.boundary k)))).v
      (fun l ↦ F.degMap (functorTargetDeg fun j ↦ deg (c.embedding l j))) (F.degMap d)
      (F.operationTargetDeg_degMap_functorTargetDeg_embedding c d hd)
      (F.compositionBlockMap a c))

/-- The right-hand side of the arity-n functor equation, summed over all compositions of
`n`, in degree `F.degMap d` for any `d` equal to the degree of mₙ(a₁, …, aₙ). -/
def compMapSum [NeZero n] (d : β) (hd : operationTargetDeg deg = d) :
    (F.obj (X 0) →ᵍ[R] F.obj (X (Fin.last n))) (F.degMap d) :=
  ∑ c : Composition n, F.compMapTerm a c d hd

/-! ### Vanishing terms -/

/-- A term of the left-hand side of the functor equation vanishes if its outer functor component
vanishes. -/
lemma mapCompTerm_eq_zero_of_map_eq_zero (p : StasheffIndex n)
    (hF : F.map (stasheffObjOut X p) = 0) (d : β) (hd : operationTargetDeg deg = d) :
    F.mapCompTerm a p d hd = 0 := by
  rw [mapCompTerm, hF, GradedMultilinearMap.zero_v, zero_apply, map_zero]

/-- A term of the left-hand side of the functor equation vanishes if its inner operation
vanishes. -/
lemma mapCompTerm_eq_zero_of_inner_map_eq_zero (p : StasheffIndex n)
    (hm : ∀ e he,
      (AInfinityCategoryStruct.m (R := R) (stasheffObjIn X p)).v (stasheffDegIn deg p) e he = 0)
    (d : β) (hd : operationTargetDeg deg = d) :
    F.mapCompTerm a p d hd = 0 := by
  rw [mapCompTerm, MultilinearMap.map_coord_zero _ p.middleIndex
    (stasheffInputsOut_middle_eq_zero_of_inner_eq_zero a p
      (stasheffInner_eq_zero_of_map_eq_zero a p hm)), map_zero]

/-- A term of the right-hand side of the functor equation vanishes if its outer operation
vanishes. -/
lemma compMapTerm_eq_zero_of_map_eq_zero [NeZero n] (c : Composition n)
    (hm : AInfinityCategoryStruct.m (β := β') (R := R) (fun k ↦ F.obj (X (c.boundary k))) = 0)
    (d : β)
    (hd : operationTargetDeg deg = d) :
    F.compMapTerm a c d hd = 0 := by
  rw [compMapTerm, hm, GradedMultilinearMap.zero_v, zero_apply, map_zero]

/-- A term of the right-hand side of the functor equation vanishes if the functor component on
one of its blocks vanishes. -/
lemma compMapTerm_eq_zero_of_block_map_eq_zero [NeZero n] (c : Composition n) (l : Fin c.length)
    (hF : F.map (compositionBlockObj X c l) = 0) (d : β) (hd : operationTargetDeg deg = d) :
    F.compMapTerm a c d hd = 0 := by
  have hl : F.compositionBlockMap a c l = 0 := by
    rw [compositionBlockMap, hF, GradedMultilinearMap.zero_v]
    exact map_zero _
  rw [compMapTerm, MultilinearMap.map_coord_zero _ l hl, map_zero]

/-- If the operations of the source vanish in every arity outside `S` and the functor components
in every arity outside `T`, a term of the left-hand side of the functor equation vanishes unless
its inner arity lies in `S` and its outer arity lies in `T`. -/
lemma mapCompTerm_eq_zero_of_arity_notMem (S T : Set ℕ)
    (hm : ∀ (k : ℕ) [NeZero k], k ∉ S → ∀ X : Fin (k + 1) → Obj,
      AInfinityCategoryStruct.m (β := β) (R := R) X = 0)
    (hF : ∀ (k : ℕ) [NeZero k], k ∉ T → ∀ X : Fin (k + 1) → Obj, F.map X = 0)
    (p : StasheffIndex n) (hST : p.s ∉ S ∨ p.r + 1 + p.t ∉ T) (d : β)
    (hd : operationTargetDeg deg = d) :
    F.mapCompTerm a p d hd = 0 := by
  rcases hST with hS | hT
  · exact F.mapCompTerm_eq_zero_of_inner_map_eq_zero a p
      (fun e he ↦ by simp only [hm p.s hS]; rfl) d hd
  · exact F.mapCompTerm_eq_zero_of_map_eq_zero a p (hF _ hT _) d hd

/-- If the operations of the target vanish in every arity outside `S` and the functor components
in every arity outside `T`, a term of the right-hand side of the functor equation vanishes unless
its number of blocks lies in `S` and the sizes of all its blocks lie in `T`. -/
lemma compMapTerm_eq_zero_of_arity_notMem [NeZero n] (S T : Set ℕ)
    (hm : ∀ (k : ℕ) [NeZero k], k ∉ S → ∀ Y : Fin (k + 1) → Obj',
      AInfinityCategoryStruct.m (β := β') (R := R) Y = 0)
    (hF : ∀ (k : ℕ) [NeZero k], k ∉ T → ∀ X : Fin (k + 1) → Obj, F.map X = 0)
    (c : Composition n) (hST : c.length ∉ S ∨ ∃ l, c.blocksFun l ∉ T) (d : β)
    (hd : operationTargetDeg deg = d) :
    F.compMapTerm a c d hd = 0 := by
  rcases hST with hS | ⟨l, hT⟩
  · exact F.compMapTerm_eq_zero_of_map_eq_zero a c (hm _ hS _) d hd
  · exact F.compMapTerm_eq_zero_of_block_map_eq_zero a c l (hF _ hT _) d hd

/-! ### The functor equation in low arities -/

/-- In arity 1, the left-hand side of the functor equation is the single term φ₁(m₁(a₁)). -/
lemma mapCompSum_arity_one {X : Fin (1 + 1) → Obj} {deg : Fin 1 → β}
    (a : ∀ i : Fin 1, ComposableHom β R X i (deg i)) (d : β) (hd : operationTargetDeg deg = d) :
    F.mapCompSum a d hd = F.mapCompTerm a ⟨0, 1, 0, rfl, le_rfl⟩ d hd := by
  rw [mapCompSum, signedStasheffSum, StasheffIndex.univ_one, Finset.sum_singleton]
  exact one_smul _ _

/-- In arity 2, the left-hand side of the functor equation has the three terms
φ₂(m₁(a₁), a₂), φ₂(a₁, m₁(a₂)) and φ₁(m₂(a₁, a₂)), with the Koszul sign (-1)^‖a₂‖ on the
first. -/
lemma mapCompSum_arity_two {X : Fin (2 + 1) → Obj} {deg : Fin 2 → β}
    (a : ∀ i : Fin 2, ComposableHom β R X i (deg i)) (d : β) (hd : operationTargetDeg deg = d) :
    F.mapCompSum a d hd =
      (sign (deg 1 - degOne)).toMul • F.mapCompTerm a ⟨0, 1, 1, rfl, le_rfl⟩ d hd +
        F.mapCompTerm a ⟨1, 1, 0, rfl, le_rfl⟩ d hd +
        F.mapCompTerm a ⟨0, 2, 0, rfl, one_le_two⟩ d hd := by
  rw [mapCompSum, signedStasheffSum, StasheffIndex.univ_two, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [stasheffSign, Fin.prod_univ_one, Fin.prod_univ_zero, one_smul, add_assoc]
  rfl

/-- In arity 3, the left-hand side of the functor equation has six terms, one for each index
triple (r, s, t), with the Koszul signs given by `stasheffSign`. -/
lemma mapCompSum_arity_three {X : Fin (3 + 1) → Obj} {deg : Fin 3 → β}
    (a : ∀ i : Fin 3, ComposableHom β R X i (deg i)) (d : β) (hd : operationTargetDeg deg = d) :
    F.mapCompSum a d hd =
      ((sign (deg 1 - degOne)).toMul * (sign (deg 2 - degOne)).toMul) •
          F.mapCompTerm a ⟨0, 1, 2, rfl, le_rfl⟩ d hd +
        (sign (deg 2 - degOne)).toMul • F.mapCompTerm a ⟨1, 1, 1, rfl, le_rfl⟩ d hd +
        F.mapCompTerm a ⟨2, 1, 0, rfl, le_rfl⟩ d hd +
        (sign (deg 2 - degOne)).toMul • F.mapCompTerm a ⟨0, 2, 1, rfl, one_le_two⟩ d hd +
        F.mapCompTerm a ⟨1, 2, 0, rfl, one_le_two⟩ d hd +
        F.mapCompTerm a ⟨0, 3, 0, rfl, by decide⟩ d hd := by
  rw [mapCompSum, signedStasheffSum, StasheffIndex.univ_three]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp only [stasheffSign, Fin.prod_univ_two, Fin.prod_univ_one, Fin.prod_univ_zero,
    one_smul, add_assoc]
  rfl

/-- In arity 1, the right-hand side of the functor equation is the single term m'₁(φ₁(a₁)),
indexed by the only composition of 1. -/
lemma compMapSum_arity_one {X : Fin (1 + 1) → Obj} {deg : Fin 1 → β}
    (a : ∀ i : Fin 1, ComposableHom β R X i (deg i)) (d : β) (hd : operationTargetDeg deg = d) :
    F.compMapSum a d hd = F.compMapTerm a (Composition.ones 1) d hd :=
  Fintype.sum_eq_single _ fun c hc ↦ absurd (Composition.eq_ones_iff_length.2
    (le_antisymm c.length_le (c.length_pos_of_pos one_pos))) hc

/-- In arity 2, the right-hand side of the functor equation has the two terms
m'₂(φ₁(a₁), φ₁(a₂)) and m'₁(φ₂(a₁, a₂)), indexed by the two compositions of 2. -/
lemma compMapSum_arity_two {X : Fin (2 + 1) → Obj} {deg : Fin 2 → β}
    (a : ∀ i : Fin 2, ComposableHom β R X i (deg i)) (d : β) (hd : operationTargetDeg deg = d) :
    F.compMapSum a d hd =
      F.compMapTerm a (Composition.ones 2) d hd +
        F.compMapTerm a (Composition.single 2 two_pos) d hd := by
  refine Fintype.sum_eq_add _ _ (by decide) fun c ⟨h₁, h₂⟩ ↦ absurd ?_ h₂
  refine (Composition.eq_single_iff_length two_pos).2 ?_
  have := c.length_pos_of_pos two_pos
  have := c.length_le
  have : c.length ≠ 2 := fun h ↦ h₁ (Composition.eq_ones_iff_length.2 h)
  omega

end AInfinityCategoryStruct

end AInfinityFunctorData

/-- An A∞-functor between A∞-categories: A∞-functor data satisfying the
functor equations. -/
structure AInfinityFunctor (β β' : Type*) [AddCommGroup β] [Grading β]
    [AddCommGroup β'] [Grading β'] (R : Type*) [Semiring R] (Obj Obj' : Type*)
    [AInfinityCategory β R Obj] [AInfinityCategory β' R Obj']
    extends AInfinityFunctorData β β' R Obj Obj' where
  /-- The functor components satisfy the functor equations: in every arity `n ≥ 1`, the
  left-hand side and the right-hand side of the functor equation agree on every composable
  string of inputs. -/
  mapCompSum_eq_compMapSum {n : ℕ} [NeZero n] {X : Fin (n + 1) → Obj} {deg : Fin n → β}
    (a : ∀ i : Fin n, ComposableHom β R X i (deg i)) {d : β}
    (hd : operationTargetDeg deg = d) :
    toAInfinityFunctorData.mapCompSum a d hd =
      toAInfinityFunctorData.compMapSum a d hd

end AInfinityTheory
