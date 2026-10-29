/-
Copyright (c) 2026 Annie Yao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Annie Yao, Marco David, Jason Dong, Zhan Shi
-/
module

public import AInfinity.AInfinityCategory
public import Mathlib.Combinatorics.Enumerative.Composition

/-! # A∞-functors

An `A∞`-functor `F : A → B` between `A∞`-categories consists of a map on objects together with,
for each `n ≥ 1`, a multilinear map
`φₙ : Hom(X₀, X₁) ⊗ ⋯ ⊗ Hom(Xₙ₋₁, Xₙ) → Hom(F X₀, F Xₙ)` of degree `1 - n`, satisfying the
`A∞`-functor equations
`∑_{r + s + t = n, s ≥ 1} (-1)^(‖a_{r+s+1}‖ + ⋯ + ‖aₙ‖)
  φ_{r+1+t}(a₁, …, aᵣ, mₛ(a_{r+1}, …, a_{r+s}), a_{r+s+1}, …, aₙ)
= ∑_{k ≥ 1} ∑_{i₁ + ⋯ + iₖ = n} m'ₖ(φ_{i₁}(a₁, …, a_{i₁}), …, φ_{iₖ}(a_{n-iₖ+1}, …, aₙ))`.

The sign on the left is the Koszul sign `stasheffSign` of the Stasheff identities. There is no
sign on the right: in reduced degrees `‖a‖ = |a| - 1` every `φᵢ` has degree `0`, so no Koszul
sign arises from moving it past the inputs (compare [Seidel, *Fukaya categories and
Picard–Lefschetz theory*, (1.6)]).

The source and target may be graded by different grading types `β` and `β'`; the functor then
carries a homomorphism of grading types `β →+ᵍ β'`, which preserves the integer shifts
and the Koszul signs.

## Main definitions

* `AInfinityTheory.AInfinityFunctorData β β' R Obj Obj'`: a map on objects, a grading
  homomorphism and functor components `φₙ`, not yet subject to any relations.
* `AInfinityTheory.AInfinityFunctorData.mapCompSum`: the left-hand side of the arity-`n`
  functor equation.
* `AInfinityTheory.AInfinityFunctorData.compMapSum`: the right-hand side of the arity-`n`
  functor equation.
* `AInfinityTheory.AInfinityFunctorData.SatisfiesFunctorEquations`: the functor equations in
  every arity.
* `AInfinityTheory.AInfinityFunctor β β' R Obj Obj'`: an `A∞`-functor between
  `A∞`-categories.

## Implementation notes

A `GradedMultilinearMap` has a single grading type for its inputs, its output and its degree.
The inputs of `φₙ` are graded by `β` and its output by `β'`, so the output family is read
through `degMap`: for input degrees `deg`, the component of `φₙ` lands in `Hom(F X₀, F Xₙ)` in
degree `degMap (∑ deg + shift (1 - n))`. All degree arithmetic happens in `β`, and `φₙ` is only
ever evaluated in target degrees of the form `degMap b`.

Both sides of the functor equation are stated pointwise on composable inputs `a₁, …, aₙ` of
degrees `deg`, in degree `degMap d` for any `d` equal to the degree `operationTargetDeg deg` of
`mₙ(a₁, …, aₙ)`, as for `indexedStasheffSum`. The left-hand side is a `signedStasheffSum`, like
the Stasheff sum. The decompositions `i₁ + ⋯ + iₖ = n` on the right-hand side are Mathlib's
`Composition n`. Changes of objects are transported with `homCongr`.

`mapCompSum` and `compMapSum` are named in order of application: a functor component applied
to a composition, and a composition of functor components.
-/

@[expose] public section

noncomputable section

namespace AInfinityTheory

open GradedLinearQuiver

variable {n : ℕ}

/-- Taking the product over each block of a composition `c` of `n`, and then over the blocks, is
the same as taking the product over `Fin n`. -/
@[to_additive /-- Summing over each block of a composition `c` of `n`, and then over the blocks,
is the same as summing over `Fin n`. -/]
lemma _root_.Composition.prod_prod_embedding {M : Type*} [CommMonoid M] (c : Composition n)
    (f : Fin n → M) : ∏ l, ∏ j, f (c.embedding l j) = ∏ i, f i :=
  (Fintype.prod_sigma _).symm.trans (c.blocksFinEquiv.prod_comp f)

section Degrees

variable {β : Type*} [AddCommGroup β] [Grading β]
variable (deg : Fin n → β)

/-- The degree of `φₙ(a₁, …, aₙ)` for inputs `aᵢ` of degrees `deg i`, where `φₙ` itself has
degree `1 - n`. -/
abbrev functorTargetDeg : β :=
  (∑ i, deg i) + shift (1 - (n : ℤ))

/-- The `n`-ary operation `mₙ` has degree one more than the `n`-ary functor component `φₙ`. -/
lemma operationTargetDeg_eq_functorTargetDeg_add_shift_one :
    operationTargetDeg deg = functorTargetDeg deg + shift 1 := by
  rw [operationTargetDeg, functorTargetDeg, add_assoc, ← map_add]
  congr 2
  lia

/-- The term `φ_{r+1+t}(a₁, …, aᵣ, mₛ(a_{r+1}, …, a_{r+s}), a_{r+s+1}, …, aₙ)` of the left-hand
side of the functor equation, indexed by `p = (r, s, t)`, has the degree of `mₙ(a₁, …, aₙ)`. -/
lemma functorTargetDeg_stasheffDegOut (p : StasheffIndex n) :
    functorTargetDeg (stasheffDegOut deg p) = operationTargetDeg deg := by
  apply add_right_cancel (b := (shift 1 : β))
  rw [← operationTargetDeg_eq_functorTargetDeg_add_shift_one, stasheffDegOut_sum,
    stasheffTargetDeg_eq_operationTargetDeg_add_shift_one]

/-- The term `mₖ(φ_{i₁}(a₁, …, a_{i₁}), …, φ_{iₖ}(a_{n-iₖ+1}, …, aₙ))` of the right-hand side of
the functor equation, indexed by a composition `c = (i₁, …, iₖ)` of `n`, has the degree of
`mₙ(a₁, …, aₙ)`. -/
lemma operationTargetDeg_functorTargetDeg_embedding (c : Composition n) :
    operationTargetDeg (fun l ↦ functorTargetDeg fun j ↦ deg (c.embedding l j)) =
      operationTargetDeg deg := by
  simp only [operationTargetDeg, functorTargetDeg, Finset.sum_add_distrib, c.sum_sum_embedding,
    add_assoc, ← map_sum, ← map_add, Finset.sum_sub_distrib, ← Nat.cast_sum]
  simp

end Degrees

section CompositionBlock

/-! ### Blocks of a composition

A composition `c = (i₁, …, iₖ)` of `n` cuts a composable string of `n` inputs into `k` blocks:
the `l`-th block has size `iₗ = c.blocksFun l` and starts at position `c.sizeUpTo l`. In the
right-hand side of the functor equation, the functor component `φ_{iₗ}` is applied to the
`l`-th block and the outer operation `m'ₖ` to the resulting `k` values, so both the sizes of
the blocks and their number must be positive. The lemmas and instances on `Composition` below
are stated without reference to functors. -/

variable {Obj : Type*} (obj : Fin (n + 1) → Obj) (c : Composition n) (l : Fin c.length)

/-- The `l`-th block of a composition `c` of `n` ends no later than `n`. -/
lemma _root_.Composition.sizeUpTo_add_blocksFun_le : c.sizeUpTo l + c.blocksFun l ≤ n :=
  (c.sizeUpTo_succ' l).symm.trans_le (c.sizeUpTo_le _)

/-- Every block of a composition is nonempty. -/
instance _root_.Composition.neZero_blocksFun : NeZero (c.blocksFun l) :=
  NeZero.of_pos (c.one_le_blocksFun l)

/-- A composition of a positive integer has at least one block. -/
instance _root_.Composition.neZero_length [NeZero n] : NeZero c.length :=
  NeZero.of_pos (c.length_pos_of_pos (NeZero.pos n))

/-- The object string of the `l`-th block of a composition `c` of `n`: its `i`-th object is
`obj (c.sizeUpTo l + i)`, for `i ≤ c.blocksFun l`. -/
def compositionBlockObj : Fin (c.blocksFun l + 1) → Obj :=
  fun i ↦ obj ((i.natAdd (c.sizeUpTo l)).castLE (Nat.succ_le_succ (c.sizeUpTo_add_blocksFun_le l)))

/-- The `l`-th block of a composition starts at the `l`-th boundary. -/
@[simp]
lemma compositionBlockObj_zero :
    compositionBlockObj obj c l 0 = obj (c.boundary l.castSucc) := by
  unfold compositionBlockObj
  congr 1

/-- The `l`-th block of a composition ends at the `(l + 1)`-st boundary. -/
@[simp]
lemma compositionBlockObj_last :
    compositionBlockObj obj c l (Fin.last (c.blocksFun l)) = obj (c.boundary l.succ) := by
  unfold compositionBlockObj Composition.boundary
  congr 1
  ext
  simp [Composition.sizeUpTo_succ']

end CompositionBlock

/-- The data of an `A∞`-functor between graded `R`-linear quivers: a map on objects, a
homomorphism of grading types and, for each `n ≥ 1`, a functor component `φₙ` of degree `1 - n`.
No relations are imposed. -/
structure AInfinityFunctorData (β β' : Type*) [AddCommGroup β] [Grading β]
    [AddCommGroup β'] [Grading β'] (R : Type*) [CommRing R] (Obj Obj' : Type*)
    [GradedLinearQuiver β R Obj] [GradedLinearQuiver β' R Obj'] where
  /-- The action of the functor on objects. -/
  obj : Obj → Obj'
  /-- The homomorphism of grading types translating source degrees into target degrees. -/
  degMap : β →+ᵍ β'
  /-- The action of the functor on hom spaces, i.e. the functor components `φₙ`, of degree
  `1 - n`, landing in the hom spaces of the target in the translated degrees. -/
  map : {n : ℕ} → [NeZero n] → (X : Fin (n + 1) → Obj) →
    GradedMultilinearMap R (ComposableHomType R X)
      (fun b : β ↦ (obj (X 0) →ᵍ[R] obj (X (Fin.last n))) (degMap b))
      (shift (1 - (n : ℤ)))

namespace AInfinityFunctorData

variable {β β' : Type*} [AddCommGroup β] [Grading β] [AddCommGroup β']
  [Grading β'] {R : Type*} [CommRing R] {Obj Obj' : Type*}
  [GradedLinearQuiver β R Obj] [GradedLinearQuiver β' R Obj']
variable (m : AInfinityComposition β R Obj) (m' : AInfinityComposition β' R Obj')
variable (F : AInfinityFunctorData β β' R Obj Obj')
variable {obj : Fin (n + 1) → Obj} {deg : Fin n → β}
variable (x : ∀ i : Fin n, ComposableHomType R obj i (deg i))

/-- A homomorphism of grading types commutes with `operationTargetDeg`. -/
lemma operationTargetDeg_degMap {k : ℕ} (b : Fin k → β) :
    operationTargetDeg (fun i ↦ F.degMap (b i)) = F.degMap (operationTargetDeg b) := by
  simp only [operationTargetDeg, map_add, map_sum, GradingHom.map_shift]

/-- `operationTargetDeg_functorTargetDeg_embedding` translated along `degMap`: the term
`m'ₖ(φ_{i₁}(…), …, φ_{iₖ}(…))` of the right-hand side of the functor equation has degree
`degMap d`, where `d` is the degree of `mₙ(a₁, …, aₙ)`. -/
lemma operationTargetDeg_degMap_functorTargetDeg_embedding (c : Composition n) (d : β)
    (hd : operationTargetDeg deg = d) :
    operationTargetDeg (fun l ↦ F.degMap (functorTargetDeg fun j ↦ deg (c.embedding l j))) =
      F.degMap d :=
  (F.operationTargetDeg_degMap _).trans
    (congrArg F.degMap ((operationTargetDeg_functorTargetDeg_embedding deg c).trans hd))

/-! ### The left-hand side of the functor equation -/

/-- The term `φ_{r+1+t}(a₁, …, aᵣ, mₛ(a_{r+1}, …, a_{r+s}), a_{r+s+1}, …, aₙ)` of the
left-hand side of the functor equation indexed by `p = (r, s, t)`, in degree `F.degMap d` for
any `d` equal to the degree of `mₙ(a₁, …, aₙ)`. -/
def mapCompTerm (p : StasheffIndex n) (d : β) (hd : operationTargetDeg deg = d) :
    (F.obj (obj 0) →ᵍ[R] F.obj (obj (Fin.last n))) (F.degMap d) :=
  homCongr R (congrArg F.obj (stasheffObjOut_zero obj p))
    (congrArg F.obj (stasheffObjOut_last obj p)) rfl
    (F.map (stasheffObjOut obj p) (stasheffDegOut deg p) d
      ((functorTargetDeg_stasheffDegOut deg p).trans hd) (indexedStasheffXOut m x p))

/-- The left-hand side of the arity-`n` functor equation, with the Koszul signs of the Stasheff
identities, in degree `F.degMap d` for any `d` equal to the degree of `mₙ(a₁, …, aₙ)`. -/
def mapCompSum (d : β) (hd : operationTargetDeg deg = d) :
    (F.obj (obj 0) →ᵍ[R] F.obj (obj (Fin.last n))) (F.degMap d) :=
  signedStasheffSum deg fun p ↦ F.mapCompTerm m x p d hd

/-! ### The right-hand side of the functor equation -/

/-- The value of the functor component `φ_{iₗ}` on the `l`-th block of a composition
`c = (i₁, …, iₖ)` of `n`, as the `l`-th input of the outer operation `m'ₖ`. -/
def compositionBlockMap (c : Composition n) (l : Fin c.length) :
    ComposableHomType R (fun k ↦ F.obj (obj (c.boundary k))) l
      (F.degMap (functorTargetDeg fun j ↦ deg (c.embedding l j))) :=
  homCongr R (congrArg F.obj (compositionBlockObj_zero obj c l))
    (congrArg F.obj (compositionBlockObj_last obj c l)) rfl
    (F.map (compositionBlockObj obj c l) (fun j ↦ deg (c.embedding l j)) _ rfl
      fun j ↦ x (c.embedding l j))

/-- The term `m'ₖ(φ_{i₁}(a₁, …, a_{i₁}), …, φ_{iₖ}(a_{n-iₖ+1}, …, aₙ))` of the right-hand
side of the functor equation indexed by a composition `c = (i₁, …, iₖ)` of `n`, in degree
`F.degMap d` for any `d` equal to the degree of `mₙ(a₁, …, aₙ)`. -/
def compMapTerm [NeZero n] (c : Composition n) (d : β) (hd : operationTargetDeg deg = d) :
    (F.obj (obj 0) →ᵍ[R] F.obj (obj (Fin.last n))) (F.degMap d) :=
  homCongr R (congrArg (fun k ↦ F.obj (obj k)) c.boundary_zero)
    (congrArg (fun k ↦ F.obj (obj k)) c.boundary_last) rfl
    (m' (fun k ↦ F.obj (obj (c.boundary k)))
      (fun l ↦ F.degMap (functorTargetDeg fun j ↦ deg (c.embedding l j))) (F.degMap d)
      (F.operationTargetDeg_degMap_functorTargetDeg_embedding c d hd)
      (F.compositionBlockMap x c))

/-- The right-hand side of the arity-`n` functor equation, summed over all compositions of `n`,
in degree `F.degMap d` for any `d` equal to the degree of `mₙ(a₁, …, aₙ)`. -/
def compMapSum [NeZero n] (d : β) (hd : operationTargetDeg deg = d) :
    (F.obj (obj 0) →ᵍ[R] F.obj (obj (Fin.last n))) (F.degMap d) :=
  ∑ c : Composition n, F.compMapTerm m' x c d hd

/-- The `A∞`-functor equations: in every arity `n ≥ 1`, the left-hand side and the right-hand
side of the functor equation agree on every composable string of inputs. -/
def SatisfiesFunctorEquations : Prop :=
  ∀ (n : ℕ) [NeZero n] (obj : Fin (n + 1) → Obj) (deg : Fin n → β)
    (x : ∀ i : Fin n, ComposableHomType R obj i (deg i)) (d : β)
    (hd : operationTargetDeg deg = d),
    F.mapCompSum m x d hd = F.compMapSum m' x d hd

end AInfinityFunctorData

/-- An `A∞`-functor between `A∞`-categories: `A∞`-functor data satisfying the functor
equations. -/
structure AInfinityFunctor (β β' : Type*) [AddCommGroup β] [Grading β]
    [AddCommGroup β'] [Grading β'] (R : Type*) [CommRing R] (Obj Obj' : Type*)
    [AInfinityCategory β R Obj] [AInfinityCategory β' R Obj']
    extends AInfinityFunctorData β β' R Obj Obj' where
  /-- The functor components satisfy the functor equations in every arity. -/
  satisfiesFunctorEquations :
    AInfinityFunctorData.SatisfiesFunctorEquations AInfinityCategoryStruct.m
      AInfinityCategoryStruct.m toAInfinityFunctorData

end AInfinityTheory
