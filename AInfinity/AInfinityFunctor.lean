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
`∑_{r + s + t = n, s ≥ 1} (-1)^(‖a_{r+s+1}‖ + ⋯ + ‖a_n‖)
  φ_{r+1+t}(a_1, …, a_r, m_s(a_{r+1}, …, a_{r+s}), a_{r+s+1}, …, a_n)
= ∑_{k ≥ 1} ∑_{i₁ + ⋯ + iₖ = n} m'_k(φ_{i₁}(a_1, …, a_{i₁}), …, φ_{iₖ}(a_{n-iₖ+1}, …, a_n))`.

The sign on the left is the Koszul sign `stasheffSign` of the Stasheff identities. There is no
sign on the right: in reduced degrees `‖a‖ = |a| - 1` every `φᵢ` has degree `0`, so no Koszul
sign arises from moving it past the inputs (compare [Seidel, *Fukaya categories and
Picard–Lefschetz theory*, (1.6)]).

The source and target may be graded by different grading types `β` and `β'`; the functor then
carries a homomorphism `β →+ β'` compatible with the integer shifts and the Koszul signs.

## Main definitions

* `AInfinityTheory.AInfinityFunctorData β β' R Obj Obj'`: a map on objects, a grading
  homomorphism and functor components `φₙ`, not yet subject to any relations.
* `AInfinityTheory.AInfinityFunctorData.lhs`: the left-hand side of the arity-`n`
  functor equation.
* `AInfinityTheory.AInfinityFunctorData.rhs`: the right-hand side of the arity-`n`
  functor equation.
* `AInfinityTheory.AInfinityFunctorData.SatisfiesFunctorEquations`: the functor equations in
  every arity.
* `AInfinityTheory.AInfinityFunctor β β' R Obj Obj'`: an `A∞`-functor between
  `A∞`-categories.

## Implementation notes

The component `φₙ` is a `GradedMultilinearMap` of degree `shift (1 - n)` in the source grading,
into the pullback `b ↦ Hom(F X₀, F Xₙ)(degMap b)` of the target hom spaces. Both sides of
the functor equation are stated pointwise on a composable string of inputs, in degree
`degMap d` for any `d` equal to the degree of `mₙ`, as for `indexedStasheffSum`. Like the
Stasheff sum, the left-hand side is a `signedStasheffSum`. Changes of objects are transported
with `homCongr`. The ordered decompositions `i₁ + ⋯ + iₖ = n` on the right-hand side are
Mathlib's `Composition n`.
-/

@[expose] public section

noncomputable section

namespace AInfinityTheory

open GradedLinearQuiver

variable {n : ℕ}

section Degrees

variable {β : Type*} [AddCommGroup β] [GradingType β]
variable (deg : Fin n → β)

/-- Target degree of the `n`-ary functor component `φₙ`, which has degree `1 - n`. -/
abbrev functorTargetDeg : β :=
  (∑ i, deg i) + shift (1 - (n : ℤ))

/-- The `n`-ary operation `mₙ` has degree one more than the `n`-ary functor component `φₙ`. -/
lemma operationTargetDeg_eq_functorTargetDeg_add_shift_one :
    operationTargetDeg deg = functorTargetDeg deg + shift 1 := by
  rw [operationTargetDeg, functorTargetDeg, add_assoc, ← map_add]
  congr 2
  ring

/-- In the term of the left-hand side of the functor equation indexed by `p = (r, s, t)`, the
outer functor component lands in the degree of `mₙ`. -/
lemma functorTargetDeg_stasheffDegOut (p : StasheffIndex n) :
    functorTargetDeg (stasheffDegOut deg p) = operationTargetDeg deg := by
  apply add_right_cancel (b := (shift 1 : β))
  rw [← operationTargetDeg_eq_functorTargetDeg_add_shift_one, stasheffDegOut_sum,
    stasheffTargetDeg_eq_operationTargetDeg_add_shift_one]

/-- Applying functor components to the blocks of a composition `c` of `n` and then the
`c.length`-ary operation lands in the degree of `mₙ`. -/
lemma operationTargetDeg_functorTargetDeg_embedding (c : Composition n) :
    operationTargetDeg (fun l ↦ functorTargetDeg fun j ↦ deg (c.embedding l j)) =
      operationTargetDeg deg := by
  have hsum : ∑ l, ∑ j, deg (c.embedding l j) = ∑ i, deg i :=
    (Fintype.sum_sigma _).symm.trans (c.blocksFinEquiv.sum_comp deg)
  have hlen : ∑ l, (1 - (c.blocksFun l : ℤ)) + (2 - c.length) = 2 - n := by
    rw [Finset.sum_sub_distrib, ← Nat.cast_sum, c.sum_blocksFun]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    ring
  simp only [operationTargetDeg, functorTargetDeg, Finset.sum_add_distrib, hsum, add_assoc,
    ← map_sum, ← map_add, hlen]

end Degrees

section CompositionBlock

variable {Obj : Type*} (obj : Fin (n + 1) → Obj) (c : Composition n) (l : Fin c.length)

/-- The `l`-th block of a composition `c` of `n` ends no later than `n`. -/
lemma _root_.Composition.sizeUpTo_add_blocksFun_le : c.sizeUpTo l + c.blocksFun l ≤ n :=
  (c.sizeUpTo_succ' l).symm.trans_le (c.sizeUpTo_le _)

/-- The object string `obj iₗ, …, obj (iₗ + c.blocksFun l)` of the `l`-th block of a composition
`c` of `n`, where `iₗ = c.sizeUpTo l` is the start of the block. -/
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
structure AInfinityFunctorData (β β' : Type*) [AddCommGroup β] [GradingType β]
    [AddCommGroup β'] [GradingType β'] (R : Type*) [CommRing R] (Obj Obj' : Type*)
    [GradedLinearQuiver β R Obj] [GradedLinearQuiver β' R Obj'] where
  /-- The action of the functor on objects. -/
  obj : Obj → Obj'
  /-- The translation of degrees from the source grading to the target grading. -/
  degMap : β →+ β'
  /-- The grading homomorphism preserves the integer degree shifts. -/
  degMap_shift : ∀ k : ℤ, degMap (shift k) = shift k
  /-- The grading homomorphism preserves the Koszul signs. -/
  degMap_sign : ∀ b : β, sign (degMap b) = sign b
  /-- The action of the functor on hom spaces, i.e. the functor components `φₙ`, of degree
  `1 - n`, landing in the hom spaces of the target in the translated degrees. -/
  map : {n : ℕ} → [NeZero n] → (X : Fin (n + 1) → Obj) →
    GradedMultilinearMap R (ComposableHomType R (β := β) X)
      (fun b : β ↦ (obj (X 0) →ᵍ[R] obj (X (Fin.last n))) (degMap b))
      (shift (1 - (n : ℤ)))

namespace AInfinityFunctorData

variable {β β' : Type*} [AddCommGroup β] [GradingType β] [AddCommGroup β']
  [GradingType β'] {R : Type*} [CommRing R] {Obj Obj' : Type*}
  [GradedLinearQuiver β R Obj] [GradedLinearQuiver β' R Obj']
variable (m : AInfinityComposition β R Obj) (m' : AInfinityComposition β' R Obj')
variable (F : AInfinityFunctorData β β' R Obj Obj')
variable {obj : Fin (n + 1) → Obj} {deg : Fin n → β}
variable (x : ∀ i : Fin n, ComposableHomType R obj i (deg i))

/-- The grading homomorphism commutes with taking the degree of an operation. -/
lemma operationTargetDeg_degMap {k : ℕ} (b : Fin k → β) :
    operationTargetDeg (fun i ↦ F.degMap (b i)) = F.degMap (operationTargetDeg b) := by
  simp only [operationTargetDeg, ← map_sum, map_add]
  congr 1
  exact (F.degMap_shift _).symm

/-- Applying functor components to the blocks of a composition `c` of `n` and then the
`c.length`-ary operation of the target lands in the image of the degree of `mₙ`. -/
lemma operationTargetDeg_degMap_functorTargetDeg_embedding (c : Composition n) (d : β)
    (hd : operationTargetDeg deg = d) :
    operationTargetDeg (fun l ↦ F.degMap (functorTargetDeg fun j ↦ deg (c.embedding l j))) =
      F.degMap d :=
  (F.operationTargetDeg_degMap _).trans
    (congrArg F.degMap ((operationTargetDeg_functorTargetDeg_embedding deg c).trans hd))

/-! ### The left-hand side of the functor equation -/

/-- The term `φ_{r+1+t}(a_1, …, a_r, m_s(a_{r+1}, …, a_{r+s}), a_{r+s+1}, …, a_n)` of the
left-hand side of the functor equation indexed by `p = (r, s, t)`, in degree `F.degMap d` for
any `d` equal to the degree of `mₙ`. -/
def lhsTerm (p : StasheffIndex n) (d : β) (hd : operationTargetDeg deg = d) :
    (F.obj (obj 0) →ᵍ[R] F.obj (obj (Fin.last n))) (F.degMap d) :=
  homCongr R (congrArg F.obj (stasheffObjOut_zero obj p))
    (congrArg F.obj (stasheffObjOut_last obj p)) rfl
    (F.map (stasheffObjOut obj p) (stasheffDegOut deg p) d
      ((functorTargetDeg_stasheffDegOut deg p).trans hd) (indexedStasheffXOut m x p))

/-- The left-hand side of the arity-`n` functor equation, with the Koszul signs of the Stasheff
identities, in degree `F.degMap d` for any `d` equal to the degree of `mₙ`. -/
def lhs (d : β) (hd : operationTargetDeg deg = d) :
    (F.obj (obj 0) →ᵍ[R] F.obj (obj (Fin.last n))) (F.degMap d) :=
  signedStasheffSum deg fun p ↦ F.lhsTerm m x p d hd

/-! ### The right-hand side of the functor equation -/

/-- The output `φ_{iₗ}` of the `l`-th block of a composition `c = (i₁, …, iₖ)` of `n`, as the
`l`-th input of the outer operation `m'_k`. -/
def rhsInput (c : Composition n) (l : Fin c.length) :
    ComposableHomType R (fun k ↦ F.obj (obj (c.boundary k))) l
      (F.degMap (functorTargetDeg fun j ↦ deg (c.embedding l j))) :=
  haveI : NeZero (c.blocksFun l) := NeZero.of_pos (c.one_le_blocksFun l)
  homCongr R (congrArg F.obj (compositionBlockObj_zero obj c l))
    (congrArg F.obj (compositionBlockObj_last obj c l)) rfl
    (F.map (compositionBlockObj obj c l) (fun j ↦ deg (c.embedding l j)) _ rfl
      fun j ↦ x (c.embedding l j))

/-- The term `m'_k(φ_{i₁}(a_1, …, a_{i₁}), …, φ_{iₖ}(a_{n-iₖ+1}, …, a_n))` of the right-hand
side of the functor equation indexed by a composition `c = (i₁, …, iₖ)` of `n`, in degree
`F.degMap d` for any `d` equal to the degree of `mₙ`. -/
def rhsTerm [NeZero n] (c : Composition n) (d : β) (hd : operationTargetDeg deg = d) :
    (F.obj (obj 0) →ᵍ[R] F.obj (obj (Fin.last n))) (F.degMap d) :=
  haveI : NeZero c.length := NeZero.of_pos (c.length_pos_of_pos (NeZero.pos n))
  homCongr R (congrArg (fun k ↦ F.obj (obj k)) c.boundary_zero)
    (congrArg (fun k ↦ F.obj (obj k)) c.boundary_last) rfl
    (m' (fun k ↦ F.obj (obj (c.boundary k)))
      (fun l ↦ F.degMap (functorTargetDeg fun j ↦ deg (c.embedding l j))) (F.degMap d)
      (F.operationTargetDeg_degMap_functorTargetDeg_embedding c d hd)
      (F.rhsInput x c))

/-- The right-hand side of the arity-`n` functor equation, summed over all compositions of `n`,
in degree `F.degMap d` for any `d` equal to the degree of `mₙ`. -/
def rhs [NeZero n] (d : β) (hd : operationTargetDeg deg = d) :
    (F.obj (obj 0) →ᵍ[R] F.obj (obj (Fin.last n))) (F.degMap d) :=
  ∑ c : Composition n, F.rhsTerm m' x c d hd

/-- The `A∞`-functor equations: in every arity `n ≥ 1`, the left-hand side and the right-hand
side of the functor equation agree on every composable string of inputs. -/
def SatisfiesFunctorEquations : Prop :=
  ∀ (n : ℕ) [NeZero n] (obj : Fin (n + 1) → Obj) (deg : Fin n → β)
    (x : ∀ i : Fin n, ComposableHomType R obj i (deg i)) (d : β)
    (hd : operationTargetDeg deg = d),
    F.lhs m x d hd = F.rhs m' x d hd

end AInfinityFunctorData

/-- An `A∞`-functor between `A∞`-categories: `A∞`-functor data satisfying the functor
equations. -/
structure AInfinityFunctor (β β' : Type*) [AddCommGroup β] [GradingType β]
    [AddCommGroup β'] [GradingType β'] (R : Type*) [CommRing R] (Obj Obj' : Type*)
    [AInfinityCategory β R Obj] [AInfinityCategory β' R Obj']
    extends AInfinityFunctorData β β' R Obj Obj' where
  /-- The functor components satisfy the functor equations in every arity. -/
  satisfiesFunctorEquations :
    AInfinityFunctorData.SatisfiesFunctorEquations AInfinityCategoryStruct.m
      AInfinityCategoryStruct.m toAInfinityFunctorData

end AInfinityTheory
