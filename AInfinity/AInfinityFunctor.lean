/-
Copyright (c) 2026 Annie Yao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Annie Yao, Marco David, Jason Dong, Zhan Shi
-/
module

public import AInfinity.AInfinityCategory
public import AInfinity.ComposableMultilinearMap

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
  homomorphism and functor components φₙ, a composable multilinear map with `s = 1`, not yet
  subject to any relations.
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
Hom(F X₀, F Xₙ) in degree `degMap (targetDeg 1 deg)`. All degree arithmetic
happens in `β`, and φₙ is only ever evaluated in target degrees of the form
`degMap b`.

Both sides of the functor equation are stated pointwise on composable inputs
a₁, …, aₙ of degrees `deg`, in degree `degMap d` for any `d` equal to the degree
`targetDeg 2 deg` of mₙ(a₁, …, aₙ), as for `stasheffSum`. The left-hand side is
a `signedStasheffSum`, like the Stasheff sum. The decompositions i₁ + ⋯ + iₖ = n on the
right-hand side are Mathlib's `Composition n`, and its terms are the terms
`ComposableMultilinearMap.compTerm` of the composite m' ∘ F. Changes of objects are transported
with `homCongr`.

`mapCompSum` and `compMapSum` are named in order of application: a functor component applied
to a composition, and a composition of functor components. As composable multilinear maps, the
two sides are the composites F ∘ (𝟙 | m) and m' ∘ F, see
`AInfinity.FunctorComposition.FunctorEquation`.

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

/-- The term of the left-hand side of the functor equation indexed by p = (r, s, t), in which
the functor component of arity r + 1 + t is applied to the inner output and the remaining
inputs, has the degree of mₙ(a₁, …, aₙ). -/
lemma targetDeg_stasheffDegOut (p : StasheffIndex n) :
    targetDeg 1 (stasheffDegOut deg p) = targetDeg 2 deg := by
  apply add_right_cancel (b := (degOne : β))
  rw [← targetDeg_eq_targetDeg_add_degOne (s := 2) (t := 1) (by norm_num), stasheffDegOut_sum,
    targetDeg_eq_targetDeg_add_degOne (s := 3) (t := 2) (by norm_num)]

end Degrees

/-- The data of an A∞-functor between graded `R`-linear quivers: a map on objects, a
homomorphism of gradings and, for each n ≥ 1, a functor component φₙ of degree
1 - n, landing in the hom spaces of the target in the translated degrees.
No relations are imposed. -/
structure AInfinityFunctorData (β β' : Type*) [AddCommGroup β] [Grading β]
    [AddCommGroup β'] [Grading β'] (R : Type*) [Semiring R] (Obj Obj' : Type*)
    [GradedLinearQuiver β R Obj] [GradedLinearQuiver β' R Obj'] where
  /-- The action of the functor on objects. -/
  obj : Obj → Obj'
  /-- The homomorphism of gradings translating source degrees into target degrees. -/
  degMap : β →+ᵍ β'
  /-- The action of the functor on hom spaces, i.e. the functor components φₙ, of
  degree 1 - n, landing in the hom spaces of the target in the translated degrees: a composable
  multilinear map with `s = 1` over `obj` and `degMap`. -/
  toComposableMultilinearMap : ComposableMultilinearMap R obj degMap 1

namespace AInfinityFunctorData

variable {β β' : Type*} [AddCommGroup β] [Grading β] [AddCommGroup β']
  [Grading β'] {R : Type*} [Semiring R] {Obj Obj' : Type*}

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
def mapCompTerm (p : StasheffIndex n) (d : β) (hd : targetDeg 2 deg = d) :
    (F.obj (X 0) →ᵍ[R] F.obj (X (Fin.last n))) (F.degMap d) :=
  homCongr R (congrArg F.obj (stasheffObjOut_zero X p))
    (congrArg F.obj (stasheffObjOut_last X p)) rfl
    ((F.toComposableMultilinearMap.map (stasheffObjOut X p)).v (stasheffDegOut deg p) d
      ((targetDeg_stasheffDegOut deg p).trans hd) (stasheffInputsOut a p))

/-- The left-hand side of the arity-n functor equation, with the Koszul signs of the Stasheff
identities, in degree `F.degMap d` for any `d` equal to the degree of mₙ(a₁, …, aₙ). -/
def mapCompSum (d : β) (hd : targetDeg 2 deg = d) :
    (F.obj (X 0) →ᵍ[R] F.obj (X (Fin.last n))) (F.degMap d) :=
  signedStasheffSum deg fun p ↦ F.mapCompTerm a p d hd

/-! ### The right-hand side of the functor equation -/

/-- The term of the right-hand side of the functor equation indexed by a composition
c = (i₁, …, iₖ) of `n`: the operation m'ₖ of the target applied to the values of the functor
components on the k blocks of c, in degree `F.degMap d` for any `d` equal to the degree of
mₙ(a₁, …, aₙ). It is the term of the composite m' ∘ F indexed by c. -/
def compMapTerm [NeZero n] (c : Composition n) (d : β) (hd : targetDeg 2 deg = d) :
    (F.obj (X 0) →ᵍ[R] F.obj (X (Fin.last n))) (F.degMap d) :=
  (AInfinityCategoryStruct.toComposableMultilinearMap β' R Obj').compTerm a c
    (fun _ ↦ ⟨1, F.toComposableMultilinearMap⟩) (F.degMap d)
    (ComposableMultilinearMap.comp_deg F.degMap (GradingHom.id β') deg c hd)

/-- The right-hand side of the arity-n functor equation, summed over all compositions of
`n`, in degree `F.degMap d` for any `d` equal to the degree of mₙ(a₁, …, aₙ). -/
def compMapSum [NeZero n] (d : β) (hd : targetDeg 2 deg = d) :
    (F.obj (X 0) →ᵍ[R] F.obj (X (Fin.last n))) (F.degMap d) :=
  ∑ c : Composition n, F.compMapTerm a c d hd

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
    (hd : targetDeg 2 deg = d) :
    toAInfinityFunctorData.mapCompSum a d hd =
      toAInfinityFunctorData.compMapSum a d hd

namespace AInfinityFunctor

variable {β β' : Type*} [AddCommGroup β] [Grading β] [AddCommGroup β'] [Grading β']
  {R : Type*} [Semiring R] {Obj Obj' : Type*} [AInfinityCategory β R Obj]
  [AInfinityCategory β' R Obj']

/-- An A∞-functor is determined by its A∞-functor data, since the functor equations are a
proposition. -/
lemma toAInfinityFunctorData_injective :
    Function.Injective (toAInfinityFunctorData : AInfinityFunctor β β' R Obj Obj' → _) := by
  rintro ⟨F, hF⟩ ⟨G, hG⟩ rfl
  rfl

end AInfinityFunctor

end AInfinityTheory
