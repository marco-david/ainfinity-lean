/-
Copyright (c) 2026 Annie Yao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Annie Yao, Marco David, Zhan Shi
-/
module

public import AInfinity.FunctorComposition.Assoc
public import AInfinity.FunctorComposition.Reindex

/-! # Composition of A∞-functors

The composite `G.comp F` of A∞-functors `F` from `Obj` to `Obj'` and `G` from `Obj'` to `Obj''` is
the composite of the underlying A∞-functor data, defined in `AInfinity.FunctorComposition.Defs`.
This file proves that it satisfies the A∞-functor equations, and that the composition of
A∞-functors is associative.

## Main definitions

* `AInfinityTheory.AInfinityFunctor.comp`: the composite `G.comp F` of A∞-functors.

## Main results

* `AInfinityTheory.AInfinityFunctor.comp_mapCompSum_eq_compMapSum`: the composite of two
  A∞-functors satisfies the A∞-functor equations.
* `AInfinityTheory.AInfinityFunctor.comp_assoc`: the composition of A∞-functors is associative.

## Implementation notes

The proof depends on combinatorial statements about the index types `MapCompIndex` and
`CompMapIndex`, and on the Koszul sign identities in
`AInfinity.FunctorComposition.Signs`. The functor equation for `G.comp F` is reduced to the
functor equations of `F`, applied blockwise, and of `G`, applied to the outputs of `F`, in three
steps:

1. `comp_mapCompSum_eq_sum_mapCompSumBlockMap`: by the reindexing in
   `AInfinity.FunctorComposition.Reindex` and the functor equations of `F`, the left-hand side of
   the functor equation for `G.comp F` is the sum, over all compositions `c` of `n`, of the
   left-hand side of the functor equation for `G` on the values of `F` on the blocks of `c`.
   This step depends on the bijectivity of the projections of `MapCompIndex` and `CompMapIndex`
   and on two sign identities.
2. `sum_mapCompSumBlockMap_eq_sum_compMapSumBlockMap`: the functor equations of `G`.
3. `ComposableMultilinearMap.sum_compMapSumBlockMap_eq_comp_compMapSum`: the resulting two-level
   sum over compositions is the right-hand side of the functor equation for `G.comp F`. Both
   sides are values of composites of the operations m'' of the target, as a composable
   multilinear map, with A∞-functor data: the first of `(m''.comp G).comp F` and the second of
   `m''.comp (G.comp F)`. So this step is the associativity `ComposableMultilinearMap.comp_assoc`,
   proved in `AInfinity.FunctorComposition.Assoc` along `Composition.sigmaEquivSigmaPi`. The
   same statement, for an A∞-functor in place of m'', gives `AInfinityFunctor.comp_assoc`.
-/

@[expose] public section

noncomputable section

namespace AInfinityTheory

open GradedLinearQuiver

variable {n : ℕ}

/-! ### The functor equations of the composite -/

namespace AInfinityFunctor

variable {β β' β'' : Type*} [AddCommGroup β] [Grading β] [AddCommGroup β'] [Grading β']
  [AddCommGroup β''] [Grading β''] {R : Type*} [Semiring R] {Obj Obj' Obj'' : Type*}
  [AInfinityCategory β R Obj] [AInfinityCategory β' R Obj'] [AInfinityCategory β'' R Obj'']
variable (G : AInfinityFunctor β' β'' R Obj' Obj'') (F : AInfinityFunctor β β' R Obj Obj')
  {X : Fin (n + 1) → Obj} {deg : Fin n → β} (a : ∀ i : Fin n, ComposableHom β R X i (deg i))

/-- The functor equation of `F` on the `j`-th block of a composition `c`, as an equation between
inputs of an outer operation on the objects `F (X (c.boundary k))`. -/
lemma signedStasheffSum_compositionBlockMapCompTerm (c : Composition n) (j : Fin c.length) :
    signedStasheffSum (fun i ↦ deg (c.embedding j i))
        (fun p ↦ F.compositionBlockMapCompTerm a c j p) =
      ∑ c' : Composition (c.blocksFun j), F.compositionBlockCompMapTerm a c j c' := by
  have h := F.mapCompSum_eq_compMapSum (X := compositionBlockObj X c j)
    (fun i ↦ a (c.embedding j i)) rfl
  unfold ComposableMultilinearMap.mapCompSum ComposableMultilinearMap.compMapSum at h
  have := congrArg (homCongr R (congrArg F.obj (compositionBlockObj_zero X c j))
    (congrArg F.obj (compositionBlockObj_last X c j)) rfl) h
  rwa [map_signedStasheffSum, map_sum] at this

variable [NeZero n] {d : β} (hd : targetDeg 2 deg = d)

/-- Applying the functor equations of `F` blockwise: the left-hand side of the functor equation
for `G.comp F` is the sum, over all compositions `c` of `n`, of the left-hand side of the
functor equation for `G` on the values of the components of `F` on the blocks of `c`.

The proof depends on the combinatorial statements `MapCompIndex.bijective_toSigma`,
`MapCompIndex.bijective_toBlock`, `CompMapIndex.bijective_toSigma`,
`CompMapIndex.bijective_toBlock`, `MapCompIndex.stasheffSign_eq` and
`CompMapIndex.stasheffSign_eq`. -/
theorem comp_mapCompSum_eq_sum_mapCompSumBlockMap :
    (G.toAInfinityFunctorData.comp F.toAInfinityFunctorData).mapCompSum a d hd =
      ∑ c : Composition n, G.mapCompSumBlockMap F.toAInfinityFunctorData a c d hd := by
  rw [ComposableMultilinearMap.comp_mapCompSum_eq_sum_compMapBlockUpdate,
    ComposableMultilinearMap.sum_mapCompSumBlockMap_eq_sum_compMapBlockUpdate]
  simp only [signedStasheffSum_compositionBlockMapCompTerm]
  rfl

/-- The functor equation of `G` on the values of the components of `F` on the blocks of a
composition `c` of `n`, transported to the endpoints `G (F X₀)` and `G (F Xₙ)`. -/
lemma mapCompSumBlockMap_eq_compMapSumBlockMap (c : Composition n) :
    G.mapCompSumBlockMap F.toAInfinityFunctorData a c d hd =
      G.compMapSumBlockMap F.toAInfinityFunctorData a c d hd :=
  congrArg _ (G.mapCompSum_eq_compMapSum _ _)

/-- Applying the functor equations of `G` to the values of the components of `F` on the blocks
of every composition of `n`. -/
lemma sum_mapCompSumBlockMap_eq_sum_compMapSumBlockMap :
    ∑ c : Composition n, G.mapCompSumBlockMap F.toAInfinityFunctorData a c d hd =
      ∑ c : Composition n, G.compMapSumBlockMap F.toAInfinityFunctorData a c d hd :=
  Finset.sum_congr rfl fun c _ ↦ mapCompSumBlockMap_eq_compMapSumBlockMap G F a hd c

/-- The composite of two A∞-functors satisfies the A∞-functor equations. -/
theorem comp_mapCompSum_eq_compMapSum :
    (G.toAInfinityFunctorData.comp F.toAInfinityFunctorData).mapCompSum a d hd =
      (G.toAInfinityFunctorData.comp F.toAInfinityFunctorData).compMapSum a d hd :=
  (comp_mapCompSum_eq_sum_mapCompSumBlockMap G F a hd).trans
    ((sum_mapCompSumBlockMap_eq_sum_compMapSumBlockMap G F a hd).trans
      (ComposableMultilinearMap.sum_compMapSumBlockMap_eq_comp_compMapSum G.toAInfinityFunctorData
        F.toAInfinityFunctorData a _ hd))

/-! ### The composite of A∞-functors -/

omit [NeZero n] in
/-- The composite `G.comp F` of A∞-functors `F` from `Obj` to `Obj'` and `G` from `Obj'` to
`Obj''`, written in Mathlib's order: the composite of the underlying A∞-functor data, which
satisfies the A∞-functor equations by `comp_mapCompSum_eq_compMapSum`. -/
protected def comp : AInfinityFunctor β β'' R Obj Obj'' where
  toAInfinityFunctorData := G.toAInfinityFunctorData.comp F.toAInfinityFunctorData
  mapCompSum_eq_compMapSum a _ hd := comp_mapCompSum_eq_compMapSum G F a hd

omit [NeZero n] in
@[simp]
lemma comp_toAInfinityFunctorData :
    (G.comp F).toAInfinityFunctorData = G.toAInfinityFunctorData.comp F.toAInfinityFunctorData :=
  rfl

end AInfinityFunctor

/-! ### Associativity -/

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

variable {β'' β''' : Type*} [AddCommGroup β''] [Grading β''] [AddCommGroup β'''] [Grading β''']
  {Obj'' Obj''' : Type*} [AInfinityCategory β'' R Obj''] [AInfinityCategory β''' R Obj''']

/-- The composition of A∞-functors is associative. -/
theorem comp_assoc (H : AInfinityFunctor β'' β''' R Obj'' Obj''')
    (G : AInfinityFunctor β' β'' R Obj' Obj'') (F : AInfinityFunctor β β' R Obj Obj') :
    (H.comp G).comp F = H.comp (G.comp F) :=
  toAInfinityFunctorData_injective (ComposableMultilinearMap.comp_assoc _ _ _)

end AInfinityFunctor

end AInfinityTheory
