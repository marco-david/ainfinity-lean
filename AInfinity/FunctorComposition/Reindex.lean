/-
Copyright (c) 2026 Zhan Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhan Shi
-/
module

public import AInfinity.FunctorComposition.BlockMap
public import AInfinity.FunctorComposition.CompMapMapIndex
public import AInfinity.FunctorComposition.Signs

/-! # Reindexing the functor equation for a composite of A∞-functors

Let `F` and `G` be A∞-functor data. The two sides of the functor equation for `G.comp F` are
compared with the corresponding sums for `G` on the values of `F`, after regrouping their terms.

For the left-hand sides, two sums are regrouped by a composition c of `n` into the inputs of the
outer component of `G` and the input j of it that contains the inner operation:

* the left-hand side of the functor equation for `G.comp F`, which becomes the sum of the
  components of `G` applied to the values of `F` on the blocks of `c`, with the value on the j-th
  block replaced by the left-hand side of the functor equation of `F` on it;
* the sum, over all compositions of `n`, of the left-hand sides of the functor equations for `G`
  on the values of `F`, which becomes the same sum with the right-hand side of the functor
  equation of `F` in place of the left-hand side.

This goes through the index types `MapCompIndex` and `CompMapIndex`. For the right-hand sides,
the sum, over all compositions of `n`, of the right-hand sides of the functor equations for `G`
on the values of `F` is the right-hand side of the functor equation for `G.comp F`, through the
index type `CompMapMapIndex`. In each case, the two descriptions of a term are matched here.

## Main definitions

* `AInfinityTheory.AInfinityFunctorData.compMapCompTerm`: the summand, indexed by a composition,
  of a term of the left-hand side of the functor equation for `G.comp F`.
* `AInfinityTheory.AInfinityFunctorData.compositionBlockCompTerm`: the summand, indexed by a
  composition of a block, of the value of the composite component (G ∘ F) on that block.
* `AInfinityTheory.AInfinityFunctorData.compCompMapTerm`: the summand, indexed by compositions of
  the blocks, of a term of the right-hand side of the functor equation for `G.comp F`.

## Main results

* `AInfinityTheory.MapCompIndex.compMapCompTerm_eq_compMapBlockUpdate`,
  `AInfinityTheory.CompMapIndex.mapCompTermBlockMap_eq_compMapBlockUpdate`,
  `AInfinityTheory.CompMapMapIndex.compMapTermBlockMap_eq_compCompMapTerm`: the two descriptions
  of a term agree.
* `AInfinityTheory.AInfinityFunctorData.comp_mapCompSum_eq_sum_compMapBlockUpdate`,
  `AInfinityTheory.AInfinityFunctorData.sum_mapCompSumBlockMap_eq_sum_compMapBlockUpdate`: the
  two regrouped sums of left-hand sides.
* `AInfinityTheory.AInfinityFunctorData.sum_compMapSumBlockMap_eq_comp_compMapSum`: the sum of the
  right-hand sides of the functor equations for `G` on the values of `F` is the right-hand side
  of the functor equation for `G.comp F`.

## Implementation notes

The reindexing relies on the bijectivity statements for the index types `MapCompIndex`,
`CompMapIndex` and `CompMapMapIndex`, and on the sign identities in
`AInfinity.FunctorComposition.Signs`.
The two descriptions of a term are matched using only the relations recorded in the index types.
-/

@[expose] public section

noncomputable section

namespace AInfinityTheory

open GradedLinearQuiver

variable {n : ℕ}

/-! ### The terms of the left-hand side of the functor equation for `G.comp F` -/

namespace AInfinityFunctorData

variable {β β' β'' : Type*} [AddCommGroup β] [Grading β] [AddCommGroup β'] [Grading β']
  [AddCommGroup β''] [Grading β''] {R : Type*} [Semiring R] {Obj Obj' Obj'' : Type*}
  [AInfinityCategoryStruct β R Obj] [AInfinityCategoryStruct β' R Obj']
  [AInfinityCategoryStruct β'' R Obj'']
variable (G : AInfinityFunctorData β' β'' R Obj' Obj'') (F : AInfinityFunctorData β β' R Obj Obj')
  {X : Fin (n + 1) → Obj} {deg : Fin n → β} (a : ∀ i : Fin n, ComposableHom β R X i (deg i))
  (d : β) (hd : operationTargetDeg deg = d)

/-- The summand, indexed by a composition `c` of r + 1 + t, of the term indexed by
p = (r, s, t) of the left-hand side of the functor equation for `G.comp F`: the component of `G`
of arity `c.length` applied to the values of the components of `F` on the blocks of `c` of the
inputs of the outer operation of the term, one of which is the inner output. -/
def compMapCompTerm (p : StasheffIndex n) (c : Composition (p.r + 1 + p.t)) :
    (G.obj (F.obj (X 0)) →ᵍ[R] G.obj (F.obj (X (Fin.last n)))) (G.degMap (F.degMap d)) :=
  homCongr R (by rw [c.boundary_zero, stasheffObjOut_zero])
    (by rw [c.boundary_last, stasheffObjOut_last]) rfl
    ((G.map fun k ↦ F.obj (stasheffObjOut X p (c.boundary k))).v _ (F.degMap d)
      (F.functorTargetDeg_degMap_functorTargetDeg_embedding c d
        ((functorTargetDeg_stasheffDegOut deg p).trans hd))
      fun l ↦ F.compositionBlockMap (stasheffInputsOut a p) c l)

lemma comp_mapCompTerm_eq_sum (p : StasheffIndex n) :
    (G.comp F).mapCompTerm a p d hd = ∑ c, G.compMapCompTerm F a d hd p c := by
  have h := sum_apply Finset.univ (fun c ↦ compMapTermMultilinearMap G F (stasheffObjOut X p)
    (stasheffDegOut deg p) c d ((functorTargetDeg_stasheffDegOut deg p).trans hd))
    (stasheffInputsOut a p)
  refine ((congrArg (homCongr R (congrArg (fun Z ↦ G.obj (F.obj Z)) (stasheffObjOut_zero X p))
    (congrArg (fun Z ↦ G.obj (F.obj Z)) (stasheffObjOut_last X p)) rfl) h).trans
    (map_sum _ _ _)).trans (Finset.sum_congr rfl fun c _ ↦ ?_)
  simp only [compMapTermMultilinearMap, LinearMap.compMultilinearMap_apply, LinearEquiv.coe_coe,
    MultilinearMap.compComposition_apply, compositionBlockMultilinearMap_apply, homCongr_homCongr]
  rfl

end AInfinityFunctorData

namespace MapCompIndex

open AInfinityFunctorData

variable (x : MapCompIndex n)

/-- The inputs of the inner operation of `x.stasheff` are those of the inner operation of
`x.inner`, inside the block `x.block` of `x.outer`. -/
lemma innerIndex_eq (u : Fin x.stasheff.s) :
    x.stasheff.innerIndex u = x.outer.embedding x.block (x.inner.innerIndex (u.cast x.s_eq)) :=
  Fin.ext (by simp [x.r_eq, add_assoc])

section Degrees

variable {β : Type*} [AddCommGroup β] [Grading β] (deg : Fin n → β)

lemma functorTargetDeg_stasheffDegOut_embedding_of_ne (l : Fin x.composition.length)
    (hl : (l : ℕ) ≠ x.block) :
    functorTargetDeg (fun i ↦ stasheffDegOut deg x.stasheff (x.composition.embedding l i)) =
      functorTargetDeg (fun i ↦ deg (x.outer.embedding (l.cast x.length_eq) i)) := by
  have := x.stasheff.one_le_s
  rcases x.block_cases l with ⟨-, hs, hb, hle⟩ | ⟨h, -⟩ | ⟨-, hs, hb, hlt⟩
  · exact functorTargetDeg_congr hb fun i ↦
      stasheffDegOut_of_lt _ _ _ _ (by have := i.2; simp only [Composition.coe_embedding]; omega)
        (by simp only [Composition.coe_embedding, Fin.val_cast]; omega)
  · exact absurd h hl
  · exact functorTargetDeg_congr hb fun i ↦
      stasheffDegOut_of_gt _ _ _ _ (by simp only [Composition.coe_embedding]; omega)
        (by simp only [Composition.coe_embedding, Fin.val_cast]; omega)

lemma stasheffInnerDeg_eq :
    stasheffInnerDeg deg x.stasheff =
      stasheffInnerDeg (fun i ↦ deg (x.outer.embedding x.block i)) x.inner :=
  operationTargetDeg_congr x.s_eq fun u ↦ congrArg deg (x.innerIndex_eq u)

/-- On the block of the inner operation, the input degrees of the outer operation of the term
indexed by `x.stasheff` are those of the outer operation of the term indexed by `x.inner`. -/
lemma stasheffDegOut_embedding_of_eq (l : Fin x.composition.length) (hl : (l : ℕ) = x.block)
    (e : x.composition.blocksFun l = x.inner.r + 1 + x.inner.t)
    (i : Fin (x.composition.blocksFun l)) :
    stasheffDegOut deg x.stasheff (x.composition.embedding l i) =
      stasheffDegOut (fun i ↦ deg (x.outer.embedding x.block i)) x.inner (i.cast e) := by
  have := x.sizeUpTo_of_eq l hl; have := x.r_eq; have := x.s_eq; have := x.inner.sum_eq
  have := x.inner.one_le_s; have := i.2
  rcases lt_trichotomy (i : ℕ) x.inner.r with h | h | h
  · rw [stasheffDegOut_of_lt _ _ _ (x.outer.embedding x.block ⟨i, by omega⟩)
      (by simp only [Composition.coe_embedding]; omega)
      (by simp only [Composition.coe_embedding]; omega),
      stasheffDegOut_of_lt _ _ _ ⟨i, by omega⟩ (by simpa using h) rfl]
  · rw [stasheffDegOut_of_eq _ _ _ (by simp only [Composition.coe_embedding]; omega),
      stasheffDegOut_of_eq _ _ _ (by simpa using h), x.stasheffInnerDeg_eq]
  · rw [stasheffDegOut_of_gt _ _ _ (x.outer.embedding x.block ⟨i + x.inner.s - 1, by omega⟩)
      (by simp only [Composition.coe_embedding]; omega)
      (by simp only [Composition.coe_embedding]; omega),
      stasheffDegOut_of_gt _ _ _ ⟨i + x.inner.s - 1, by omega⟩ (by simpa using h) (by simp)]

/-- On the block of the inner operation, the degree of the value of `F` in the term indexed by
`x` is the degree of the inner operation on the corresponding block of `x.outer`. -/
lemma functorTargetDeg_stasheffDegOut_embedding_of_eq (l : Fin x.composition.length)
    (hl : (l : ℕ) = x.block) :
    functorTargetDeg (fun i ↦ stasheffDegOut deg x.stasheff (x.composition.embedding l i)) =
      operationTargetDeg (fun i ↦ deg (x.outer.embedding x.block i)) := by
  have e := x.blocksFun_of_eq l hl
  rw [← functorTargetDeg_stasheffDegOut _ x.inner]
  exact functorTargetDeg_congr e (x.stasheffDegOut_embedding_of_eq deg l hl e)

/-- The input degrees of the outer component of `G` in the term indexed by `x`, translated along
a grading homomorphism `φ`: the degrees of the values of `F` on the blocks of `x.outer`, except
on the block of the inner operation, whose degree is raised by one. -/
lemma degMap_functorTargetDeg_eq_update {β' : Type*} [AddCommGroup β'] [Grading β']
    (φ : β →+ᵍ β') (l : Fin x.composition.length) :
    φ (functorTargetDeg fun i ↦ stasheffDegOut deg x.stasheff (x.composition.embedding l i)) =
      Function.update (fun l ↦ φ (functorTargetDeg fun i ↦ deg (x.outer.embedding l i)))
        x.block (φ (operationTargetDeg fun i ↦ deg (x.outer.embedding x.block i)))
        (l.cast x.length_eq) := by
  by_cases hl : (l : ℕ) = x.block
  · rw [show l.cast x.length_eq = x.block from Fin.ext hl, Function.update_self]
    exact congrArg φ (x.functorTargetDeg_stasheffDegOut_embedding_of_eq deg l hl)
  · rw [Function.update_of_ne (fun h ↦ hl (by simpa using congrArg Fin.val h))]
    exact congrArg φ (x.functorTargetDeg_stasheffDegOut_embedding_of_ne deg l hl)

end Degrees

/-! #### Positions of objects -/

/-- The boundaries of `x.composition`, as positions of objects of the outer operation of
`x.stasheff`, are the boundaries of `x.outer`. -/
lemma outerBoundary_boundary (k : Fin (x.composition.length + 1)) :
    x.stasheff.outerBoundary (x.composition.boundary k) =
      x.outer.boundary (k.cast (by rw [x.length_eq])) :=
  Fin.ext (by
    simpa [StasheffIndex.val_outerBoundary, Composition.boundary] using x.outerBoundary_sizeUpTo k)

/-- On the block of the inner operation, the objects of the value of `F` in the term indexed by
`x` are those of the outer operation of the term indexed by `x.inner`. -/
lemma compositionBlockObj_stasheffObjOut_of_eq {T : Type*} (Z : Fin (n + 1) → T)
    (l : Fin x.composition.length) (hl : (l : ℕ) = x.block)
    (e : x.composition.blocksFun l = x.inner.r + 1 + x.inner.t)
    (i : Fin (x.composition.blocksFun l + 1)) :
    compositionBlockObj (stasheffObjOut Z x.stasheff) x.composition l i =
      stasheffObjOut (compositionBlockObj Z x.outer x.block) x.inner (i.cast (by rw [e])) := by
  have := x.sizeUpTo_of_eq l hl; have := x.r_eq; have := x.s_eq
  refine congrArg Z (Fin.ext ?_)
  simp only [StasheffIndex.val_outerBoundary, Fin.val_castLE, Fin.val_natAdd, Fin.val_cast]
  split_ifs <;> omega

section Inputs

variable {β β' : Type*} [AddCommGroup β] [Grading β] [AddCommGroup β'] [Grading β']
  {R : Type*} [Semiring R] {Obj Obj' : Type*} [AInfinityCategoryStruct β R Obj]
  [AInfinityCategoryStruct β' R Obj'] (F : AInfinityFunctorData β β' R Obj Obj')
  {X : Fin (n + 1) → Obj} {deg : Fin n → β} (a : ∀ i : Fin n, ComposableHom β R X i (deg i))

/-- The inner output of the term indexed by `x.stasheff` is the inner output of the term indexed
by `x.inner` on the block of the inner operation. -/
lemma stasheffInner_congr {d d' : β} (hd : stasheffInnerDeg deg x.stasheff = d)
    (hd' : stasheffInnerDeg (fun i ↦ deg (x.outer.embedding x.block i)) x.inner = d') :
    homCongr R (congrArg X (Fin.ext (by simp [x.r_eq])))
      (congrArg X (Fin.ext (by simp [x.r_eq, x.s_eq, add_assoc])))
      (hd.symm.trans ((x.stasheffInnerDeg_eq deg).trans hd')) (stasheffInner a x.stasheff d hd) =
      stasheffInner (X := compositionBlockObj X x.outer x.block)
        (fun i ↦ a (x.outer.embedding x.block i)) x.inner d' hd' :=
  AInfinityTheory.stasheffInner_congr x.stasheff a (X' := compositionBlockObj X x.outer x.block)
    (fun i ↦ a (x.outer.embedding x.block i)) x.inner x.s_eq
    (fun u ↦ congrArg X (Fin.ext (by simp [x.r_eq, add_assoc])))
    (fun u ↦ congrArg deg (x.innerIndex_eq u)) (fun u ↦ homCongr_congrArg a (x.innerIndex_eq u))
    hd hd'

/-- On the block of the inner operation, the inputs of the outer operation of the term indexed
by `x.stasheff` are those of the outer operation of the term indexed by `x.inner`. -/
lemma homCongr_stasheffInputsOut_embedding_of_eq (l : Fin x.composition.length)
    (hl : (l : ℕ) = x.block) (e : x.composition.blocksFun l = x.inner.r + 1 + x.inner.t)
    (i : Fin (x.composition.blocksFun l)) :
    homCongr R (x.compositionBlockObj_stasheffObjOut_of_eq X l hl e i.castSucc)
      (x.compositionBlockObj_stasheffObjOut_of_eq X l hl e i.succ)
      (x.stasheffDegOut_embedding_of_eq deg l hl e i)
      (stasheffInputsOut a x.stasheff (x.composition.embedding l i)) =
      stasheffInputsOut (X := compositionBlockObj X x.outer x.block)
        (fun i ↦ a (x.outer.embedding x.block i)) x.inner (i.cast e) := by
  have := x.sizeUpTo_of_eq l hl; have := x.r_eq; have := x.s_eq; have := x.inner.sum_eq
  have := x.inner.one_le_s; have := i.2
  rcases lt_trichotomy (i : ℕ) x.inner.r with h | h | h
  · exact homCongr_eq_trans (homCongr_stasheffInputsOut_of_lt x.stasheff a
      (x.composition.embedding l i)
      (x.outer.embedding x.block ⟨i, by omega⟩) (by simp only [Composition.coe_embedding]; omega)
      (by simp only [Composition.coe_embedding]; omega)) (homCongr_eq_symm
        (homCongr_stasheffInputsOut_of_lt x.inner (X := compositionBlockObj X x.outer x.block)
          (fun i ↦ a (x.outer.embedding x.block i)) (i.cast e) ⟨i, by omega⟩ (by simpa using h)
          rfl))
  · exact homCongr_eq_trans (homCongr_eq_trans (homCongr_stasheffInputsOut_of_eq x.stasheff a
      (x.composition.embedding l i)
      (by simp only [Composition.coe_embedding]; omega) rfl) (x.stasheffInner_congr a rfl rfl))
      (homCongr_eq_symm (homCongr_stasheffInputsOut_of_eq x.inner
        (X := compositionBlockObj X x.outer x.block) (fun i ↦ a (x.outer.embedding x.block i))
        (i.cast e) (by simpa using h) rfl))
  · exact homCongr_eq_trans (homCongr_stasheffInputsOut_of_gt x.stasheff a
      (x.composition.embedding l i)
      (x.outer.embedding x.block ⟨i + x.inner.s - 1, by omega⟩)
      (by simp only [Composition.coe_embedding]; omega)
      (by simp only [Composition.coe_embedding]; omega)) (homCongr_eq_symm
        (homCongr_stasheffInputsOut_of_gt x.inner (X := compositionBlockObj X x.outer x.block)
          (fun i ↦ a (x.outer.embedding x.block i)) (i.cast e) ⟨i + x.inner.s - 1, by omega⟩
          (by simpa using h) (by simp)))

/-- On a block other than the one of the inner operation, the value of `F` in the term indexed
by `x` is the value of `F` on the corresponding block of `x.outer`. -/
lemma homCongr_compositionBlockMap_of_ne (l : Fin x.composition.length)
    (hl : (l : ℕ) ≠ x.block) :
    homCongr R (congrArg (fun z ↦ F.obj (X z)) (x.outerBoundary_boundary l.castSucc))
      (congrArg (fun z ↦ F.obj (X z)) (x.outerBoundary_boundary l.succ))
      (congrArg F.degMap (x.functorTargetDeg_stasheffDegOut_embedding_of_ne deg l hl))
      (F.compositionBlockMap (stasheffInputsOut a x.stasheff) x.composition l) =
      F.compositionBlockMap a x.outer (l.cast x.length_eq) := by
  have := x.stasheff.one_le_s
  rcases x.block_cases l with ⟨-, hs, hb, hle⟩ | ⟨h, -⟩ | ⟨-, hs, hb, hlt⟩
  · refine F.compositionBlockMap_congr (stasheffInputsOut a x.stasheff) a hb
      (fun i ↦ congrArg X (Fin.ext ?_))
      (fun i ↦ stasheffDegOut_of_lt _ _ _ _
        (by have := i.2; simp only [Composition.coe_embedding]; omega)
        (by simp only [Composition.coe_embedding, Fin.val_cast]; omega))
      (fun i ↦ homCongr_stasheffInputsOut_of_lt x.stasheff a (x.composition.embedding l i)
        (x.outer.embedding (l.cast x.length_eq) (i.cast hb))
        (by have := i.2; simp only [Composition.coe_embedding]; omega)
        (by simp only [Composition.coe_embedding, Fin.val_cast]; omega))
    have := i.2
    simp only [StasheffIndex.val_outerBoundary, Fin.val_castLE, Fin.val_natAdd, Fin.val_cast]
    split_ifs <;> omega
  · exact absurd h hl
  · refine F.compositionBlockMap_congr (stasheffInputsOut a x.stasheff) a hb
      (fun i ↦ congrArg X (Fin.ext ?_))
      (fun i ↦ stasheffDegOut_of_gt _ _ _ _ (by simp only [Composition.coe_embedding]; omega)
        (by simp only [Composition.coe_embedding, Fin.val_cast]; omega))
      (fun i ↦ homCongr_stasheffInputsOut_of_gt x.stasheff a (x.composition.embedding l i)
        (x.outer.embedding (l.cast x.length_eq) (i.cast hb))
        (by simp only [Composition.coe_embedding]; omega)
        (by simp only [Composition.coe_embedding, Fin.val_cast]; omega))
    simp only [StasheffIndex.val_outerBoundary, Fin.val_castLE, Fin.val_natAdd, Fin.val_cast]
    split_ifs <;> omega

/-- On the block of the inner operation, the value of `F` in the term indexed by `x` is the term
indexed by `x.inner` of the left-hand side of the functor equation of `F` on that block. -/
lemma homCongr_compositionBlockMap_of_eq (l : Fin x.composition.length)
    (hl : (l : ℕ) = x.block) :
    homCongr R (congrArg (fun z ↦ F.obj (X z))
        ((x.outerBoundary_boundary l.castSucc).trans
          (congrArg x.outer.boundary (Fin.ext hl : l.castSucc.cast _ = x.block.castSucc))))
      (congrArg (fun z ↦ F.obj (X z)) ((x.outerBoundary_boundary l.succ).trans
        (congrArg x.outer.boundary (Fin.ext (by simp [hl]) : l.succ.cast _ = x.block.succ))))
      (congrArg F.degMap (x.functorTargetDeg_stasheffDegOut_embedding_of_eq deg l hl))
      (F.compositionBlockMap (stasheffInputsOut a x.stasheff) x.composition l) =
      F.compositionBlockMapCompTerm a x.outer x.block x.inner := by
  have e := x.blocksFun_of_eq l hl
  refine (homCongr_homCongr _ _ _ _ _ _ _).trans ((homCongr_eq_homCongr_of_eq
    (F.map_v_congr e (x.compositionBlockObj_stasheffObjOut_of_eq X l hl e)
      (x.stasheffDegOut_embedding_of_eq deg l hl e) _ _ fun i ↦ ?_)).trans
    (homCongr_homCongr _ _ _ _ _ _ _).symm)
  exact x.homCongr_stasheffInputsOut_embedding_of_eq a l hl e i

/-- The inputs of the outer component of `G` in the term indexed by `x`: the values of `F` on the
blocks of `x.outer`, with the value on the block of the inner operation replaced by the term
indexed by `x.inner` of the left-hand side of the functor equation of `F` on it. -/
lemma homCongr_compositionBlockMap_eq_updateComposableHom (l : Fin x.composition.length) :
    homCongr R (congrArg (fun z ↦ F.obj (X z)) (x.outerBoundary_boundary l.castSucc))
      (congrArg (fun z ↦ F.obj (X z)) (x.outerBoundary_boundary l.succ))
      (x.degMap_functorTargetDeg_eq_update deg F.degMap l)
      (F.compositionBlockMap (stasheffInputsOut a x.stasheff) x.composition l) =
      updateComposableHom (F.compositionBlockMap a x.outer) x.block
        (F.compositionBlockMapCompTerm a x.outer x.block x.inner) (l.cast x.length_eq) := by
  by_cases hl : (l : ℕ) = x.block
  · exact homCongr_eq_trans (x.homCongr_compositionBlockMap_of_eq F a l hl)
      (homCongr_eq_symm (homCongr_updateComposableHom_of_eq (F.compositionBlockMap a x.outer)
        (Fin.ext hl : l.cast x.length_eq = x.block)
        (F.compositionBlockMapCompTerm a x.outer x.block x.inner)))
  · exact homCongr_eq_trans (x.homCongr_compositionBlockMap_of_ne F a l hl)
      (homCongr_eq_symm (homCongr_updateComposableHom_of_ne (F.compositionBlockMap a x.outer)
        (fun h ↦ hl (by simpa using congrArg Fin.val h) : l.cast x.length_eq ≠ x.block)
        (F.compositionBlockMapCompTerm a x.outer x.block x.inner)))

end Inputs

variable {β β' β'' : Type*} [AddCommGroup β] [Grading β] [AddCommGroup β'] [Grading β']
  [AddCommGroup β''] [Grading β''] {R : Type*} [Semiring R] {Obj Obj' Obj'' : Type*}
  [AInfinityCategoryStruct β R Obj] [AInfinityCategoryStruct β' R Obj']
  [AInfinityCategoryStruct β'' R Obj'']
  (G : AInfinityFunctorData β' β'' R Obj' Obj'') (F : AInfinityFunctorData β β' R Obj Obj')
  {X : Fin (n + 1) → Obj} {deg : Fin n → β} (a : ∀ i : Fin n, ComposableHom β R X i (deg i))
  (d : β) (hd : operationTargetDeg deg = d) [NeZero n]

/-- The two descriptions of a term of the left-hand side of the functor equation for `G.comp F`
agree: the summand indexed by `x.stasheff` and `x.composition` is the component of `G` applied
to the values of `F` on the blocks of `x.outer`, with the value on the block `x.block` replaced
by the term indexed by `x.inner` of the left-hand side of the functor equation of `F` on it. -/
theorem compMapCompTerm_eq_compMapBlockUpdate :
    G.compMapCompTerm F a d hd x.stasheff x.composition =
      G.compMapBlockUpdate F a x.outer x.block d hd
        (F.compositionBlockMapCompTerm a x.outer x.block x.inner) := by
  rw [compMapBlockUpdate_apply]
  refine homCongr_eq_homCongr_of_eq (G.map_v_congr x.length_eq
    (Y' := fun k ↦ F.obj (X (x.outer.boundary k)))
    (fun k ↦ congrArg (fun z ↦ F.obj (X z)) (x.outerBoundary_boundary k))
    (x.degMap_functorTargetDeg_eq_update deg F.degMap) _ _ fun l ↦ ?_)
  exact x.homCongr_compositionBlockMap_eq_updateComposableHom F a l

end MapCompIndex

/-! ### The terms of the functor equation for `G` on the values of `F` -/

namespace CompMapIndex

open AInfinityFunctorData

variable (x : CompMapIndex n)

/-! #### Positions of objects and inputs -/

/-- The object string of the outer component of `G` in the term indexed by `x`: the boundaries of
`x.composition` at the positions of the objects of the outer operation of `x.stasheff` are the
boundaries of `x.outer`. -/
lemma boundary_outerBoundary (k : Fin (x.stasheff.r + 1 + x.stasheff.t + 1)) :
    x.composition.boundary (x.stasheff.outerBoundary k) =
      x.outer.boundary (k.cast (by rw [x.length_eq])) :=
  Fin.ext (by
    simpa [StasheffIndex.val_outerBoundary, Composition.boundary] using x.sizeUpTo_outerBoundary k)

/-- The objects of the inner operation of the term indexed by `x` are those of the merged block,
at the boundaries of `x.inner`. -/
lemma boundary_innerBoundary_eq_compositionBlockObj {T : Type*} (Z : Fin (n + 1) → T)
    (u : Fin (x.stasheff.s + 1)) :
    Z (x.composition.boundary (x.stasheff.innerBoundary u)) =
      compositionBlockObj Z x.outer x.block (x.inner.boundary (u.cast (by rw [x.s_eq]))) := by
  have := x.s_eq
  exact congrArg Z
    (Fin.ext (by simpa [Composition.boundary, x.r_eq] using x.sizeUpTo_add u (by omega)))

lemma boundary_innerBoundary_zero :
    x.composition.boundary (x.stasheff.innerBoundary 0) = x.outer.boundary x.block.castSucc :=
  by simpa using x.boundary_innerBoundary_eq_compositionBlockObj id 0

lemma boundary_innerBoundary_last :
    x.composition.boundary (x.stasheff.innerBoundary (Fin.last _)) =
      x.outer.boundary x.block.succ :=
  by simpa using x.boundary_innerBoundary_eq_compositionBlockObj id (Fin.last _)

variable {β β' β'' : Type*} [AddCommGroup β] [Grading β] [AddCommGroup β'] [Grading β']
  [AddCommGroup β''] [Grading β''] {R : Type*} [Semiring R] {Obj Obj' Obj'' : Type*}

/-- The blocks of `x.composition` inside the merged block are the blocks of `x.inner`, so their
values under the components of A∞-functor data have the same degrees. -/
lemma functorTargetDeg_embedding_innerIndex (deg : Fin n → β) (u : Fin x.stasheff.s) :
    functorTargetDeg (fun i ↦ deg (x.composition.embedding (x.stasheff.innerIndex u) i)) =
      functorTargetDeg
        (fun i ↦ deg (x.outer.embedding x.block (x.inner.embedding (u.cast x.s_eq) i))) :=
  functorTargetDeg_congr (x.blocksFun_innerIndex u) fun i ↦ congrArg deg
    (Composition.embedding_eq_embedding_embedding (x.sizeUpTo_innerIndex u)
      (x.blocksFun_innerIndex u) i)

section Inputs

variable [AInfinityCategoryStruct β R Obj] [AInfinityCategoryStruct β' R Obj']
  (F : AInfinityFunctorData β β' R Obj Obj') {X : Fin (n + 1) → Obj} {deg : Fin n → β}
  (a : ∀ i : Fin n, ComposableHom β R X i (deg i))

/-- The degree of the inner operation of the term indexed by `x` is the degree of the term
indexed by `x.inner` of the right-hand side of the functor equation of `F` on the merged
block. -/
lemma stasheffInnerDeg_degMap_eq :
    stasheffInnerDeg (fun l ↦ F.degMap (functorTargetDeg fun i ↦
      deg (x.composition.embedding l i))) x.stasheff =
      F.degMap (operationTargetDeg fun i ↦ deg (x.outer.embedding x.block i)) := by
  rw [← F.operationTargetDeg_degMap_functorTargetDeg_embedding x.inner _ rfl]
  exact operationTargetDeg_congr x.s_eq fun u ↦
    congrArg F.degMap (x.functorTargetDeg_embedding_innerIndex deg u)

/-- The input degrees of the outer component of `G` in the term indexed by `x`: the degrees of
the values of `F` on the blocks of `x.outer`, except on the merged block, whose degree is the
one of the inner operation. -/
lemma stasheffDegOut_eq_update (l : Fin (x.stasheff.r + 1 + x.stasheff.t)) :
    stasheffDegOut (fun l ↦ F.degMap (functorTargetDeg fun i ↦ deg (x.composition.embedding l i)))
        x.stasheff l =
      Function.update (fun l ↦ F.degMap (functorTargetDeg fun i ↦ deg (x.outer.embedding l i)))
        x.block (F.degMap (operationTargetDeg fun i ↦ deg (x.outer.embedding x.block i)))
        (l.cast x.length_eq) := by
  have := x.r_eq; have := x.s_eq; have := l.2; have := x.length_eq; have := x.stasheff.sum_eq
  rcases lt_trichotomy (l : ℕ) x.stasheff.r with h | h | h
  · obtain ⟨hs, e⟩ := x.sizeUpTo_blocksFun_of_ne l ⟨l, by omega⟩ (by omega) (by simp [h])
    rw [stasheffDegOut_of_lt _ _ _ ⟨l, by omega⟩ h rfl,
      Function.update_of_ne (Fin.ne_of_val_ne (by simp only [Fin.val_cast, ne_eq]; omega))]
    exact congrArg F.degMap (functorTargetDeg_congr e fun i ↦
      congrArg deg (Composition.embedding_eq_of_sizeUpTo_eq hs e i))
  · rw [stasheffDegOut_of_eq _ _ _ h,
      show l.cast x.length_eq = x.block from Fin.ext (by simp only [Fin.val_cast]; omega),
      Function.update_self]
    exact x.stasheffInnerDeg_degMap_eq F
  · obtain ⟨hs, e⟩ := x.sizeUpTo_blocksFun_of_ne l ⟨l + x.stasheff.s - 1, by omega⟩ (by omega)
      (by simp only [right_eq_ite_iff]; omega)
    rw [stasheffDegOut_of_gt _ _ _ ⟨l + x.stasheff.s - 1, by omega⟩ h rfl,
      Function.update_of_ne (Fin.ne_of_val_ne (by simp only [Fin.val_cast, ne_eq]; omega))]
    exact congrArg F.degMap (functorTargetDeg_congr e fun i ↦
      congrArg deg (Composition.embedding_eq_of_sizeUpTo_eq hs e i))

/-- The inner operation of the term indexed by `x`, applied to the values of `F` on the blocks of
`x.composition`, is the term indexed by `x.inner` of the right-hand side of the functor equation of
`F` on the merged block. -/
lemma homCongr_stasheffInner {d : β'}
    (hd : stasheffInnerDeg (fun l ↦ F.degMap (functorTargetDeg fun i ↦
      deg (x.composition.embedding l i))) x.stasheff = d) :
    homCongr R (congrArg (fun z ↦ F.obj (X z)) x.boundary_innerBoundary_zero)
      (congrArg (fun z ↦ F.obj (X z)) x.boundary_innerBoundary_last)
      (hd.symm.trans (x.stasheffInnerDeg_degMap_eq F))
      (stasheffInner (F.compositionBlockMap a x.composition) x.stasheff d hd) =
      F.compositionBlockCompMapTerm a x.outer x.block x.inner := by
  refine (homCongr_eq_homCongr_of_eq (AInfinityCategoryStruct.m_v_congr x.s_eq
    (Y' := fun k ↦ F.obj (compositionBlockObj X x.outer x.block (x.inner.boundary k)))
    (x.boundary_innerBoundary_eq_compositionBlockObj fun z ↦ F.obj (X z))
    (fun u ↦ congrArg F.degMap (x.functorTargetDeg_embedding_innerIndex deg u)) hd _
    fun u ↦ ?_)).trans (homCongr_homCongr _ _ _ _ _ _ _).symm
  exact F.compositionBlockMap_congr_compositionBlockMap_embedding a (x.sizeUpTo_innerIndex u)
    (x.blocksFun_innerIndex u)

/-- The inputs of the outer component of `G` in the term indexed by `x`: the values of `F` on the
blocks of `x.outer`, with the value on the merged block replaced by the term indexed by `x.inner`
of the right-hand side of the functor equation of `F` on it. -/
lemma homCongr_stasheffInputsOut_eq_updateComposableHom
    (l : Fin (x.stasheff.r + 1 + x.stasheff.t)) :
    homCongr R (congrArg (fun z ↦ F.obj (X z)) (x.boundary_outerBoundary l.castSucc))
      (congrArg (fun z ↦ F.obj (X z)) (x.boundary_outerBoundary l.succ))
      (x.stasheffDegOut_eq_update F l)
      (stasheffInputsOut (F.compositionBlockMap a x.composition) x.stasheff l) =
      updateComposableHom (F.compositionBlockMap a x.outer) x.block
        (F.compositionBlockCompMapTerm a x.outer x.block x.inner) (l.cast x.length_eq) := by
  have := x.r_eq; have := x.s_eq; have := l.2; have := x.length_eq; have := x.stasheff.sum_eq
  have hne : (l : ℕ) ≠ x.stasheff.r → l.cast x.length_eq ≠ x.block := fun h ↦
    Fin.ne_of_val_ne (by simp only [Fin.val_cast, ne_eq]; omega)
  rcases lt_trichotomy (l : ℕ) x.stasheff.r with h | h | h
  · obtain ⟨hs, e⟩ := x.sizeUpTo_blocksFun_of_ne l ⟨l, by omega⟩ (by omega) (by simp [h])
    exact homCongr_eq_trans (homCongr_eq_trans (homCongr_stasheffInputsOut_of_lt x.stasheff
      (F.compositionBlockMap a x.composition) l ⟨l, by omega⟩ h rfl)
      (F.compositionBlockMap_congr_of_sizeUpTo_eq a hs e)) (homCongr_eq_symm
        (homCongr_updateComposableHom_of_ne (F.compositionBlockMap a x.outer) (hne h.ne) _))
  · exact homCongr_eq_trans (homCongr_eq_trans (homCongr_stasheffInputsOut_of_eq x.stasheff
      (F.compositionBlockMap a x.composition) l h rfl) (x.homCongr_stasheffInner F a rfl))
      (homCongr_eq_symm (homCongr_updateComposableHom_of_eq (F.compositionBlockMap a x.outer)
        (Fin.ext (by simp only [Fin.val_cast]; omega) : l.cast x.length_eq = x.block)
        (F.compositionBlockCompMapTerm a x.outer x.block x.inner)))
  · obtain ⟨hs, e⟩ := x.sizeUpTo_blocksFun_of_ne l ⟨l + x.stasheff.s - 1, by omega⟩ (by omega)
      (by simp only [right_eq_ite_iff]; omega)
    exact homCongr_eq_trans (homCongr_eq_trans (homCongr_stasheffInputsOut_of_gt x.stasheff
      (F.compositionBlockMap a x.composition) l ⟨l + x.stasheff.s - 1, by omega⟩ h rfl)
      (F.compositionBlockMap_congr_of_sizeUpTo_eq a hs e)) (homCongr_eq_symm
        (homCongr_updateComposableHom_of_ne (F.compositionBlockMap a x.outer) (hne h.ne') _))

end Inputs

variable [AInfinityCategoryStruct β R Obj] [AInfinityCategoryStruct β' R Obj']
  [AInfinityCategoryStruct β'' R Obj'']
  (G : AInfinityFunctorData β' β'' R Obj' Obj'') (F : AInfinityFunctorData β β' R Obj Obj')
  {X : Fin (n + 1) → Obj} {deg : Fin n → β} (a : ∀ i : Fin n, ComposableHom β R X i (deg i))
  (d : β) (hd : operationTargetDeg deg = d) [NeZero n]

/-- The two descriptions of a term of the left-hand side of the functor equation for `G` on the
values of `F` agree: the term indexed by `x.stasheff` on the values of `F` on the blocks of
`x.composition` is the component of `G` applied to the values of `F` on the blocks of `x.outer`,
with the value on the block `x.block` replaced by the term indexed by `x.inner` of the
right-hand side of the functor equation of `F` on it. -/
theorem mapCompTermBlockMap_eq_compMapBlockUpdate :
    G.mapCompTermBlockMap F a x.composition d hd x.stasheff =
      G.compMapBlockUpdate F a x.outer x.block d hd
        (F.compositionBlockCompMapTerm a x.outer x.block x.inner) := by
  rw [compMapBlockUpdate_apply]
  refine (homCongr_homCongr _ _ _ _ _ _ _).trans (homCongr_eq_homCongr_of_eq (G.map_v_congr
    x.length_eq (Y' := fun k ↦ F.obj (X (x.outer.boundary k)))
    (fun k ↦ congrArg (fun z ↦ F.obj (X z)) (x.boundary_outerBoundary k))
    (x.stasheffDegOut_eq_update F) _ _ fun l ↦ ?_))
  exact x.homCongr_stasheffInputsOut_eq_updateComposableHom F a l

end CompMapIndex

/-! ### The terms of the right-hand side of the functor equation for `G.comp F` -/

namespace AInfinityFunctorData

variable {β β' β'' : Type*} [AddCommGroup β] [Grading β] [AddCommGroup β'] [Grading β']
  [AddCommGroup β''] [Grading β''] {R : Type*} [Semiring R] {Obj Obj' Obj'' : Type*}
  [AInfinityCategoryStruct β R Obj] [AInfinityCategoryStruct β' R Obj']
  [AInfinityCategoryStruct β'' R Obj'']
variable (G : AInfinityFunctorData β' β'' R Obj' Obj'') (F : AInfinityFunctorData β β' R Obj Obj')
  {X : Fin (n + 1) → Obj} {deg : Fin n → β} (a : ∀ i : Fin n, ComposableHom β R X i (deg i))

/-- The term, indexed by a composition `c` of the `l`-th block of a composition `e` of `n`, of the
value of the composite component (G ∘ F) on that block: the component of `G` of arity `c.length`
applied to the values of the components of `F` on the blocks of `c`, as the `l`-th input of an
outer operation on the objects `G (F (X (e.boundary k)))`. -/
def compositionBlockCompTerm (e : Composition n) (l : Fin e.length)
    (c : Composition (e.blocksFun l)) :
    ComposableHom β'' R (fun k ↦ (G.comp F).obj (X (e.boundary k))) l
      ((G.comp F).degMap (functorTargetDeg fun j ↦ deg (e.embedding l j))) :=
  homCongr R (congrArg (G.comp F).obj (compositionBlockObj_zero X e l))
    (congrArg (G.comp F).obj (compositionBlockObj_last X e l)) rfl
    (compMapTermMultilinearMap G F (compositionBlockObj X e l) (fun j ↦ deg (e.embedding l j)) c
      _ rfl fun j ↦ a (e.embedding l j))

lemma comp_compositionBlockMap_eq_sum (e : Composition n) (l : Fin e.length) :
    (G.comp F).compositionBlockMap a e l = ∑ c, G.compositionBlockCompTerm F a e l c :=
  (congrArg (homCongr R (congrArg (G.comp F).obj (compositionBlockObj_zero X e l))
    (congrArg (G.comp F).obj (compositionBlockObj_last X e l)) rfl)
    (sum_apply Finset.univ (fun c ↦ compMapTermMultilinearMap G F (compositionBlockObj X e l)
      (fun j ↦ deg (e.embedding l j)) c _ rfl) fun j ↦ a (e.embedding l j))).trans (map_sum _ _ _)

variable [NeZero n] (d : β) (hd : operationTargetDeg deg = d)

/-- The summand, indexed by compositions `τ l` of the blocks of a composition `e` of `n`, of the
term indexed by `e` of the right-hand side of the functor equation for `G.comp F`: the operation
of arity `e.length` applied to the components of `G` on the values of the components of `F` on the
blocks of the compositions `τ l`. -/
def compCompMapTerm (e : Composition n) (τ : ∀ l : Fin e.length, Composition (e.blocksFun l)) :
    ((G.comp F).obj (X 0) →ᵍ[R] (G.comp F).obj (X (Fin.last n))) ((G.comp F).degMap d) :=
  homCongr R (congrArg (fun k ↦ (G.comp F).obj (X k)) e.boundary_zero)
    (congrArg (fun k ↦ (G.comp F).obj (X k)) e.boundary_last) rfl
    ((AInfinityCategoryStruct.m fun k ↦ (G.comp F).obj (X (e.boundary k))).v
      (fun l ↦ (G.comp F).degMap (functorTargetDeg fun j ↦ deg (e.embedding l j)))
      ((G.comp F).degMap d) ((G.comp F).operationTargetDeg_degMap_functorTargetDeg_embedding e d hd)
      fun l ↦ G.compositionBlockCompTerm F a e l (τ l))

lemma comp_compMapTerm_eq_sum (e : Composition n) :
    (G.comp F).compMapTerm a e d hd = ∑ τ, G.compCompMapTerm F a d hd e τ := by
  rw [compMapTerm, funext (G.comp_compositionBlockMap_eq_sum F a e), MultilinearMap.map_sum,
    map_sum]
  rfl

end AInfinityFunctorData

namespace CompMapMapIndex

open AInfinityFunctorData

variable (x : CompMapMapIndex n)

/-- The object string of the outer operation in the term indexed by `x`: the boundaries of
`x.composition` at the boundaries of `x.grouping` are the boundaries of `x.outer`. -/
lemma boundary_boundary (k : Fin (x.grouping.length + 1)) :
    x.composition.boundary (x.grouping.boundary k) =
      x.outer.boundary (k.cast (by rw [x.length_eq])) :=
  Fin.ext (by simpa [Composition.boundary] using x.sizeUpTo_sizeUpTo k)

lemma functorTargetDeg_embedding_eq {β : Type*} [AddCommGroup β] [Grading β] (deg : Fin n → β)
    (l : Fin x.grouping.length) (j : Fin (x.grouping.blocksFun l)) :
    functorTargetDeg (fun i ↦ deg (x.composition.embedding (x.grouping.embedding l j) i)) =
      functorTargetDeg (fun i ↦ deg (x.outer.embedding (l.cast x.length_eq)
        ((x.inner (l.cast x.length_eq)).embedding (j.cast (x.length_inner l).symm) i))) :=
  functorTargetDeg_congr (x.blocksFun_embedding l j) fun i ↦ congrArg deg
    (Composition.embedding_eq_embedding_embedding (x.sizeUpTo_embedding l j)
      (x.blocksFun_embedding l j) i)

variable {β β' β'' : Type*} [AddCommGroup β] [Grading β] [AddCommGroup β'] [Grading β']
  [AddCommGroup β''] [Grading β''] {R : Type*} [Semiring R] {Obj Obj' Obj'' : Type*}
  [AInfinityCategoryStruct β R Obj] [AInfinityCategoryStruct β' R Obj']
  [AInfinityCategoryStruct β'' R Obj'']
variable (G : AInfinityFunctorData β' β'' R Obj' Obj'') (F : AInfinityFunctorData β β' R Obj Obj')
  {X : Fin (n + 1) → Obj} {deg : Fin n → β} (a : ∀ i : Fin n, ComposableHom β R X i (deg i))

/-- The input degrees of the outer operation in the term indexed by `x`, before translation along
`G.degMap`: the degree of the value of `G` on the values of `F` on the blocks of `x.composition`
grouped by `x.grouping` is the degree of the value of `G.comp F` on the corresponding block of
`x.outer`. -/
lemma functorTargetDeg_degMap_eq (l : Fin x.grouping.length) :
    functorTargetDeg (fun j ↦ F.degMap (functorTargetDeg fun i ↦
      deg (x.composition.embedding (x.grouping.embedding l j) i))) =
      F.degMap (functorTargetDeg fun i ↦ deg (x.outer.embedding (l.cast x.length_eq) i)) := by
  rw [← F.functorTargetDeg_degMap_functorTargetDeg_embedding
    (deg := fun i ↦ deg (x.outer.embedding (l.cast x.length_eq) i))
    (x.inner (l.cast x.length_eq)) _ rfl]
  exact functorTargetDeg_congr (x.length_inner l).symm fun j ↦
    congrArg F.degMap (x.functorTargetDeg_embedding_eq deg l j)

/-- The `l`-th input of the outer operation in the term indexed by `x`: the value of `G` on the
values of `F` on the blocks of `x.composition` grouped by `x.grouping` is the term indexed by
`x.inner` of the value of `G.comp F` on the corresponding block of `x.outer`. -/
lemma homCongr_compositionBlockMap_eq_compositionBlockCompTerm (l : Fin x.grouping.length) :
    homCongr R (congrArg (fun z ↦ G.obj (F.obj (X z))) (x.boundary_boundary l.castSucc))
      (congrArg (fun z ↦ G.obj (F.obj (X z))) (x.boundary_boundary l.succ))
      (congrArg G.degMap (x.functorTargetDeg_degMap_eq F l))
      (G.compositionBlockMap (F.compositionBlockMap a x.composition) x.grouping l) =
      G.compositionBlockCompTerm F a x.outer (l.cast x.length_eq)
        (x.inner (l.cast x.length_eq)) := by
  refine (homCongr_homCongr _ _ _ _ _ _ _).trans ((homCongr_eq_homCongr_of_eq
    (G.map_v_congr (x.length_inner l).symm
      (Y := compositionBlockObj (fun k ↦ F.obj (X (x.composition.boundary k))) x.grouping l)
      (Y' := fun k ↦ F.obj (compositionBlockObj X x.outer (l.cast x.length_eq)
        ((x.inner (l.cast x.length_eq)).boundary k)))
      (fun k ↦ congrArg F.obj (congrArg X (Fin.ext ?_)))
      (fun j ↦ congrArg F.degMap (x.functorTargetDeg_embedding_eq deg l j)) _ _
      fun j ↦ ?_)).trans (homCongr_homCongr _ _ _ _ _ _ _).symm)
  · simpa [Composition.boundary, compositionBlockObj] using
      x.sizeUpTo_add l k (Nat.lt_succ_iff.mp k.2)
  · exact F.compositionBlockMap_congr_compositionBlockMap_embedding a (x.sizeUpTo_embedding l j)
      (x.blocksFun_embedding l j)

variable [NeZero n] (d : β) (hd : operationTargetDeg deg = d)

/-- The two descriptions of a term of the right-hand side of the functor equation for `G.comp F`
agree: the term indexed by `x.grouping` of the right-hand side of the functor equation for `G` on
the values of `F` on the blocks of `x.composition` is the summand indexed by `x.inner` of the term
indexed by `x.outer` of the right-hand side of the functor equation for `G.comp F`. -/
theorem compMapTermBlockMap_eq_compCompMapTerm :
    G.compMapTermBlockMap F a x.composition d hd x.grouping =
      G.compCompMapTerm F a d hd x.outer x.inner := by
  refine (homCongr_homCongr _ _ _ _ _ _ _).trans (homCongr_eq_homCongr_of_eq
    (AInfinityCategoryStruct.m_v_congr x.length_eq
      (Y' := fun k ↦ (G.comp F).obj (X (x.outer.boundary k)))
      (fun k ↦ congrArg (fun z ↦ G.obj (F.obj (X z))) (x.boundary_boundary k))
      (fun l ↦ congrArg G.degMap (x.functorTargetDeg_degMap_eq F l)) _ _ fun l ↦ ?_))
  exact x.homCongr_compositionBlockMap_eq_compositionBlockCompTerm G F a l

end CompMapMapIndex

/-! ### Reindexing -/

namespace AInfinityFunctorData

variable {β β' β'' : Type*} [AddCommGroup β] [Grading β] [AddCommGroup β'] [Grading β']
  [AddCommGroup β''] [Grading β''] {R : Type*} [Semiring R] {Obj Obj' Obj'' : Type*}
  [AInfinityCategoryStruct β R Obj] [AInfinityCategoryStruct β' R Obj']
  [AInfinityCategoryStruct β'' R Obj'']
variable (G : AInfinityFunctorData β' β'' R Obj' Obj'') (F : AInfinityFunctorData β β' R Obj Obj')
  {X : Fin (n + 1) → Obj} {deg : Fin n → β} (a : ∀ i : Fin n, ComposableHom β R X i (deg i))
  (d : β) (hd : operationTargetDeg deg = d) [NeZero n]

/-- The left-hand side of the functor equation for `G.comp F`, regrouped by the composition of
`n` into the inputs of the outer component of `G` and the input containing the inner operation:
for each of them, the component of `G` is applied to the values of `F`, with the value on that
input replaced by the left-hand side of the functor equation of `F` on it. -/
theorem comp_mapCompSum_eq_sum_compMapBlockUpdate :
    (G.comp F).mapCompSum a d hd =
      ∑ c : Composition n, ∑ j : Fin c.length, tailSign deg (c.sizeUpTo (j + 1)) •
        G.compMapBlockUpdate F a c j d hd (signedStasheffSum (fun i ↦ deg (c.embedding j i))
          fun p ↦ F.compositionBlockMapCompTerm a c j p) := by
  show @Eq ((G.obj (F.obj (X 0)) →ᵍ[R] G.obj (F.obj (X (Fin.last n)))) (G.degMap (F.degMap d)))
    _ _
  calc _
      = ∑ σ : Σ q : StasheffIndex n, Composition (q.r + 1 + q.t),
          stasheffSign deg σ.1 • G.compMapCompTerm F a d hd σ.1 σ.2 := by
        simp only [mapCompSum, signedStasheffSum, comp_mapCompTerm_eq_sum, Fintype.sum_sigma]
        exact Finset.sum_congr rfl fun q _ ↦ Finset.smul_sum
    _ = ∑ x : MapCompIndex n,
          stasheffSign deg x.stasheff • G.compMapCompTerm F a d hd x.stasheff x.composition :=
        (Fintype.sum_bijective _ MapCompIndex.bijective_toSigma _ _ fun _ ↦ rfl).symm
    _ = ∑ x : MapCompIndex n, tailSign deg (x.outer.sizeUpTo (x.block + 1)) •
          stasheffSign (fun i ↦ deg (x.outer.embedding x.block i)) x.inner •
            G.compMapBlockUpdate F a x.outer x.block d hd
              (F.compositionBlockMapCompTerm a x.outer x.block x.inner) :=
        Finset.sum_congr rfl fun x _ ↦ by
          rw [x.compMapCompTerm_eq_compMapBlockUpdate, x.stasheffSign_eq, mul_comm, mul_smul]
    _ = ∑ σ : Σ c : Composition n, Σ j : Fin c.length, StasheffIndex (c.blocksFun j),
          tailSign deg (σ.1.sizeUpTo (σ.2.1 + 1)) •
            stasheffSign (fun i ↦ deg (σ.1.embedding σ.2.1 i)) σ.2.2 •
              G.compMapBlockUpdate F a σ.1 σ.2.1 d hd
                (F.compositionBlockMapCompTerm a σ.1 σ.2.1 σ.2.2) :=
        Fintype.sum_bijective _ MapCompIndex.bijective_toBlock _ _ fun _ ↦ rfl
    _ = _ := by
        simp only [Fintype.sum_sigma, signedStasheffSum, map_sum, Finset.smul_sum, Units.smul_def,
          map_zsmul]

/-- The sum, over all compositions `c` of `n`, of the left-hand sides of the functor equations
for `G` on the values of `F` on the blocks of `c`, regrouped by the composition of `n` into the
inputs of the outer component of `G` and the input containing the inner operation: for each of
them, the component of `G` is applied to the values of `F`, with the value on that input replaced
by the right-hand side of the functor equation of `F` on it. -/
theorem sum_mapCompSumBlockMap_eq_sum_compMapBlockUpdate :
    ∑ c : Composition n, G.mapCompSumBlockMap F a c d hd =
      ∑ c : Composition n, ∑ j : Fin c.length, tailSign deg (c.sizeUpTo (j + 1)) •
        G.compMapBlockUpdate F a c j d hd
          (∑ c' : Composition (c.blocksFun j), F.compositionBlockCompMapTerm a c j c') := by
  calc ∑ c : Composition n, G.mapCompSumBlockMap F a c d hd
      = ∑ σ : Σ c : Composition n, StasheffIndex c.length,
          stasheffSign (fun l ↦ F.degMap (functorTargetDeg fun i ↦ deg (σ.1.embedding l i))) σ.2 •
            G.mapCompTermBlockMap F a σ.1 d hd σ.2 := by
        simp only [mapCompSumBlockMap_eq_signedStasheffSum, signedStasheffSum, Fintype.sum_sigma]
    _ = ∑ x : CompMapIndex n,
          stasheffSign (fun l ↦ F.degMap (functorTargetDeg fun i ↦
            deg (x.composition.embedding l i))) x.stasheff •
              G.mapCompTermBlockMap F a x.composition d hd x.stasheff :=
        (Fintype.sum_bijective _ CompMapIndex.bijective_toSigma _ _ fun _ ↦ rfl).symm
    _ = ∑ x : CompMapIndex n, tailSign deg (x.outer.sizeUpTo (x.block + 1)) •
          G.compMapBlockUpdate F a x.outer x.block d hd
            (F.compositionBlockCompMapTerm a x.outer x.block x.inner) :=
        Finset.sum_congr rfl fun x _ ↦ by
          rw [x.mapCompTermBlockMap_eq_compMapBlockUpdate, x.stasheffSign_eq]
    _ = ∑ σ : Σ c : Composition n, Σ j : Fin c.length, Composition (c.blocksFun j),
          tailSign deg (σ.1.sizeUpTo (σ.2.1 + 1)) •
            G.compMapBlockUpdate F a σ.1 σ.2.1 d hd
              (F.compositionBlockCompMapTerm a σ.1 σ.2.1 σ.2.2) :=
        Fintype.sum_bijective _ CompMapIndex.bijective_toBlock _ _ fun _ ↦ rfl
    _ = _ := by simp only [Fintype.sum_sigma, map_sum, Finset.smul_sum]


/-- The right-hand side of the functor equation for `G.comp F`, indexed by `CompMapMapIndex`. -/
lemma comp_compMapSum_eq_sum_compCompMapTerm :
    (G.comp F).compMapSum a d hd =
      ∑ x : CompMapMapIndex n, G.compCompMapTerm F a d hd x.outer x.inner := by
  calc (G.comp F).compMapSum a d hd
      = ∑ σ : Σ e : Composition n, ∀ l : Fin e.length, Composition (e.blocksFun l),
          G.compCompMapTerm F a d hd σ.1 σ.2 := by
        simp only [compMapSum, comp_compMapTerm_eq_sum, Fintype.sum_sigma]
    _ = _ := (Fintype.sum_bijective _ CompMapMapIndex.bijective_toSigmaPi _ _ fun _ ↦ rfl).symm

/-- The sum, over all compositions `c` of `n`, of the right-hand sides of the functor equations
for `G` on the values of `F` on the blocks of `c` is the right-hand side of the functor equation
for `G.comp F`. -/
theorem sum_compMapSumBlockMap_eq_comp_compMapSum :
    ∑ c : Composition n, G.compMapSumBlockMap F a c d hd = (G.comp F).compMapSum a d hd := by
  refine Eq.trans ?_ ((Finset.sum_congr rfl fun x _ ↦
    x.compMapTermBlockMap_eq_compCompMapTerm G F a d hd).trans
      (G.comp_compMapSum_eq_sum_compCompMapTerm F a d hd).symm)
  calc ∑ c : Composition n, G.compMapSumBlockMap F a c d hd
      = ∑ σ : Σ c : Composition n, Composition c.length,
          G.compMapTermBlockMap F a σ.1 d hd σ.2 := by
        simp only [compMapSumBlockMap_eq_sum_compMapTermBlockMap, Fintype.sum_sigma]
    _ = _ := (Fintype.sum_bijective _ CompMapMapIndex.bijective_toSigma _ _ fun _ ↦ rfl).symm

end AInfinityFunctorData

end AInfinityTheory
