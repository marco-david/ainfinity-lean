/-
Copyright (c) 2026 Annie Yao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Annie Yao, Marco David, Zhan Shi
-/
module

public import AInfinity.FunctorComposition.Congr
public import AInfinity.FunctorComposition.Defs

/-! # The functor equation of `G` on the values of `F` on the blocks of a composition

For A∞-functor data `F` and `G` and a composition c = (i₁, …, iₖ) of `n`, the values
F_{i₁}(…), …, F_{iₖ}(…) of the components of `F` on the k blocks of `c` form a composable string
of length k, on which the functor equation of `G` can be evaluated. Summed over all compositions
of `n`, both of its sides appear in the proof that `G.comp F` satisfies the functor equations.
This file defines the terms of both sides, transported to the endpoints `G (F X₀)` and
`G (F Xₙ)`, and the component of `G` on the values of `F` with one of them replaced.

## Main definitions

* `AInfinityTheory.ComposableMultilinearMap.mapCompSumBlockMap`,
  `AInfinityTheory.ComposableMultilinearMap.compMapSumBlockMap`: the left-hand and right-hand sides
  of the functor equation of `G` on the values of the components of `F` on the blocks of a
  composition of `n`.
* `AInfinityTheory.updateComposableHom`: a composable string with one morphism replaced by a
  morphism of another degree.
* `AInfinityTheory.ComposableMultilinearMap.compMapBlockUpdate`: the component of `G` applied to the
  values of `F` on the blocks of a composition, with one of them replaced, as a linear map in the
  replacing morphism.
* `AInfinityTheory.ComposableMultilinearMap.compositionBlockMapCompTerm`,
  `AInfinityTheory.ComposableMultilinearMap.compositionBlockCompMapTerm`: the terms of the two sides
  of the functor equation of `F` on one block of a composition.
-/

@[expose] public section

noncomputable section

namespace AInfinityTheory

open GradedLinearQuiver

variable {n : ℕ}

section Degrees

variable {β : Type*} [AddCommGroup β] [Grading β]

lemma targetDeg_update (s : ℤ) {k : ℕ} (δ : Fin k → β) (j : Fin k) (e : β) :
    targetDeg s (Function.update δ j e) = targetDeg s δ - δ j + e := by
  simp only [targetDeg, Finset.sum_update_of_mem (Finset.mem_univ j),
    Finset.sdiff_singleton_eq_erase, Finset.sum_erase_eq_sub (Finset.mem_univ j)]
  abel

end Degrees

namespace ComposableMultilinearMap

variable {β β' β'' : Type*} [AddCommGroup β] [Grading β] [AddCommGroup β'] [Grading β']
  [AddCommGroup β''] [Grading β''] {R : Type*} [Semiring R] {Obj Obj' Obj'' : Type*}

/-! ### The two sides of the functor equation of `G` on the blocks of `F` -/

section AInfinityCategoryStruct

variable [GradedLinearQuiver β R Obj] [AInfinityCategoryStruct β' R Obj']
  [AInfinityCategoryStruct β'' R Obj'']
variable (G : AInfinityFunctorData β' β'' R Obj' Obj'') (F : AInfinityFunctorData β β' R Obj Obj')
  {X : Fin (n + 1) → Obj} {deg : Fin n → β} (a : ∀ i : Fin n, ComposableHom β R X i (deg i))
  (c : Composition n) (d : β) (hd : targetDeg 2 deg = d)

/-- The term, indexed by p = (r, s, t), of the left-hand side of the functor equation of `G` on
the values of the components of `F` on the k blocks of a composition `c` of `n`: the component
of `G` of arity r + 1 + t applied to the first r values of `F`, the operation of arity s on the
next s values and the last t values, as a morphism from `G (F X₀)` to `G (F Xₙ)`. -/
def mapCompTermBlockMap (p : StasheffIndex c.length) :
    (G.obj (F.obj (X 0)) →ᵍ[R] G.obj (F.obj (X (Fin.last n)))) (G.degMap (F.degMap d)) :=
  homCongr R (congrArg (fun k ↦ G.obj (F.obj (X k))) c.boundary_zero)
    (congrArg (fun k ↦ G.obj (F.obj (X k))) c.boundary_last) rfl
    (G.mapCompTerm (F.compositionBlockMap a c) p (F.degMap d)
      (F.targetDeg_degMap_targetDeg_embedding c d hd))

/-- The left-hand side of the functor equation of `G` on the values of the components of `F`
on the blocks of a composition `c` of `n`, as a morphism from `G (F X₀)` to `G (F Xₙ)`.
Summed over `c`, it is the left-hand side of the functor equation of `G.comp F`. -/
def mapCompSumBlockMap :
    (G.obj (F.obj (X 0)) →ᵍ[R] G.obj (F.obj (X (Fin.last n)))) (G.degMap (F.degMap d)) :=
  homCongr R (congrArg (fun k ↦ G.obj (F.obj (X k))) c.boundary_zero)
    (congrArg (fun k ↦ G.obj (F.obj (X k))) c.boundary_last) rfl
    (G.mapCompSum (F.compositionBlockMap a c) (F.degMap d)
      (F.targetDeg_degMap_targetDeg_embedding c d hd))

lemma mapCompSumBlockMap_eq_signedStasheffSum :
    G.mapCompSumBlockMap F a c d hd =
      signedStasheffSum (fun l ↦ F.degMap (targetDeg 1 fun j ↦ deg (c.embedding l j)))
        fun p ↦ G.mapCompTermBlockMap F a c d hd p :=
  map_signedStasheffSum _ _

variable [NeZero n]

/-- The right-hand side of the functor equation of `G` on the values of the components of `F`
on the blocks of a composition `c` of `n`, as a morphism from `G (F X₀)` to `G (F Xₙ)`.
Summed over `c`, it is the right-hand side of the functor equation of `G.comp F`
(`ComposableMultilinearMap.sum_compMapSumBlockMap_eq_comp_compMapSum`). -/
def compMapSumBlockMap :
    (G.obj (F.obj (X 0)) →ᵍ[R] G.obj (F.obj (X (Fin.last n)))) (G.degMap (F.degMap d)) :=
  homCongr R (congrArg (fun k ↦ G.obj (F.obj (X k))) c.boundary_zero)
    (congrArg (fun k ↦ G.obj (F.obj (X k))) c.boundary_last) rfl
    (G.compMapSum (F.compositionBlockMap a c) (F.degMap d)
      (F.targetDeg_degMap_targetDeg_embedding c d hd))

end AInfinityCategoryStruct

end ComposableMultilinearMap

/-! ### The component of `G` with one value of `F` replaced -/

section Update

variable {β : Type*} {R : Type*} [Semiring R] {Obj : Type*} [GradedLinearQuiver β R Obj] {k : ℕ}
  {Y : Fin (k + 1) → Obj} {δ : Fin k → β}

/-- The composable string `b` with its `j`-th morphism replaced by a morphism `x` of another
degree `e`. -/
def updateComposableHom (b : ∀ l, ComposableHom β R Y l (δ l)) (j : Fin k) {e : β}
    (x : ComposableHom β R Y j e) : ∀ l, ComposableHom β R Y l (Function.update δ j e l) :=
  fun l ↦ if h : l = j then homCongr R (by rw [h]) (by rw [h]) (by simp [h]) x
    else homCongr R rfl rfl (by simp [h]) (b l)

lemma homCongr_updateComposableHom_of_eq (b : ∀ l, ComposableHom β R Y l (δ l)) {j l : Fin k}
    (h : l = j) {e : β} (x : ComposableHom β R Y j e) :
    homCongr R (congrArg (fun l ↦ Y l.castSucc) h) (congrArg (fun l ↦ Y l.succ) h)
      (by rw [h, Function.update_self]) (updateComposableHom b j x l) = x := by
  subst h
  simp [updateComposableHom]

lemma homCongr_updateComposableHom_of_ne (b : ∀ l, ComposableHom β R Y l (δ l)) {j l : Fin k}
    (h : l ≠ j) {e : β} (x : ComposableHom β R Y j e) :
    homCongr R rfl rfl (Function.update_of_ne h e δ) (updateComposableHom b j x l) = b l := by
  simp [updateComposableHom, h]

lemma updateComposableHom_eq_update (b : ∀ l, ComposableHom β R Y l (δ l)) (j : Fin k) {e : β}
    (x : ComposableHom β R Y j e) :
    updateComposableHom b j x =
      Function.update (updateComposableHom b j 0) j (homCongr R rfl rfl (by simp) x) := by
  funext l
  by_cases h : l = j
  · subst h
    simp [updateComposableHom]
  · simp [updateComposableHom, h]

variable {N : Type*} [AddCommMonoid N] [Module R N]

/-- A multilinear map on a composable string with the `j`-th morphism replaced, as a linear map
in the replacing morphism. -/
def updateLinearMap (b : ∀ l, ComposableHom β R Y l (δ l)) (j : Fin k) {e : β}
    (f : MultilinearMap R (fun l ↦ ComposableHom β R Y l (Function.update δ j e l)) N) :
    ComposableHom β R Y j e →ₗ[R] N :=
  f.toLinearMap (updateComposableHom b j 0) j ∘ₗ (homCongr R rfl rfl (by simp)).toLinearMap

@[simp]
lemma updateLinearMap_apply (b : ∀ l, ComposableHom β R Y l (δ l)) (j : Fin k) {e : β}
    (f : MultilinearMap R (fun l ↦ ComposableHom β R Y l (Function.update δ j e l)) N)
    (x : ComposableHom β R Y j e) :
    updateLinearMap b j f x = f (updateComposableHom b j x) := by
  simp [updateLinearMap, updateComposableHom_eq_update b j x]

end Update

namespace ComposableMultilinearMap

variable {β β' β'' : Type*} [AddCommGroup β] [Grading β] [AddCommGroup β'] [Grading β']
  [AddCommGroup β''] [Grading β''] {R : Type*} [Semiring R] {Obj Obj' Obj'' : Type*}

section BlockUpdate

variable [GradedLinearQuiver β R Obj] [GradedLinearQuiver β' R Obj']
  [GradedLinearQuiver β'' R Obj'']
variable (G : AInfinityFunctorData β' β'' R Obj' Obj'') (F : AInfinityFunctorData β β' R Obj Obj')
  {X : Fin (n + 1) → Obj} {deg : Fin n → β} (a : ∀ i : Fin n, ComposableHom β R X i (deg i))
  (c : Composition n) (j : Fin c.length) (d : β) (hd : targetDeg 2 deg = d)

include hd in
lemma targetDeg_update_targetDeg :
    targetDeg 1 (Function.update
      (fun l ↦ F.degMap (targetDeg 1 fun i ↦ deg (c.embedding l i))) j
      (F.degMap (targetDeg 2 fun i ↦ deg (c.embedding j i)))) = F.degMap d := by
  rw [targetDeg_update, F.targetDeg_degMap_targetDeg_embedding c _ rfl, ← hd,
    targetDeg_eq_targetDeg_add_degOne (s := 2) (t := 1) (by norm_num),
    targetDeg_eq_targetDeg_add_degOne (s := 2) (t := 1) (by norm_num)]
  simp only [map_add, GradingHom.map_degOne]
  abel

variable [NeZero n]

/-- The component of `G` of arity k applied to the values of the components of `F` on the k
blocks of a composition `c` of `n`, with the value on the `j`-th block replaced by a morphism `x`
of one degree higher, transported to the hom space from `G (F X₀)` to `G (F Xₙ)`; as a linear
map in `x`. -/
def compMapBlockUpdate :
    ComposableHom β' R (fun k ↦ F.obj (X (c.boundary k))) j
        (F.degMap (targetDeg 2 fun i ↦ deg (c.embedding j i))) →ₗ[R]
      (G.obj (F.obj (X 0)) →ᵍ[R] G.obj (F.obj (X (Fin.last n)))) (G.degMap (F.degMap d)) :=
  (homCongr R (congrArg (fun k ↦ G.obj (F.obj (X k))) c.boundary_zero)
    (congrArg (fun k ↦ G.obj (F.obj (X k))) c.boundary_last) rfl).toLinearMap ∘ₗ
    updateLinearMap (F.compositionBlockMap a c) j
      ((G.map fun k ↦ F.obj (X (c.boundary k))).v _ (F.degMap d)
        (targetDeg_update_targetDeg F c j d hd))

lemma compMapBlockUpdate_apply
    (x : ComposableHom β' R (fun k ↦ F.obj (X (c.boundary k))) j
      (F.degMap (targetDeg 2 fun i ↦ deg (c.embedding j i)))) :
    G.compMapBlockUpdate F a c j d hd x =
      homCongr R (congrArg (fun k ↦ G.obj (F.obj (X k))) c.boundary_zero)
        (congrArg (fun k ↦ G.obj (F.obj (X k))) c.boundary_last) rfl
        ((G.map fun k ↦ F.obj (X (c.boundary k))).v _ (F.degMap d)
          (targetDeg_update_targetDeg F c j d hd)
          (updateComposableHom (F.compositionBlockMap a c) j x)) := by
  simp [compMapBlockUpdate]

end BlockUpdate

section BlockTerms

variable [AInfinityCategoryStruct β R Obj] [AInfinityCategoryStruct β' R Obj']
variable (F : AInfinityFunctorData β β' R Obj Obj') {X : Fin (n + 1) → Obj} {deg : Fin n → β}
  (a : ∀ i : Fin n, ComposableHom β R X i (deg i)) (c : Composition n) (j : Fin c.length)

/-- The term indexed by `p` of the left-hand side of the functor equation of `F` on the `j`-th
block of a composition `c`, as the `j`-th input of an outer operation on the objects
`F (X (c.boundary k))`. -/
def compositionBlockMapCompTerm (p : StasheffIndex (c.blocksFun j)) :
    ComposableHom β' R (fun k ↦ F.obj (X (c.boundary k))) j
      (F.degMap (targetDeg 2 fun i ↦ deg (c.embedding j i))) :=
  homCongr R (congrArg F.obj (compositionBlockObj_zero X c j))
    (congrArg F.obj (compositionBlockObj_last X c j)) rfl
    (F.mapCompTerm (fun i ↦ a (c.embedding j i)) p _ rfl)

/-- The term indexed by a composition `c'` of the right-hand side of the functor equation of `F`
on the `j`-th block of a composition `c`, as the `j`-th input of an outer operation on the
objects `F (X (c.boundary k))`. -/
def compositionBlockCompMapTerm (c' : Composition (c.blocksFun j)) :
    ComposableHom β' R (fun k ↦ F.obj (X (c.boundary k))) j
      (F.degMap (targetDeg 2 fun i ↦ deg (c.embedding j i))) :=
  homCongr R (congrArg F.obj (compositionBlockObj_zero X c j))
    (congrArg F.obj (compositionBlockObj_last X c j)) rfl
    (F.compMapTerm (fun i ↦ a (c.embedding j i)) c' _ rfl)

end BlockTerms

end ComposableMultilinearMap

end AInfinityTheory
