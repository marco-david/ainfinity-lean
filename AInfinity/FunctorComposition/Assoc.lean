/-
Copyright (c) 2026 Zhan Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhan Shi
-/
module

public import AInfinity.FunctorComposition.BlockMap
public import AInfinity.FunctorComposition.CompMapMapIndex

/-! # Associativity of the composition with A∞-functor data

Let `H` be a composable multilinear map and `G` and `F` be A∞-functor data. This file proves that
`(H.comp G).comp F = H.comp (G.comp F)`. The two sides are sums of terms
$$H_k(G(F(\dots), \dots, F(\dots)), \dots, G(F(\dots), \dots, F(\dots))).$$
In `(H.comp G).comp F`, such a term is described by a composition c of `n` and a composition of
`c.length`; in `H.comp (G.comp F)`, it is described by a composition of `n` and a composition of
each of its blocks. The index type `CompMapMapIndex` records both descriptions, and the two
descriptions of a term are matched here.

Two cases of this statement are used elsewhere:

* for A∞-functor data `H`, it is the associativity of the composition of A∞-functor data, and
  gives the associativity of the composition of A∞-functors, `AInfinityFunctor.comp_assoc`;
* for the operations `m''` of an A∞-category structure, it says that the sum, over all
  compositions of `n`, of the right-hand sides of the functor equations for `G` on the values of
  `F` is the right-hand side of the functor equation for `G.comp F`
  (`ComposableMultilinearMap.sum_compMapSumBlockMap_eq_comp_compMapSum`). This is the third step
  of the proof that the composite of A∞-functors is an A∞-functor.

## Main definitions

* `AInfinityTheory.ComposableMultilinearMap.compositionBlockCompTerm`: the summand, indexed by a
  composition of a block, of the value of the composite component (G ∘ F) on that block.
* `AInfinityTheory.ComposableMultilinearMap.compCompMapTerm`: the summand of `H.comp (G.comp F)`
  indexed by a composition of `n` and compositions of its blocks.
* `AInfinityTheory.ComposableMultilinearMap.compMapTermBlockMap`: the summand of
  `(H.comp G).comp F` indexed by a composition c of `n` and a composition of `c.length`.

## Main results

* `AInfinityTheory.CompMapMapIndex.compMapTermBlockMap_eq_compCompMapTerm`: the two descriptions
  of a term agree.
* `AInfinityTheory.ComposableMultilinearMap.comp_assoc`: the composition with A∞-functor data is
  associative.
* `AInfinityTheory.ComposableMultilinearMap.sum_compMapSumBlockMap_eq_comp_compMapSum`: the sum of
  the right-hand sides of the functor equations for `G` on the values of `F` is the right-hand
  side of the functor equation for `G.comp F`.

## Implementation notes

The reindexing relies on the bijectivity of the projections of `CompMapMapIndex`, which describe
Mathlib's `Composition.sigmaEquivSigmaPi`, as in the proof of associativity of the composition of
formal multilinear series (`FormalMultilinearSeries.comp_assoc`). The two descriptions of a term
are matched using only the relations recorded in `CompMapMapIndex`.
-/

@[expose] public section

noncomputable section

namespace AInfinityTheory

open GradedLinearQuiver AInfinityCategoryStruct

variable {n : ℕ}

/-! ### The terms of both sides -/

namespace ComposableMultilinearMap

variable {β β' β'' β''' : Type*} [AddCommGroup β] [Grading β] [AddCommGroup β'] [Grading β']
  [AddCommGroup β''] [Grading β''] [AddCommGroup β'''] [Grading β'''] {R : Type*} [Semiring R]
  {Obj Obj' Obj'' Obj''' : Type*} [GradedLinearQuiver β R Obj] [GradedLinearQuiver β' R Obj']
  [GradedLinearQuiver β'' R Obj''] [GradedLinearQuiver β''' R Obj'''] {s : ℤ}
variable (H : ComposableMultilinearMap β'' β''' R Obj'' Obj''' s)
  (G : AInfinityFunctorData β' β'' R Obj' Obj'') (F : AInfinityFunctorData β β' R Obj Obj')
  {X : Fin (n + 1) → Obj} {deg : Fin n → β} (a : ∀ i : Fin n, ComposableHom β R X i (deg i))

/-- The term, indexed by a composition `c` of the `l`-th block of a composition `e` of `n`, of the
value of the composite component (G ∘ F) on that block: the component of `G` of arity `c.length`
applied to the values of the components of `F` on the blocks of `c`, as the `l`-th input of an
outer map on the objects `G (F (X (e.boundary k)))`. -/
def compositionBlockCompTerm (e : Composition n) (l : Fin e.length)
    (c : Composition (e.blocksFun l)) :
    ComposableHom β'' R (fun k ↦ (G.comp F).obj (X (e.boundary k))) l
      ((G.comp F).degMap (targetDeg 1 fun j ↦ deg (e.embedding l j))) :=
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

variable [NeZero n] (j : β) (hj : targetDeg s deg = j)

/-- The summand of `H.comp (G.comp F)` indexed by a composition `e` of `n` and compositions `τ l`
of its blocks: the component of `H` of arity `e.length` applied to the components of `G` on the
values of the components of `F` on the blocks of the compositions `τ l`. -/
def compCompMapTerm (e : Composition n) (τ : ∀ l : Fin e.length, Composition (e.blocksFun l)) :
    (H.obj (G.obj (F.obj (X 0))) →ᵍ[R] H.obj (G.obj (F.obj (X (Fin.last n)))))
      (H.degMap (G.degMap (F.degMap j))) :=
  homCongr R (congrArg (fun k ↦ H.obj ((G.comp F).obj (X k))) e.boundary_zero)
    (congrArg (fun k ↦ H.obj ((G.comp F).obj (X k))) e.boundary_last) rfl
    ((H.map fun k ↦ (G.comp F).obj (X (e.boundary k))).v
      (fun l ↦ (G.comp F).degMap (targetDeg 1 fun i ↦ deg (e.embedding l i)))
      ((G.comp F).degMap j) ((G.comp F).targetDeg_degMap_targetDeg_embedding e j hj)
      fun l ↦ G.compositionBlockCompTerm F a e l (τ l))

/-- The value of `H.comp (G.comp F)`, as a sum over compositions of `n` and compositions of their
blocks. -/
lemma comp_comp_map_v_apply_eq_sum_compCompMapTerm :
    ((H.comp (G.comp F)).map X).v deg j hj a =
      ∑ σ : Σ e : Composition n, ∀ l : Fin e.length, Composition (e.blocksFun l),
        H.compCompMapTerm G F a j hj σ.1 σ.2 := by
  rw [comp_map_v_apply, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  rw [funext (G.comp_compositionBlockMap_eq_sum F a e), MultilinearMap.map_sum, map_sum]
  rfl

/-- The summand of `(H.comp G).comp F` indexed by a composition `c` of `n` and a composition `c'`
of `c.length`: the component of `H` of arity `c'.length` applied to the components of `G` on the
groups, given by `c'`, of the values of the components of `F` on the blocks of `c`. -/
def compMapTermBlockMap (c : Composition n) (c' : Composition c.length) :
    (H.obj (G.obj (F.obj (X 0))) →ᵍ[R] H.obj (G.obj (F.obj (X (Fin.last n)))))
      (H.degMap (G.degMap (F.degMap j))) :=
  homCongr R (congrArg (fun k ↦ H.obj (G.obj (F.obj (X k)))) c.boundary_zero)
    (congrArg (fun k ↦ H.obj (G.obj (F.obj (X k)))) c.boundary_last) rfl
    (homCongr R (congrArg (fun k ↦ H.obj (G.obj (F.obj (X (c.boundary k))))) c'.boundary_zero)
      (congrArg (fun k ↦ H.obj (G.obj (F.obj (X (c.boundary k))))) c'.boundary_last) rfl
      ((H.map fun k ↦ G.obj (F.obj (X (c.boundary (c'.boundary k))))).v _
        (G.degMap (F.degMap j))
        (G.targetDeg_degMap_targetDeg_embedding c' _
          (F.targetDeg_degMap_targetDeg_embedding c j hj))
        (G.compositionBlockMap (F.compositionBlockMap a c) c')))

/-- The summand of `(H.comp G).comp F` indexed by a composition `c` of `n`, as a sum over the
compositions of `c.length`. -/
lemma homCongr_comp_map_v_apply_eq_sum_compMapTermBlockMap (c : Composition n) :
    homCongr R (congrArg (fun k ↦ (H.comp G).obj (F.obj (X k))) c.boundary_zero)
      (congrArg (fun k ↦ (H.comp G).obj (F.obj (X k))) c.boundary_last) rfl
      ((((H.comp G).map fun k ↦ F.obj (X (c.boundary k))).v _ (F.degMap j)
        (F.targetDeg_degMap_targetDeg_embedding c j hj)) (F.compositionBlockMap a c)) =
      ∑ c' : Composition c.length, H.compMapTermBlockMap G F a j hj c c' :=
  (congrArg (homCongr R (congrArg (fun k ↦ (H.comp G).obj (F.obj (X k))) c.boundary_zero)
    (congrArg (fun k ↦ (H.comp G).obj (F.obj (X k))) c.boundary_last) rfl)
    (comp_map_v_apply H G _ _ (F.compositionBlockMap a c) _ _)).trans (map_sum _ _ _)

/-- The value of `(H.comp G).comp F`, as a sum over compositions c of `n` and compositions of
`c.length`. -/
lemma comp_comp_map_v_apply_eq_sum_compMapTermBlockMap :
    (((H.comp G).comp F).map X).v deg j hj a =
      ∑ σ : Σ c : Composition n, Composition c.length, H.compMapTermBlockMap G F a j hj σ.1 σ.2 :=
  ((comp_map_v_apply (H.comp G) F X deg a j hj).trans (Finset.sum_congr rfl fun c _ ↦
    H.homCongr_comp_map_v_apply_eq_sum_compMapTermBlockMap G F a j hj c)).trans
    (Fintype.sum_sigma fun σ : Σ c : Composition n, Composition c.length ↦
      H.compMapTermBlockMap G F a j hj σ.1 σ.2).symm

end ComposableMultilinearMap

/-! ### Matching the two descriptions of a term -/

namespace CompMapMapIndex

open ComposableMultilinearMap

variable (x : CompMapMapIndex n)

/-- The object string of the outer map in the term indexed by `x`: the boundaries of
`x.composition` at the boundaries of `x.grouping` are the boundaries of `x.outer`. -/
lemma boundary_boundary (k : Fin (x.grouping.length + 1)) :
    x.composition.boundary (x.grouping.boundary k) =
      x.outer.boundary (k.cast (by rw [x.length_eq])) :=
  Fin.ext (by simpa [Composition.boundary] using x.sizeUpTo_sizeUpTo k)

lemma targetDeg_embedding_eq {β : Type*} [AddCommGroup β] [Grading β] (deg : Fin n → β)
    (l : Fin x.grouping.length) (j : Fin (x.grouping.blocksFun l)) :
    targetDeg 1 (fun i ↦ deg (x.composition.embedding (x.grouping.embedding l j) i)) =
      targetDeg 1 (fun i ↦ deg (x.outer.embedding (l.cast x.length_eq)
        ((x.inner (l.cast x.length_eq)).embedding (j.cast (x.length_inner l).symm) i))) :=
  targetDeg_congr 1 (x.blocksFun_embedding l j) fun i ↦ congrArg deg
    (Composition.embedding_eq_embedding_embedding (x.sizeUpTo_embedding l j)
      (x.blocksFun_embedding l j) i)

variable {β β' β'' β''' : Type*} [AddCommGroup β] [Grading β] [AddCommGroup β'] [Grading β']
  [AddCommGroup β''] [Grading β''] [AddCommGroup β'''] [Grading β'''] {R : Type*} [Semiring R]
  {Obj Obj' Obj'' Obj''' : Type*} [GradedLinearQuiver β R Obj] [GradedLinearQuiver β' R Obj']
  [GradedLinearQuiver β'' R Obj''] [GradedLinearQuiver β''' R Obj'''] {s : ℤ}
variable (H : ComposableMultilinearMap β'' β''' R Obj'' Obj''' s)
  (G : AInfinityFunctorData β' β'' R Obj' Obj'') (F : AInfinityFunctorData β β' R Obj Obj')
  {X : Fin (n + 1) → Obj} {deg : Fin n → β} (a : ∀ i : Fin n, ComposableHom β R X i (deg i))

/-- The input degrees of the outer map in the term indexed by `x`, before translation along
`G.degMap`: the degree of the value of `G` on the values of `F` on the blocks of `x.composition`
grouped by `x.grouping` is the degree of the value of `G.comp F` on the corresponding block of
`x.outer`. -/
lemma targetDeg_degMap_eq (l : Fin x.grouping.length) :
    targetDeg 1 (fun j ↦ F.degMap (targetDeg 1 fun i ↦
      deg (x.composition.embedding (x.grouping.embedding l j) i))) =
      F.degMap (targetDeg 1 fun i ↦ deg (x.outer.embedding (l.cast x.length_eq) i)) := by
  rw [← F.targetDeg_degMap_targetDeg_embedding
    (deg := fun i ↦ deg (x.outer.embedding (l.cast x.length_eq) i))
    (x.inner (l.cast x.length_eq)) _ rfl]
  exact targetDeg_congr 1 (x.length_inner l).symm fun j ↦
    congrArg F.degMap (x.targetDeg_embedding_eq deg l j)

/-- The `l`-th input of the outer map in the term indexed by `x`: the value of `G` on the
values of `F` on the blocks of `x.composition` grouped by `x.grouping` is the term indexed by
`x.inner` of the value of `G.comp F` on the corresponding block of `x.outer`. -/
lemma homCongr_compositionBlockMap_eq_compositionBlockCompTerm (l : Fin x.grouping.length) :
    homCongr R (congrArg (fun z ↦ G.obj (F.obj (X z))) (x.boundary_boundary l.castSucc))
      (congrArg (fun z ↦ G.obj (F.obj (X z))) (x.boundary_boundary l.succ))
      (congrArg G.degMap (x.targetDeg_degMap_eq F l))
      (G.compositionBlockMap (F.compositionBlockMap a x.composition) x.grouping l) =
      G.compositionBlockCompTerm F a x.outer (l.cast x.length_eq)
        (x.inner (l.cast x.length_eq)) := by
  refine (homCongr_homCongr _ _ _ _ _ _ _).trans ((homCongr_eq_homCongr_of_eq
    (G.map_v_congr (x.length_inner l).symm
      (Y := compositionBlockObj (fun k ↦ F.obj (X (x.composition.boundary k))) x.grouping l)
      (Y' := fun k ↦ F.obj (compositionBlockObj X x.outer (l.cast x.length_eq)
        ((x.inner (l.cast x.length_eq)).boundary k)))
      (fun k ↦ congrArg F.obj (congrArg X (Fin.ext ?_)))
      (fun j ↦ congrArg F.degMap (x.targetDeg_embedding_eq deg l j)) _ _
      fun j ↦ ?_)).trans (homCongr_homCongr _ _ _ _ _ _ _).symm)
  · simpa [Composition.boundary, compositionBlockObj] using
      x.sizeUpTo_add l k (Nat.lt_succ_iff.mp k.2)
  · exact F.compositionBlockMap_congr_compositionBlockMap_embedding a (x.sizeUpTo_embedding l j)
      (x.blocksFun_embedding l j)

variable [NeZero n] (j : β) (hj : targetDeg s deg = j)

/-- The two descriptions of a term of `(H.comp G).comp F = H.comp (G.comp F)` agree: the summand
of `(H.comp G).comp F` indexed by `x.composition` and `x.grouping` is the summand of
`H.comp (G.comp F)` indexed by `x.outer` and `x.inner`. -/
theorem compMapTermBlockMap_eq_compCompMapTerm :
    H.compMapTermBlockMap G F a j hj x.composition x.grouping =
      H.compCompMapTerm G F a j hj x.outer x.inner := by
  refine (homCongr_homCongr _ _ _ _ _ _ _).trans (homCongr_eq_homCongr_of_eq
    (H.map_v_congr x.length_eq
      (Y' := fun k ↦ (G.comp F).obj (X (x.outer.boundary k)))
      (fun k ↦ congrArg (fun z ↦ G.obj (F.obj (X z))) (x.boundary_boundary k))
      (fun l ↦ congrArg G.degMap (x.targetDeg_degMap_eq F l)) _ _ fun l ↦ ?_))
  exact x.homCongr_compositionBlockMap_eq_compositionBlockCompTerm G F a l

end CompMapMapIndex

/-! ### Associativity -/

namespace ComposableMultilinearMap

variable {β β' β'' β''' : Type*} [AddCommGroup β] [Grading β] [AddCommGroup β'] [Grading β']
  [AddCommGroup β''] [Grading β''] [AddCommGroup β'''] [Grading β'''] {R : Type*} [Semiring R]
  {Obj Obj' Obj'' Obj''' : Type*}

section GradedLinearQuiver

variable [GradedLinearQuiver β R Obj] [GradedLinearQuiver β' R Obj']
  [GradedLinearQuiver β'' R Obj''] [GradedLinearQuiver β''' R Obj'''] {s : ℤ}
variable (H : ComposableMultilinearMap β'' β''' R Obj'' Obj''' s)
  (G : AInfinityFunctorData β' β'' R Obj' Obj'') (F : AInfinityFunctorData β β' R Obj Obj')

/-- The terms of `(H.comp G).comp F` and of `H.comp (G.comp F)` are the same, reindexed through
`CompMapMapIndex`. -/
lemma sum_compMapTermBlockMap_eq_sum_compCompMapTerm [NeZero n] {X : Fin (n + 1) → Obj}
    {deg : Fin n → β} (a : ∀ i : Fin n, ComposableHom β R X i (deg i)) (j : β)
    (hj : targetDeg s deg = j) :
    ∑ σ : Σ c : Composition n, Composition c.length, H.compMapTermBlockMap G F a j hj σ.1 σ.2 =
      ∑ σ : Σ e : Composition n, ∀ l : Fin e.length, Composition (e.blocksFun l),
        H.compCompMapTerm G F a j hj σ.1 σ.2 :=
  calc _ = ∑ x : CompMapMapIndex n, H.compMapTermBlockMap G F a j hj x.composition x.grouping :=
        (Fintype.sum_bijective _ CompMapMapIndex.bijective_toSigma _ _ fun _ ↦ rfl).symm
    _ = ∑ x : CompMapMapIndex n, H.compCompMapTerm G F a j hj x.outer x.inner :=
        Finset.sum_congr rfl fun x _ ↦ x.compMapTermBlockMap_eq_compCompMapTerm H G F a j hj
    _ = _ := Fintype.sum_bijective _ CompMapMapIndex.bijective_toSigmaPi _ _ fun _ ↦ rfl

/-- The components of `(H.comp G).comp F` and `H.comp (G.comp F)` agree. -/
theorem comp_comp_map [NeZero n] (X : Fin (n + 1) → Obj) :
    ((H.comp G).comp F).map X = (H.comp (G.comp F)).map X :=
  GradedMultilinearMap.ext fun _ j hj ↦ MultilinearMap.ext fun a ↦
    (H.comp_comp_map_v_apply_eq_sum_compMapTermBlockMap G F a j hj).trans
      ((H.sum_compMapTermBlockMap_eq_sum_compCompMapTerm G F a j hj).trans
        (H.comp_comp_map_v_apply_eq_sum_compCompMapTerm G F a j hj).symm)

/-- The composition of a composable multilinear map with A∞-functor data is associative. In
particular, the composition of A∞-functor data is associative. -/
theorem comp_assoc : (H.comp G).comp F = H.comp (G.comp F) := by
  have h : (fun {n : ℕ} [NeZero n] (X : Fin (n + 1) → Obj) ↦ ((H.comp G).comp F).map X) =
      fun {n : ℕ} [NeZero n] (X : Fin (n + 1) → Obj) ↦ (H.comp (G.comp F)).map X := by
    funext n _ X
    exact comp_comp_map H G F X
  exact congrArg (mk (H.comp (G.comp F)).obj (H.comp (G.comp F)).degMap) h

end GradedLinearQuiver

/-! ### The right-hand side of the functor equation for a composite -/

section AInfinityCategoryStruct

variable [AInfinityCategoryStruct β R Obj] [AInfinityCategoryStruct β' R Obj']
  [AInfinityCategoryStruct β'' R Obj'']
variable (G : AInfinityFunctorData β' β'' R Obj' Obj'') (F : AInfinityFunctorData β β' R Obj Obj')
  {X : Fin (n + 1) → Obj} {deg : Fin n → β} (a : ∀ i : Fin n, ComposableHom β R X i (deg i))
  (d : β) (hd : targetDeg 2 deg = d) [NeZero n]

/-- The right-hand side of the functor equation of `G` on the values of `F` on the blocks of a
composition `c` of `n` is the summand indexed by `c` of the composite of `m''.comp G` with `F`. -/
lemma compMapSumBlockMap_eq_homCongr_comp_map_v_apply (c : Composition n) :
    G.compMapSumBlockMap F a c d hd =
      homCongr R (congrArg (fun k ↦ ((toComposableMultilinearMap β'' R Obj'').comp G).obj
          (F.obj (X k))) c.boundary_zero)
        (congrArg (fun k ↦ ((toComposableMultilinearMap β'' R Obj'').comp G).obj
          (F.obj (X k))) c.boundary_last) rfl
        ((((toComposableMultilinearMap β'' R Obj'').comp G).map
          fun k ↦ F.obj (X (c.boundary k))).v _ (F.degMap d)
          (F.targetDeg_degMap_targetDeg_embedding c d hd) (F.compositionBlockMap a c)) :=
  congrArg (homCongr R _ _ rfl) (G.compMapSum_eq_comp_map_v (F.compositionBlockMap a c) _ _)

/-- The sum, over all compositions `c` of `n`, of the right-hand sides of the functor equations
for `G` on the values of `F` on the blocks of `c` is the right-hand side of the functor equation
for `G.comp F`. This is `comp_assoc` for the operations m'' of the target. -/
theorem sum_compMapSumBlockMap_eq_comp_compMapSum :
    ∑ c : Composition n, G.compMapSumBlockMap F a c d hd = (G.comp F).compMapSum a d hd := by
  rw [compMapSum_eq_comp_map_v, ← comp_comp_map]
  refine (Finset.sum_congr rfl fun c _ ↦
    G.compMapSumBlockMap_eq_homCongr_comp_map_v_apply F a d hd c).trans ?_
  exact (comp_map_v_apply _ F X deg a d hd).symm

end AInfinityCategoryStruct

end ComposableMultilinearMap

end AInfinityTheory
