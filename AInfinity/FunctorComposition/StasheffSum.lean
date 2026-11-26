/-
Copyright (c) 2026 Marco David. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco David
-/
module

public import AInfinity.FunctorComposition.Assoc
public import AInfinity.FunctorComposition.Unit

/-! # The two sides of the A∞-functor equation as composites

Let `F` be A∞-functor data, with components the composable multilinear map
`F.toComposableMultilinearMap` with `s = 1`. This file identifies the two sides of the A∞-functor
equation of `F` with composites of composable multilinear maps:

* the right-hand side is the value of m' ∘ F, for the operations m' of the target;
* the left-hand side, a signed sum over the index triples (r, s, t) of the Stasheff identities,
  is the value of F ∘ (𝟙 | m), for the identity 𝟙 and the operations m of the source.

So the A∞-functor equation reads F ∘ (𝟙 | m) = m' ∘ F. The file also defines the composite of
A∞-functor data.

## Main definitions

* `AInfinityTheory.AInfinityFunctorData.toComposableMultilinearMap`: the components of A∞-functor
  data, as a composable multilinear map.
* `AInfinityTheory.AInfinityFunctorData.comp`: the composite of A∞-functor data.

## Main results

* `AInfinityTheory.AInfinityFunctorData.comp_assoc`: the composition of A∞-functor data is
  associative.
* `AInfinityTheory.AInfinityFunctorData.compMapSum_eq_comp_map_v`: the right-hand side of the
  functor equation is the value of m' ∘ F.
* `AInfinityTheory.AInfinityFunctorData.mapCompSum_eq_compMarked_map_v`: the left-hand side of
  the functor equation is the value of F ∘ (𝟙 | m).

## Implementation notes

A term of F ∘ (𝟙 | m) is indexed by a composition of `n` with a marked block. It vanishes unless
all blocks other than the marked one have size one, since the identity vanishes in arities other
than one. The compositions with a marked block of this form are the outer compositions
`StasheffIndex.outerMark` of the index triples: (r, s, t) gives r blocks of size one, the marked
block of size s, and t blocks of size one. This is the only place where the index triples of the
Stasheff identities meet compositions.
-/

@[expose] public section

noncomputable section

namespace AInfinityTheory

open GradedLinearQuiver

variable {n : ℕ}

namespace ComposableMultilinearMap

variable {β β' : Type*} [AddCommGroup β] [Grading β] [AddCommGroup β'] [Grading β']
  {R : Type*} [Semiring R] {Obj Obj' : Type*} [GradedLinearQuiver β R Obj]
  [GradedLinearQuiver β' R Obj'] {f : Obj → Obj'} {φ : β →+ᵍ β'} {X : Fin (n + 1) → Obj}
  {deg : Fin n → β} (a : ∀ i : Fin n, ComposableHom β R X i (deg i)) (c : Composition n)
  (l : Fin c.length)

/-- The value of an unmarked choice on a block is the value of the unmarked map. -/
lemma total_pick_blockMap_of_false (A : ComposableMultilinearMap R f φ 1)
    (D : ComposableMultilinearMap R f φ 2) {b : Bool} (hb : b = false) :
    Total.of ((pick A D b).2.blockMap a c l) = Total.of (A.blockMap a c l) := by
  subst hb
  rfl

/-- The value of a marked choice on a block is the value of the marked map. -/
lemma total_pick_blockMap_of_true (A : ComposableMultilinearMap R f φ 1)
    (D : ComposableMultilinearMap R f φ 2) {b : Bool} (hb : b = true) :
    Total.of ((pick A D b).2.blockMap a c l) = Total.of (D.blockMap a c l) := by
  subst hb
  rfl

/-- The value of an unmarked identity on a block of size other than one vanishes. -/
lemma pick_id_blockMap_eq_zero
    (D : ComposableMultilinearMap R (fun X : Obj ↦ X) (GradingHom.id β) 2) {b : Bool}
    (hb : b = false) (hl : c.blocksFun l ≠ 1) :
    (pick (ComposableMultilinearMap.id β R Obj) D b).2.blockMap a c l = 0 := by
  subst hb
  exact id_blockMap_eq_zero a c l hl

end ComposableMultilinearMap

namespace AInfinityFunctorData

variable {β β' β'' β''' : Type*} [AddCommGroup β] [Grading β] [AddCommGroup β'] [Grading β']
  [AddCommGroup β''] [Grading β''] [AddCommGroup β'''] [Grading β'''] {R : Type*} [Semiring R]
  {Obj Obj' Obj'' Obj''' : Type*}

/-! ### A∞-functor data as composable multilinear maps -/

section GradedLinearQuiver

variable [GradedLinearQuiver β R Obj] [GradedLinearQuiver β' R Obj']
  [GradedLinearQuiver β'' R Obj''] [GradedLinearQuiver β''' R Obj''']

/-- The components of A∞-functor data `F`, as a composable multilinear map with `s = 1` over
`F.obj` and `F.degMap`. -/
def toComposableMultilinearMap (F : AInfinityFunctorData β β' R Obj Obj') :
    ComposableMultilinearMap R F.obj F.degMap 1 where
  map X := F.map X

@[simp]
lemma toComposableMultilinearMap_map (F : AInfinityFunctorData β β' R Obj Obj') [NeZero n]
    (X : Fin (n + 1) → Obj) : F.toComposableMultilinearMap.map X = F.map X :=
  rfl

/-- The composite `G.comp F` of A∞-functor data `F` from `Obj` to `Obj'` and `G` from `Obj'` to
`Obj''`, written in Mathlib's order: it acts on objects by `G.obj ∘ F.obj`, translates degrees
along `G.degMap.comp F.degMap`, and its components are those of the composite of the components
of `G` and of `F` as composable multilinear maps. -/
protected def comp (G : AInfinityFunctorData β' β'' R Obj' Obj'')
    (F : AInfinityFunctorData β β' R Obj Obj') : AInfinityFunctorData β β'' R Obj Obj'' where
  obj X := G.obj (F.obj X)
  degMap := G.degMap.comp F.degMap
  map X := (G.toComposableMultilinearMap.comp F.toComposableMultilinearMap).map X

@[simp]
lemma comp_obj (G : AInfinityFunctorData β' β'' R Obj' Obj'')
    (F : AInfinityFunctorData β β' R Obj Obj') (X : Obj) : (G.comp F).obj X = G.obj (F.obj X) :=
  rfl

@[simp]
lemma comp_degMap (G : AInfinityFunctorData β' β'' R Obj' Obj'')
    (F : AInfinityFunctorData β β' R Obj Obj') : (G.comp F).degMap = G.degMap.comp F.degMap :=
  rfl

@[simp]
lemma comp_toComposableMultilinearMap (G : AInfinityFunctorData β' β'' R Obj' Obj'')
    (F : AInfinityFunctorData β β' R Obj Obj') :
    (G.comp F).toComposableMultilinearMap =
      G.toComposableMultilinearMap.comp F.toComposableMultilinearMap :=
  rfl

/-- The composition of A∞-functor data is associative. -/
theorem comp_assoc (H : AInfinityFunctorData β'' β''' R Obj'' Obj''')
    (G : AInfinityFunctorData β' β'' R Obj' Obj'') (F : AInfinityFunctorData β β' R Obj Obj') :
    (H.comp G).comp F = H.comp (G.comp F) :=
  congrArg (fun Ψ : ComposableMultilinearMap R (fun X ↦ H.obj (G.obj (F.obj X)))
      ((H.degMap.comp G.degMap).comp F.degMap) 1 ↦
    ({ obj := fun X ↦ H.obj (G.obj (F.obj X))
       degMap := (H.degMap.comp G.degMap).comp F.degMap
       map := fun X ↦ Ψ.map X } : AInfinityFunctorData β β''' R Obj Obj'''))
    (ComposableMultilinearMap.comp_assoc H.toComposableMultilinearMap
      G.toComposableMultilinearMap F.toComposableMultilinearMap)

end GradedLinearQuiver

section AInfinityCategoryStruct

variable [AInfinityCategoryStruct β R Obj] [AInfinityCategoryStruct β' R Obj']
  (F : AInfinityFunctorData β β' R Obj Obj') {X : Fin (n + 1) → Obj} {deg : Fin n → β}
  (a : ∀ i : Fin n, ComposableHom β R X i (deg i))

/-! ### The right-hand side of the functor equation -/

section CompMap

variable [NeZero n]

/-- A term of the right-hand side of the functor equation of `F` is a term of the composite
m' ∘ F of the operations of the target with `F`. -/
lemma total_compMapTerm (c : Composition n) (d : β) (hd : targetDeg 2 deg = d) (d' : β')
    (hd' : _) :
    Total.of (F.compMapTerm a c d hd) =
      Total.of ((AInfinityCategoryStruct.toComposableMultilinearMap β' R Obj').compTerm a c
        (fun _ ↦ ⟨1, F.toComposableMultilinearMap⟩) d' hd') := by
  simp only [compMapTerm, ComposableMultilinearMap.compTerm,
    ComposableMultilinearMap.applyBlocks, Total.of_homCongr]
  exact (AInfinityCategoryStruct.toComposableMultilinearMap β' R Obj').total_map_congr rfl _ _
    fun l ↦ rfl

/-- The right-hand side of the functor equation of `F` is the value of the composite m' ∘ F of
the operations of the target with `F`. -/
theorem compMapSum_eq_comp_map_v (d : β) (hd : targetDeg 2 deg = d) :
    F.compMapSum a d hd =
      (((AInfinityCategoryStruct.toComposableMultilinearMap β' R Obj').comp
        F.toComposableMultilinearMap).map X).v deg d hd a := by
  rw [ComposableMultilinearMap.comp_map_v_apply]
  exact Finset.sum_congr rfl fun c _ ↦ Total.of_inj.1 (F.total_compMapTerm a c d hd _ _)

end CompMap

/-! ### The left-hand side of the functor equation -/

section MapComp

open ComposableMultilinearMap

local notation "𝟙" => ComposableMultilinearMap.id β R Obj

local notation "𝐦" => AInfinityCategoryStruct.toComposableMultilinearMap β R Obj

variable (p : StasheffIndex n)

/-- The value of the identity on a block of size one of the outer composition of an index triple
is the input of that block. -/
lemma total_pick_blockMap_outerComposition_of_ne (x : Fin p.outerComposition.length)
    (hx : (x : ℕ) ≠ p.r) (i : Fin n)
    (hi : (i : ℕ) = if (x : ℕ) ≤ p.r then (x : ℕ) else x + p.s - 1) :
    Total.of ((pick 𝟙 𝐦 (decide (x = p.outerMiddle))).2.blockMap a p.outerComposition x) =
      Total.of (a i) := by
  refine (total_pick_blockMap_of_false a _ x 𝟙 𝐦
    (decide_eq_false fun hm ↦ hx (congrArg Fin.val hm))).trans ?_
  refine (total_id_blockMap a _ x (p.blocksFun_outerComposition_of_ne x hx)).trans ?_
  refine congrArg (fun i ↦ Total.of (a i)) (Fin.ext ?_)
  rw [p.val_embedding_outerComposition, hi]
  exact add_zero _

/-- The value of the operations of the source on the marked block of the outer composition of an
index triple is the inner output of the corresponding Stasheff term. -/
lemma total_pick_blockMap_outerComposition_middle (d : β) (hd : stasheffInnerDeg deg p = d) :
    Total.of ((pick 𝟙 𝐦 (decide (p.outerMiddle = p.outerMiddle))).2.blockMap a
      p.outerComposition p.outerMiddle) = Total.of (stasheffInner a p d hd) := by
  refine (total_pick_blockMap_of_true a _ _ 𝟙 𝐦 (decide_eq_true rfl)).trans ?_
  simp only [blockMap, stasheffInner, Total.of_homCongr]
  refine (𝐦).total_map_congr p.blocksFun_outerComposition_middle _ _ fun u ↦ ?_
  refine congrArg (fun i ↦ Total.of (a i)) (Fin.ext ?_)
  rw [p.val_embedding_outerComposition]
  change (if p.r ≤ p.r then p.r else p.r + p.s - 1) + (u : ℕ) = p.r + (u : ℕ)
  simp only [le_refl, ↓reduceIte]

variable [NeZero n]

/-- A term of the left-hand side of the functor equation of `F` is the term of F ∘ (𝟙 | m)
indexed by the outer composition of its index triple, with its marked block. -/
lemma total_mapCompTerm (d : β) (hd : targetDeg 2 deg = d) (d' : β') (hd' : _) :
    Total.of (F.mapCompTerm a p d hd) =
      Total.of (F.toComposableMultilinearMap.compTerm a p.outerComposition
        (fun l ↦ pick 𝟙 𝐦 (decide (l = p.outerMiddle))) d' hd') := by
  simp only [mapCompTerm, compTerm, applyBlocks, Total.of_homCongr]
  refine F.toComposableMultilinearMap.total_map_congr p.length_outerComposition.symm _ _
    fun i ↦ ?_
  induction i using Fin.addCases with
  | left i =>
    induction i using Fin.lastCases with
    | last =>
      rw [stasheffInputsOut_middle, Total.of_homCongr]
      exact (total_pick_blockMap_outerComposition_middle a p _ _).symm
    | cast j =>
      rw [stasheffInputsOut_left, Total.of_homCongr]
      refine (total_pick_blockMap_outerComposition_of_ne a p _ (Nat.ne_of_lt j.2) _ ?_).symm
      have := j.2
      change (j : ℕ) = if (j : ℕ) ≤ p.r then (j : ℕ) else j + p.s - 1
      split_ifs <;> omega
  | right k =>
    rw [stasheffInputsOut_right, Total.of_homCongr]
    refine (total_pick_blockMap_outerComposition_of_ne a p _
      (by change p.r + 1 + (k : ℕ) ≠ p.r; omega) _ ?_).symm
    change p.r + p.s + (k : ℕ) =
      if p.r + 1 + (k : ℕ) ≤ p.r then p.r + 1 + (k : ℕ) else p.r + 1 + k + p.s - 1
    split_ifs <;> omega

/-- A term of F ∘ (𝟙 | m) vanishes unless its composition with its marked block is the outer
composition of an index triple. -/
lemma compTerm_pick_id_eq_zero (x : Σ c : Composition n, Fin c.length)
    (hx : x ∉ Set.range (StasheffIndex.outerMark (n := n))) (d' : β') (hd' : _) :
    F.toComposableMultilinearMap.compTerm a x.1 (fun l ↦ pick 𝟙 𝐦 (decide (l = x.2))) d' hd' =
      0 := by
  obtain ⟨l, hl, hl'⟩ : ∃ l, l ≠ x.2 ∧ x.1.blocksFun l ≠ 1 := by
    by_contra hall
    exact hx (StasheffIndex.mem_range_outerMark x fun l hl ↦ by_contra fun hl' ↦ hall ⟨l, hl, hl'⟩)
  simp only [compTerm, applyBlocks]
  refine (congrArg _ (MultilinearMap.map_coord_zero _ l ?_)).trans (map_zero _)
  exact pick_id_blockMap_eq_zero a x.1 l 𝐦 (decide_eq_false hl) hl'

/-- The left-hand side of the functor equation of `F` is the signed sum of the terms of
F ∘ (𝟙 | m). -/
lemma signedStasheffSum_mapCompTerm (d : β) (hd : targetDeg 2 deg = d)
    (hd' : ∀ (c : Composition n) (_ : Fin c.length), _) :
    signedStasheffSum deg (fun p ↦ F.mapCompTerm a p d hd) =
      ∑ c : Composition n, ∑ m : Fin c.length, tailSign deg (c.sizeUpTo (m + 1)) •
        F.toComposableMultilinearMap.compTerm a c (fun l ↦ pick 𝟙 𝐦 (decide (l = m)))
          (F.degMap d) (hd' c m) := by
  rw [Finset.sum_sigma', Finset.univ_sigma_univ]
  refine Fintype.sum_of_injective StasheffIndex.outerMark StasheffIndex.outerMark_injective _ _
    (fun x hx ↦ ?_) fun p ↦ ?_
  · rw [F.compTerm_pick_id_eq_zero a x hx, smul_zero]
  · refine congrArg₂ (· • ·) ((stasheffSign_eq_tailSign deg p).trans (congrArg _ ?_))
      (Total.of_inj.1 (F.total_mapCompTerm a p d hd _ _))
    have := p.sum_eq
    have := p.one_le_s
    change p.r + p.s = p.outerComposition.sizeUpTo (p.r + 1)
    rw [p.sizeUpTo_outerComposition]
    split_ifs <;> omega

/-- The left-hand side of the functor equation of `F` is the value of the composite F ∘ (𝟙 | m)
of `F` with the identity, with one input replaced by the operations of the source. -/
theorem mapCompSum_eq_compMarked_map_v (d : β) (hd : targetDeg 2 deg = d) :
    F.mapCompSum a d hd =
      ((F.toComposableMultilinearMap.compMarked 𝟙 𝐦 one_add_one_eq_two).map X).v deg d hd a :=
  (F.signedStasheffSum_mapCompTerm a d hd _).trans
    (compMarked_map_v_apply F.toComposableMultilinearMap 𝟙 𝐦 a one_add_one_eq_two hd).symm

end MapComp

end AInfinityCategoryStruct

end AInfinityFunctorData

end AInfinityTheory
