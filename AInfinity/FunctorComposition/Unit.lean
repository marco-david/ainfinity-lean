/-
Copyright (c) 2026 Marco David. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco David
-/
module

public import AInfinity.FunctorComposition.Defs

/-! # The identity is a unit for the composition of composable multilinear maps

The identity composable multilinear map 𝟙 has the identity as its unary component, and its other
components vanish. This file proves that it is a unit for the composition of
`AInfinity.FunctorComposition.Defs`.

## Main results

* `AInfinityTheory.ComposableMultilinearMap.comp_id`: `Φ ∘ 𝟙 = Φ`. Only the composition of `n`
  into blocks of size one contributes to the composite.
* `AInfinityTheory.ComposableMultilinearMap.id_comp`: `𝟙 ∘ F = F`. Only the composition of `n`
  with a single block contributes to the composite.

## Implementation notes

The two sides of a unit law are composable multilinear maps over `fun X ↦ f X` and
`φ.comp (GradingHom.id β)`, and over `f` and `φ`. These are equal by `rfl`, so the laws are
equalities in one type, and can be used to rewrite.
-/

@[expose] public section

noncomputable section

namespace AInfinityTheory

open GradedLinearQuiver

variable {n : ℕ}

namespace ComposableMultilinearMap

variable {β β' : Type*} [AddCommGroup β] [Grading β] [AddCommGroup β'] [Grading β']
  {R : Type*} [Semiring R] {Obj Obj' : Type*} [GradedLinearQuiver β R Obj]
  [GradedLinearQuiver β' R Obj'] {f : Obj → Obj'} {φ : β →+ᵍ β'} {s : ℤ}

/-! ### Values of the identity -/

section Identity

/-- The unary component of the identity is the identity, in the type of all morphisms. -/
lemma total_id_map {k : ℕ} [NeZero k] (hk : k = 1) {Y : Fin (k + 1) → Obj} {δ : Fin k → β}
    (b : ∀ i, ComposableHom β R Y i (δ i)) {j : β} (hj : targetDeg 1 δ = j) :
    Total.of (((ComposableMultilinearMap.id β R Obj).map Y).v δ j hj b) =
      Total.of (b ⟨0, hk ▸ Nat.one_pos⟩) := by
  subst hk
  simp only [id_map_one, idMap_v_apply, Total.of_homCongr]
  rfl

variable {X : Fin (n + 1) → Obj} {deg : Fin n → β} (a : ∀ i : Fin n, ComposableHom β R X i (deg i))
  (c : Composition n) (l : Fin c.length)

/-- The value of the identity on a block of size one is the input of that block. -/
lemma total_id_blockMap (hl : c.blocksFun l = 1) :
    Total.of ((ComposableMultilinearMap.id β R Obj).blockMap a c l) =
      Total.of (a (c.embedding l ⟨0, hl ▸ Nat.one_pos⟩)) := by
  simp only [blockMap, Total.of_homCongr]
  exact total_id_map hl _ _

/-- The value of the identity on a block of size other than one vanishes. -/
lemma id_blockMap_eq_zero (hl : c.blocksFun l ≠ 1) :
    (ComposableMultilinearMap.id β R Obj).blockMap a c l = 0 := by
  simp only [blockMap, id_map_eq_zero hl, GradedMultilinearMap.zero_v]
  exact map_zero _

end Identity

/-! ### The identity is a right unit -/

section CompId

variable (Φ : ComposableMultilinearMap R f φ s) [NeZero n] {X : Fin (n + 1) → Obj}
  {deg : Fin n → β} (a : ∀ i : Fin n, ComposableHom β R X i (deg i))

/-- A term of Φ ∘ 𝟙 vanishes unless all blocks of its composition have size one. -/
lemma compTerm_id_eq_zero (c : Composition n) (hc : c ≠ Composition.ones n) (d : β')
    (hd : _) :
    Φ.compTerm a c (fun _ ↦ ⟨1, ComposableMultilinearMap.id β R Obj⟩) d hd = 0 := by
  obtain ⟨i, hi, h1⟩ := Composition.ne_ones_iff.1 hc
  obtain ⟨l, rfl⟩ := List.mem_iff_get.1 hi
  simp only [compTerm, applyBlocks]
  rw [MultilinearMap.map_coord_zero _ l (id_blockMap_eq_zero a c l (Nat.ne_of_gt h1)), map_zero]

/-- The term of Φ ∘ 𝟙 indexed by the composition into blocks of size one is the value of Φ. -/
lemma total_compTerm_id_ones (d : β') (hd : _) {j : β} (hj : targetDeg s deg = j) :
    Total.of (Φ.compTerm a (Composition.ones n)
      (fun _ ↦ ⟨1, ComposableMultilinearMap.id β R Obj⟩) d hd) =
      Total.of ((Φ.map X).v deg j hj a) := by
  simp only [compTerm, applyBlocks, Total.of_homCongr]
  refine Φ.total_map_congr (Composition.ones_length n) _ _ fun l ↦ ?_
  refine (total_id_blockMap a _ l (Composition.ones_blocksFun n l)).trans ?_
  exact congrArg (fun i ↦ Total.of (a i)) ((Composition.ones_embedding l _).trans (Fin.ext rfl))

/-- The identity is a right unit for the composition of composable multilinear maps. -/
theorem comp_id (Φ : ComposableMultilinearMap R f φ s) :
    Φ.comp (ComposableMultilinearMap.id β R Obj) = Φ := by
  ext n _ X deg a j hj
  rw [comp_map_v_apply, Finset.sum_eq_single (Composition.ones n)
    (fun c _ hc ↦ compTerm_id_eq_zero Φ a c hc _ _) (fun hn ↦ absurd (Finset.mem_univ _) hn)]
  exact Total.of_inj.1 (total_compTerm_id_ones Φ a _ _ hj)

end CompId

/-! ### The identity is a left unit -/

section IdComp

variable (F : ComposableMultilinearMap R f φ 1) [NeZero n] {X : Fin (n + 1) → Obj}
  {deg : Fin n → β} (a : ∀ i : Fin n, ComposableHom β R X i (deg i))

/-- A term of 𝟙 ∘ F vanishes unless its composition has a single block. -/
lemma id_compTerm_eq_zero (c : Composition n) (hc : c ≠ Composition.single n (NeZero.pos n))
    (d : β') (hd : _) :
    (ComposableMultilinearMap.id β' R Obj').compTerm a c (fun _ ↦ ⟨1, F⟩) d hd = 0 := by
  have hl : c.length ≠ 1 := fun hl ↦ hc ((Composition.eq_single_iff_length (NeZero.pos n)).2 hl)
  simp only [compTerm, applyBlocks, id_map_eq_zero hl, GradedMultilinearMap.zero_v]
  exact map_zero _

/-- The term of 𝟙 ∘ F indexed by the composition with a single block is the value of `F`. -/
lemma total_id_compTerm_single (d : β') (hd : _) {j : β} (hj : targetDeg 1 deg = j) :
    Total.of ((ComposableMultilinearMap.id β' R Obj').compTerm a
      (Composition.single n (NeZero.pos n)) (fun _ ↦ ⟨1, F⟩) d hd) =
      Total.of ((F.map X).v deg j hj a) := by
  simp only [compTerm, applyBlocks, Total.of_homCongr]
  refine (total_id_map (Composition.single_length (NeZero.pos n)) _ _).trans ?_
  simp only [blockMap, Total.of_homCongr]
  refine F.total_map_congr (Composition.single_blocksFun (NeZero.pos n) _) _ _ fun i ↦ ?_
  exact congrArg (fun i ↦ Total.of (a i))
    (Fin.ext ((Composition.coe_embedding _ _ _).trans (zero_add _)))

/-- The identity is a left unit for the composition of composable multilinear maps. -/
theorem id_comp (F : ComposableMultilinearMap R f φ 1) :
    (ComposableMultilinearMap.id β' R Obj').comp F = F := by
  ext n _ X deg a j hj
  rw [comp_map_v_apply, Finset.sum_eq_single (Composition.single n (NeZero.pos n))
    (fun c _ hc ↦ id_compTerm_eq_zero F a c hc _ _) (fun hn ↦ absurd (Finset.mem_univ _) hn)]
  exact Total.of_inj.1 (total_id_compTerm_single F a _ _ hj)

end IdComp

end ComposableMultilinearMap

end AInfinityTheory
