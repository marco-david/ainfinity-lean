/-
Copyright (c) 2026 Zhan Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhan Shi
-/
module

public import AInfinity.FunctorComposition.OuterComposition

/-! # Koszul signs in the functor equation of a composite

The Koszul sign `stasheffSign` of an index triple q = (r, s, t) is the sign of the inputs after
the inner operation. This file introduces the Koszul sign `tailSign deg N` of the inputs from
position `N` on, so that `stasheffSign deg q = tailSign deg (q.r + q.s)`. It is the sign of the
terms of the composite Φ ∘ (F | D) of `AInfinity.FunctorComposition.Defs`.

## Main definitions

* `AInfinityTheory.tailSign`: the Koszul sign of the inputs from a given position on.

## Main results

* `AInfinityTheory.stasheffSign_eq_tailSign`: the Koszul sign of an index triple is the Koszul
  sign of the inputs after its inner operation.
* `AInfinityTheory.tailSign_sizeUpTo_add`: splitting the inputs from a position inside a block of
  a composition into those inside the block and those after it.
* `AInfinityTheory.tailSign_targetDeg_embedding`: the reduced degree of a value of an
  A∞-functor is the sum of the reduced degrees of its inputs, so the Koszul sign of the values
  of `F` on the blocks of a composition is the Koszul sign of the original inputs.
-/

@[expose] public section

noncomputable section

namespace AInfinityTheory

variable {n : ℕ} {β : Type*} [AddCommGroup β] [Grading β]

/-- The Koszul sign of the inputs from position `N` on: (-1) raised to the sum of the reduced
degrees ‖a‖ = |a| - 1 of the inputs at positions `i ≥ N`. -/
def tailSign (deg : Fin n → β) (N : ℕ) : ℤˣ :=
  ∏ i ∈ Finset.univ.filter (fun i : Fin n ↦ N ≤ (i : ℕ)), (sign (deg i - degOne)).toMul

lemma tailSign_eq_prod_ite (deg : Fin n → β) (N : ℕ) :
    tailSign deg N = ∏ i : Fin n, if N ≤ (i : ℕ) then (sign (deg i - degOne)).toMul else 1 :=
  Finset.prod_filter _ _

/-- The Koszul sign of the index triple q = (r, s, t) is the Koszul sign of the inputs after
its inner operation. -/
theorem stasheffSign_eq_tailSign (deg : Fin n → β) (q : StasheffIndex n) :
    stasheffSign deg q = tailSign deg (q.r + q.s) := by
  have := q.sum_eq
  refine Finset.prod_nbij q.rightIndex (fun k _ ↦ ?_) (fun k _ k' _ h ↦ ?_) (fun i hi ↦ ?_)
    fun _ _ ↦ rfl
  · simp [StasheffIndex.rightIndex]
  · simpa [StasheffIndex.rightIndex, Fin.ext_iff] using h
  · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hi
    exact ⟨⟨i - (q.r + q.s), by omega⟩, by simp,
      Fin.ext (by simp only [StasheffIndex.rightIndex, Fin.natAdd_mk, Fin.castLE_mk]; omega)⟩

/-- Splitting the inputs from position N inside the block `j` of a composition `c` into the
inputs of the block from its position N on and the inputs after the block. -/
theorem tailSign_sizeUpTo_add (deg : Fin n → β) (c : Composition n) (j : Fin c.length) {N : ℕ}
    (hN : N ≤ c.blocksFun j) :
    tailSign deg (c.sizeUpTo j + N) =
      tailSign (fun i ↦ deg (c.embedding j i)) N * tailSign deg (c.sizeUpTo (j + 1)) := by
  have := c.sizeUpTo_succ' j
  rw [tailSign, tailSign, tailSign, ← Finset.prod_filter_mul_prod_filter_not _
    (fun i : Fin n ↦ (i : ℕ) < c.sizeUpTo (j + 1)), Finset.filter_filter, Finset.filter_filter]
  congr 1
  · refine (Finset.prod_nbij (c.embedding j) (fun m hm ↦ ?_) (c.embedding j).injective.injOn
      (fun i hi ↦ ?_) fun _ _ ↦ rfl).symm
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, c.coe_embedding] at hm ⊢
      omega
    · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hi
      refine ⟨⟨i - c.sizeUpTo j, by omega⟩, ?_, Fin.ext (by simp only [c.coe_embedding]; omega)⟩
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
      omega
  · congr 1
    exact Finset.filter_congr fun i _ ↦ ⟨fun h ↦ by omega, fun h ↦ by omega⟩

/-- The reduced degree ‖φₖ(a₁, …, aₖ)‖ of a value of an A∞-functor is the sum of the reduced
degrees ‖aᵢ‖ of its inputs, since φₖ has degree 1 - k. -/
lemma toMul_sign_targetDeg_sub_degOne {k : ℕ} (d : Fin k → β) :
    (sign (targetDeg 1 d - degOne)).toMul = ∏ i, (sign (d i - degOne)).toMul := by
  rw [← toMul_sum, ← map_sum]
  congr 2
  simp only [targetDeg, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin]
  module

/-- The Koszul sign of the values of an A∞-functor on the blocks of a composition `c`, from the
block `k` on, is the Koszul sign of the original inputs from the boundary of the block `k` on. -/
theorem tailSign_targetDeg_embedding {β' : Type*} [AddCommGroup β'] [Grading β']
    (φ : β →+ᵍ β') (deg : Fin n → β) (c : Composition n) (k : ℕ) :
    tailSign (fun l ↦ φ (targetDeg 1 fun i ↦ deg (c.embedding l i))) k =
      tailSign deg (c.sizeUpTo k) := by
  rw [tailSign_eq_prod_ite, tailSign_eq_prod_ite, ← c.blocksFinEquiv.prod_comp,
    Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun l _ ↦ ?_
  simp only [Composition.blocksFinEquiv, Equiv.coe_fn_mk, c.sizeUpTo_le_embedding_iff]
  split_ifs
  · rw [← GradingHom.map_degOne φ, ← map_sub, GradingHom.map_sign,
      toMul_sign_targetDeg_sub_degOne]
  · simp

end AInfinityTheory
