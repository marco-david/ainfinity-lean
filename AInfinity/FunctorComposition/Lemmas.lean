/-
Copyright (c) 2026 Zhan Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhan Shi
-/
module

public import Mathlib.Analysis.Analytic.Composition
public import AInfinity.StasheffIndex

/-! # Auxiliary results for the index types of the functor equation of a composite

This file collects the results shared by the index types `MapCompIndex`, `CompMapIndex` and
`CompMapMapIndex` of the terms of the functor equation for a composite `G.comp F` of A∞-functors:
lemmas on lists and compositions, the change of the size of one block of a composition, lemmas on
two-level compositions, and the Koszul sign `tailSign` of the inputs from a given position on.

The lemmas on two-level compositions relate Mathlib's `Composition.sigmaEquivSigmaPi` to the two
descriptions recorded in `CompMapMapIndex`.

## Main definitions

* `Composition.setBlock`: a composition with the size of one block changed.
* `AInfinityTheory.tailSign`: the Koszul sign of the inputs from a given position on.
-/

@[expose] public section

noncomputable section

/-- Two blocks whose boundaries differ by the same offset `m` have the same size. -/
lemma Composition.blocksFun_eq_of_sizeUpTo_eq_add {n₁ n₂ : ℕ} {c₁ : Composition n₁}
    {c₂ : Composition n₂} {l₁ : Fin c₁.length} {l₂ : Fin c₂.length} {m : ℕ}
    (h : c₁.sizeUpTo l₁ = m + c₂.sizeUpTo l₂)
    (h' : c₁.sizeUpTo (l₁ + 1) = m + c₂.sizeUpTo (l₂ + 1)) :
    c₁.blocksFun l₁ = c₂.blocksFun l₂ := by
  have := c₁.sizeUpTo_succ' l₁
  have := c₂.sizeUpTo_succ' l₂
  omega

/-- Changing the `i`-th entry of a list changes its sum by the difference. -/
lemma List.sum_set_add_getElem {M : Type*} [AddCommMonoid M] {l : List M} {i : ℕ}
    (hi : i < l.length) (a : M) : (l.set i a).sum + l[i] = l.sum + a := by
  have h := List.sum_set l i l[i]
  rw [List.set_getElem_self] at h
  rw [h, List.sum_set]
  simp only [hi, ↓reduceIte]
  abel

/-! ### Changing the size of one block of a composition -/

namespace Composition

variable {n : ℕ} (c : Composition n) (j : Fin c.length) (b : ℕ) (hb : 0 < b) {m : ℕ}
  (hm : m + c.blocksFun j = n + b)

/-- The composition of `m` obtained from a composition `c` of `n` by changing the size of its
`j`-th block to a positive `b`, where `m + c.blocksFun j = n + b`. -/
def setBlock : Composition m where
  blocks := c.blocks.set j b
  blocks_pos h := (List.mem_or_eq_of_mem_set h).elim c.blocks_pos fun h ↦ h ▸ hb
  blocks_sum := by
    have := List.sum_set_add_getElem j.2 b
    have := c.blocks_sum
    simp only [Composition.blocksFun, List.get_eq_getElem] at hm
    omega

@[simp]
lemma length_setBlock : (c.setBlock j b hb hm).length = c.length :=
  List.length_set

lemma blocksFun_setBlock_self :
    (c.setBlock j b hb hm).blocksFun (j.cast (c.length_setBlock j b hb hm).symm) = b :=
  List.getElem_set_self _

lemma sizeUpTo_setBlock_of_le {i : ℕ} (hi : i ≤ j) :
    (c.setBlock j b hb hm).sizeUpTo i = c.sizeUpTo i := by
  simp only [sizeUpTo, setBlock, List.take_set_of_le hi]

lemma sizeUpTo_setBlock_of_lt {i : ℕ} (hi : j < i) :
    (c.setBlock j b hb hm).sizeUpTo i + c.blocksFun j = c.sizeUpTo i + b := by
  have hj : (j : ℕ) < (c.blocks.take i).length := by
    simpa only [List.length_take, lt_min_iff] using ⟨hi, j.2⟩
  simpa [sizeUpTo, setBlock, List.take_set, blocksFun] using List.sum_set_add_getElem hj b

/-- Changing the size of a block and then changing it back gives the original composition. -/
lemma setBlock_setBlock {b' : ℕ} (hb' : b' = c.blocksFun j) :
    (c.setBlock j b hb hm).setBlock (j.cast (c.length_setBlock j b hb hm).symm) b'
      (hb' ▸ c.one_le_blocksFun j) (by rw [blocksFun_setBlock_self]; omega) = c :=
  Composition.ext <| (List.set_set _).trans <| hb' ▸ List.set_getElem_self _

omit b hb m hm in
/-- The `i`-th input lies in the block `c.index i`. -/
lemma lt_sizeUpTo_index_add_blocksFun (i : Fin n) :
    (i : ℕ) < c.sizeUpTo (c.index i) + c.blocksFun (c.index i) := by
  simpa [sizeUpTo_succ'] using c.lt_sizeUpTo_index_succ i

omit j b hb m hm in
/-- A composition is determined by its number of blocks and the positions of its blocks. -/
lemma ext_of_sizeUpTo {c' : Composition n} (hl : c.length = c'.length)
    (h : ∀ i, c.sizeUpTo i = c'.sizeUpTo i) : c = c' :=
  Composition.ext (List.ext_getElem hl fun i h₁ h₂ ↦
    blocksFun_eq_of_sizeUpTo_eq_add (l₁ := ⟨i, h₁⟩) (l₂ := ⟨i, h₂⟩) (m := 0)
      (by simpa using h i) (by simpa using h (i + 1)))

end Composition

/-! ### Two-level compositions

For a composition `a` of `n` and a composition `b` of `a.length`, the blocks of `a.gather b` are
the groups of consecutive blocks of `a` given by `b`, and `a.sigmaCompositionAux b` records how
each of them splits into blocks of `a`. -/

namespace Composition

variable {n : ℕ} (a : Composition n) (b : Composition a.length)

/-- The blocks of `a.gather b` before the `i`-th one cover the same part of `n` as the blocks of
`a` before the `b.sizeUpTo i`-th one. -/
lemma sizeUpTo_gather (i : ℕ) : (a.gather b).sizeUpTo i = a.sizeUpTo (b.sizeUpTo i) := by
  rcases lt_or_ge i b.length with hi | hi
  · simpa using (sizeUpTo_sizeUpTo_add a b hi (b.one_le_blocksFun ⟨i, hi⟩)).symm
  · rw [sizeUpTo_ofLength_le _ _ (by rwa [length_gather]), b.sizeUpTo_ofLength_le _ hi,
      a.sizeUpTo_length]

/-- The boundaries of the blocks of `a` inside the `j`-th group of `b` are the boundaries of the
blocks of `a.sigmaCompositionAux b` inside the `j`-th block of `a.gather b`, including the last
one. -/
lemma sizeUpTo_sizeUpTo_add_boundary (j : Fin b.length) (q : Fin (b.blocksFun j + 1)) :
    a.sizeUpTo (b.sizeUpTo j + q) =
      (a.gather b).sizeUpTo j +
        (a.sigmaCompositionAux b (j.cast (length_gather a b).symm)).sizeUpTo q := by
  induction q using Fin.lastCases with
  | last =>
    rw [Fin.val_last, ← b.sizeUpTo_succ', ← sizeUpTo_gather, sizeUpTo_ofLength_le
      (a.sigmaCompositionAux b (j.cast _)) _ (length_sigmaCompositionAux a b j).le]
    exact (a.gather b).sizeUpTo_succ' (j.cast (length_gather a b).symm)
  | cast q => exact sizeUpTo_sizeUpTo_add a b j.2 q.2

/-- The embedding of a block of `a.sigmaCompositionAux b` into the corresponding block of
`a.gather b` is the embedding of the corresponding block of `a`. -/
lemma gather_embedding_sigmaCompositionAux_embedding (j : Fin b.length)
    (q : Fin (b.blocksFun j)) (s : Fin (a.blocksFun (b.embedding j q))) :
    (a.gather b).embedding (j.cast (length_gather a b).symm)
        ((a.sigmaCompositionAux b (j.cast (length_gather a b).symm)).embedding
          (q.cast (length_sigmaCompositionAux a b j).symm)
          (s.cast (blocksFun_sigmaCompositionAux a b j q).symm)) =
      a.embedding (b.embedding j q) s := by
  apply Fin.ext
  simpa [coe_embedding, Nat.add_assoc] using
    congrArg (· + s.val) (sizeUpTo_sizeUpTo_add_boundary a b j q.castSucc).symm

end Composition

namespace AInfinityTheory

variable {n : ℕ}

namespace StasheffIndex

variable (p : StasheffIndex n)

/-- The position of the `i`-th object of the outer operation among the n + 1 objects: the
objects up to position r are kept, the later ones are shifted by s - 1. -/
lemma val_outerBoundary (i : Fin (p.r + 1 + p.t + 1)) :
    (p.outerBoundary i : ℕ) = if (i : ℕ) ≤ p.r then (i : ℕ) else (i : ℕ) + p.s - 1 := by
  have := p.one_le_s
  split_ifs with h
  · exact p.val_outerBoundary_castAdd ⟨i, by omega⟩
  · have := p.val_outerBoundary_natAdd ⟨i - (p.r + 1), by omega⟩
    rw [show Fin.natAdd (p.r + 1) ⟨i - (p.r + 1), _⟩ = i from
      Fin.ext (by simp only [Fin.natAdd_mk]; omega)] at this
    simp only [this]
    omega

end StasheffIndex

/-! ### Koszul signs -/

section Signs

variable {β : Type*} [AddCommGroup β] [Grading β]

/-- The Koszul sign of the inputs from position `N` on: (-1) raised to the sum of the reduced
degrees ‖a‖ = |a| - 1 of the inputs at positions `i ≥ N`. -/
def tailSign (deg : Fin n → β) (N : ℕ) : ℤˣ :=
  ∏ i ∈ Finset.univ.filter (fun i : Fin n ↦ N ≤ (i : ℕ)), (sign (deg i - degOne)).toMul

end Signs

end AInfinityTheory
