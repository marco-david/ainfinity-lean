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
lemmas on lists and compositions, the change of the size of one block of a composition, the
splitting of one block of a composition, lemmas on two-level compositions, the composition
`StasheffIndex.outerComposition` along which the blocks fed to an inner operation are gathered,
and the Koszul sign `tailSign` of the inputs from a given position on.

The lemmas on two-level compositions relate Mathlib's `Composition.sigmaEquivSigmaPi` to the two
descriptions recorded in `CompMapMapIndex`.

## Main definitions

* `Composition.setBlock`: a composition with the size of one block changed.
* `Composition.splitBlock`: a composition with one block split into the blocks of a composition
  of that block.
* `AInfinityTheory.StasheffIndex.outerComposition`: the composition of the inputs of an index
  triple into the inputs of its outer operation.
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

/-! ### Splitting one block of a composition -/

namespace Composition

variable {n : ℕ} (c : Composition n) (j : Fin c.length) (d : Composition (c.blocksFun j))

/-- The composition of `n` obtained from a composition `c` of `n` by splitting its `j`-th block
into the blocks of a composition `d` of that block. -/
def splitBlock : Composition n where
  blocks := c.blocks.take j ++ d.blocks ++ c.blocks.drop (j + 1)
  blocks_pos h := by
    simp only [List.mem_append] at h
    rcases h with (h | h) | h
    · exact c.blocks_pos (List.mem_of_mem_take h)
    · exact d.blocks_pos h
    · exact c.blocks_pos (List.mem_of_mem_drop h)
  blocks_sum := by
    have h := List.sum_take_add_sum_drop c.blocks j
    rw [List.drop_eq_getElem_cons (by simp), List.sum_cons] at h
    have := d.blocks_sum
    simp only [blocksFun, List.get_eq_getElem] at this
    simp only [List.sum_append, c.blocks_sum] at h ⊢
    omega

lemma length_splitBlock : (c.splitBlock j d).length + 1 = c.length + d.length := by
  simp only [splitBlock, length, List.length_append, List.length_take, List.length_drop]
  omega

lemma sizeUpTo_splitBlock_of_le {i : ℕ} (hi : i ≤ j) :
    (c.splitBlock j d).sizeUpTo i = c.sizeUpTo i := by
  simp [sizeUpTo, splitBlock, List.take_append, List.take_take, hi]

lemma sizeUpTo_splitBlock_add {u : ℕ} (hu : u ≤ d.length) :
    (c.splitBlock j d).sizeUpTo (j + u) = c.sizeUpTo j + d.sizeUpTo u := by
  simp [sizeUpTo, splitBlock, List.take_append, List.take_take, Nat.sub_eq_zero_of_le hu]

lemma sizeUpTo_splitBlock_add_length (v : ℕ) :
    (c.splitBlock j d).sizeUpTo (j + d.length + v) = c.sizeUpTo (j + 1 + v) := by
  have key : (c.splitBlock j d).blocks.drop (j + d.length + v) = c.blocks.drop (j + 1 + v) := by
    simp [splitBlock, List.drop_append, List.drop_drop, add_assoc, List.drop_eq_nil_of_le]
  have h₁ := List.sum_take_add_sum_drop (c.splitBlock j d).blocks (j + d.length + v)
  have h₂ := List.sum_take_add_sum_drop c.blocks (j + 1 + v)
  rw [key, blocks_sum] at h₁
  rw [blocks_sum] at h₂
  simp only [sizeUpTo]
  omega

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

/-- The composition of the n inputs into the r + 1 + t inputs of the outer operation: r blocks of
size 1, the block of size s of the inputs of the inner operation, and t blocks of size 1. Its
boundaries are the positions `outerBoundary` of the objects of the outer operation. -/
def outerComposition : Composition n where
  blocks := List.replicate p.r 1 ++ p.s :: List.replicate p.t 1
  blocks_pos h := by
    simp only [List.mem_append, List.mem_replicate, List.mem_cons] at h
    have := p.one_le_s
    omega
  blocks_sum := by
    simp only [List.sum_append, List.sum_replicate, List.sum_cons, smul_eq_mul, mul_one]
    have := p.sum_eq
    omega

@[simp]
lemma length_outerComposition : p.outerComposition.length = p.r + 1 + p.t := by
  simp only [outerComposition, Composition.length, List.length_append, List.length_replicate,
    List.length_cons]
  omega

lemma sizeUpTo_outerComposition (k : ℕ) :
    p.outerComposition.sizeUpTo k = min (if k ≤ p.r then k else k + p.s - 1) n := by
  have := p.sum_eq; have := p.one_le_s
  simp only [Composition.sizeUpTo, outerComposition, List.take_append, List.take_replicate,
    List.length_replicate, List.sum_append, List.sum_replicate, smul_eq_mul, mul_one]
  rcases Nat.lt_or_ge p.r k with h | h
  · obtain ⟨w, hw⟩ : ∃ w, k - p.r = w + 1 := ⟨k - p.r - 1, by omega⟩
    simp only [hw, List.take_succ_cons, List.sum_cons, List.take_replicate, List.sum_replicate,
      smul_eq_mul, mul_one]
    split_ifs <;> omega
  · simp only [Nat.sub_eq_zero_of_le h, List.take_zero, List.sum_nil]
    split_ifs <;> omega

lemma blocksFun_outerComposition_middle :
    p.outerComposition.blocksFun (p.middleIndex.cast p.length_outerComposition.symm) = p.s := by
  show (List.replicate p.r 1 ++ p.s :: List.replicate p.t 1)[p.r]'(by simp) = p.s
  simp [List.getElem_append_right]

section Gather

variable {m : ℕ} (c : Composition m) (q : StasheffIndex c.length)

lemma length_gather_outerComposition :
    (c.gather q.outerComposition).length = q.r + 1 + q.t := by
  rw [Composition.length_gather, length_outerComposition]

/-- Gathering the blocks of `c` along the outer operation of `q` merges the s blocks of the
inputs of the inner operation into one. -/
lemma sizeUpTo_gather_outerComposition (k : ℕ) :
    (c.gather q.outerComposition).sizeUpTo k =
      c.sizeUpTo (if k ≤ q.r then k else k + q.s - 1) := by
  rw [Composition.sizeUpTo_gather, sizeUpTo_outerComposition]
  rcases le_total (if k ≤ q.r then k else k + q.s - 1) c.length with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h, c.sizeUpTo_length, c.sizeUpTo_ofLength_le _ h]

/-- The merged block of `c.gather q.outerComposition` consists of s blocks of `c`. -/
lemma length_sigmaCompositionAux_outerComposition (j : Fin (c.gather q.outerComposition).length)
    (hj : (j : ℕ) = q.r) : (c.sigmaCompositionAux q.outerComposition j).length = q.s := by
  obtain rfl : j = (q.middleIndex.cast q.length_outerComposition.symm).cast
    (c.length_gather _).symm := Fin.ext hj
  exact (c.length_sigmaCompositionAux _ _).trans q.blocksFun_outerComposition_middle

/-- Inside the merged block of `c.gather q.outerComposition`, the blocks of `c` are those of
`c.sigmaCompositionAux q.outerComposition`. -/
lemma sizeUpTo_add_sigmaCompositionAux (j : Fin (c.gather q.outerComposition).length)
    (hj : (j : ℕ) = q.r) {u : ℕ} (hu : u ≤ q.s) :
    c.sizeUpTo (q.r + u) = (c.gather q.outerComposition).sizeUpTo q.r +
      (c.sigmaCompositionAux q.outerComposition j).sizeUpTo u := by
  obtain rfl : j = (q.middleIndex.cast q.length_outerComposition.symm).cast
    (c.length_gather _).symm := Fin.ext hj
  have := q.sum_eq
  have e := Composition.sizeUpTo_sizeUpTo_add_boundary c q.outerComposition
    (q.middleIndex.cast q.length_outerComposition.symm)
    ⟨u, by rw [blocksFun_outerComposition_middle]; omega⟩
  rw [show ((q.middleIndex.cast q.length_outerComposition.symm : Fin _) : ℕ) = q.r from rfl]
    at e
  simpa only [sizeUpTo_outerComposition, le_refl, ↓reduceIte,
    min_eq_left (by omega : q.r ≤ c.length)] using e

/-- Splitting the merged block of `c.gather q.outerComposition` back into the blocks of `c` gives
`c`. -/
lemma splitBlock_gather_outerComposition (j : Fin (c.gather q.outerComposition).length)
    (hj : (j : ℕ) = q.r) :
    (c.gather q.outerComposition).splitBlock j (c.sigmaCompositionAux q.outerComposition j) =
      c := by
  have hs := length_sigmaCompositionAux_outerComposition c q j hj
  have hl := (c.gather q.outerComposition).length_splitBlock j
    (c.sigmaCompositionAux q.outerComposition j)
  have := q.sum_eq; have := q.one_le_s; have := length_gather_outerComposition c q
  refine Composition.ext_of_sizeUpTo _ (by omega) fun k ↦ ?_
  rcases le_or_gt k q.r with h | h
  · rw [Composition.sizeUpTo_splitBlock_of_le _ _ _ (hj ▸ h), sizeUpTo_gather_outerComposition]
    simp only [h, ↓reduceIte]
  rcases le_or_gt k (q.r + q.s) with h' | h'
  · obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le h.le
    have e := Composition.sizeUpTo_splitBlock_add (c.gather q.outerComposition) j
      (c.sigmaCompositionAux q.outerComposition j) (u := u) (by omega)
    rw [hj] at e
    rw [e, sizeUpTo_add_sigmaCompositionAux c q j hj (by omega)]
  · obtain ⟨v, rfl⟩ : ∃ v, k = q.r + (c.sigmaCompositionAux q.outerComposition j).length + v :=
      ⟨k - q.r - q.s, by omega⟩
    have e := Composition.sizeUpTo_splitBlock_add_length (c.gather q.outerComposition) j
      (c.sigmaCompositionAux q.outerComposition j) v
    rw [hj] at e
    rw [e, sizeUpTo_gather_outerComposition]
    simp only [show ¬q.r + 1 + v ≤ q.r by omega, ↓reduceIte]
    congr 1
    omega

end Gather

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
