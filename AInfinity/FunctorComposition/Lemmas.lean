/-
Copyright (c) 2026 Zhan Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhan Shi
-/
module

public import Mathlib.Analysis.Analytic.Composition
public import AInfinity.StasheffIndex

/-! # Auxiliary results on compositions for the composition of A∞-functors

This file collects the combinatorial results on Mathlib's `Composition` used in the proof that the
composite of A∞-functors is an A∞-functor: lemmas on two-level compositions, and the composition
`StasheffIndex.outerComposition` of the inputs of an index triple of the Stasheff identities into
the inputs of its outer operation.

The lemmas on two-level compositions describe the blocks of the two components `Composition.gather`
and `Composition.sigmaCompositionAux` of Mathlib's `Composition.sigmaEquivSigmaPi`.

## Main definitions

* `AInfinityTheory.StasheffIndex.outerComposition`: the composition of the inputs of an index
  triple into the inputs of its outer operation.
* `AInfinityTheory.StasheffIndex.outerMark`: the outer composition of an index triple, with the
  block of the inputs of the inner operation marked.

## Main results

* `AInfinityTheory.StasheffIndex.outerMark_injective`,
  `AInfinityTheory.StasheffIndex.mem_range_outerMark`: the index triples are the compositions with
  a marked block all of whose other blocks have size one.
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

namespace Composition

variable {n : ℕ} (c : Composition n)

/-- A composition is determined by its number of blocks and the positions of its blocks. -/
lemma ext_of_sizeUpTo {c' : Composition n} (hl : c.length = c'.length)
    (h : ∀ i, c.sizeUpTo i = c'.sizeUpTo i) : c = c' :=
  Composition.ext (List.ext_getElem hl fun i h₁ h₂ ↦
    blocksFun_eq_of_sizeUpTo_eq_add (l₁ := ⟨i, h₁⟩) (l₂ := ⟨i, h₂⟩) (m := 0)
      (by simpa using h i) (by simpa using h (i + 1)))

/-- A composition with a marked block is determined by the composition and the position of the
marked block. -/
lemma sigma_fin_ext {c₁ c₂ : Composition n} {m₁ : Fin c₁.length} {m₂ : Fin c₂.length}
    (hc : c₁ = c₂) (hm : (m₁ : ℕ) = m₂) :
    (⟨c₁, m₁⟩ : Σ c : Composition n, Fin c.length) = ⟨c₂, m₂⟩ := by
  subst hc
  exact congrArg _ (Fin.ext hm)

/-- The positions of the blocks of a composition all of whose blocks other than `m` have size
one. -/
lemma sizeUpTo_of_blocksFun_eq_one (m : Fin c.length) (h : ∀ l, l ≠ m → c.blocksFun l = 1)
    (k : ℕ) (hk : k ≤ c.length) :
    c.sizeUpTo k = if k ≤ m then k else k + c.blocksFun m - 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h₁ : c.sizeUpTo (k + 1) = c.sizeUpTo k + c.blocksFun ⟨k, hk⟩ := c.sizeUpTo_succ' ⟨k, hk⟩
    have ih := ih (Nat.le_of_succ_le hk)
    have hpos := c.one_le_blocksFun m
    rcases lt_trichotomy k m with hlt | heq | hgt
    · have := h ⟨k, hk⟩ (Fin.ne_of_val_ne hlt.ne)
      split_ifs at ih ⊢ <;> omega
    · have : c.blocksFun ⟨k, hk⟩ = c.blocksFun m := congrArg c.blocksFun (Fin.ext heq)
      split_ifs at ih ⊢ <;> omega
    · have := h ⟨k, hk⟩ (Fin.ne_of_val_ne hgt.ne')
      split_ifs at ih ⊢ <;> omega

/-- The number of blocks of a composition all of whose blocks other than `m` have size one. -/
lemma length_add_blocksFun_of_blocksFun_eq_one (m : Fin c.length)
    (h : ∀ l, l ≠ m → c.blocksFun l = 1) : c.length + c.blocksFun m = n + 1 := by
  have hlen := c.sizeUpTo_of_blocksFun_eq_one m h c.length le_rfl
  have := m.2
  have := c.one_le_blocksFun m
  rw [c.sizeUpTo_length] at hlen
  split_ifs at hlen <;> omega

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

/-- The blocks of the outer composition other than the block of the inputs of the inner operation
have size one. -/
lemma blocksFun_outerComposition_of_ne (l : Fin p.outerComposition.length)
    (hl : (l : ℕ) ≠ p.r) : p.outerComposition.blocksFun l = 1 := by
  have h₁ := p.outerComposition.sizeUpTo_succ' l
  have h₂ := p.sizeUpTo_outerComposition l
  have h₃ := p.sizeUpTo_outerComposition (l + 1)
  have hl' : (l : ℕ) < p.r + 1 + p.t := lt_of_lt_of_eq l.2 p.length_outerComposition
  have := p.sum_eq
  have := p.one_le_s
  split_ifs at h₂ h₃ <;> omega

/-- The positions of the inputs of the blocks of the outer composition. -/
lemma val_embedding_outerComposition (l : Fin p.outerComposition.length)
    (i : Fin (p.outerComposition.blocksFun l)) :
    (p.outerComposition.embedding l i : ℕ) =
      (if (l : ℕ) ≤ p.r then (l : ℕ) else l + p.s - 1) + i := by
  have hl : (l : ℕ) < p.r + 1 + p.t := lt_of_lt_of_eq l.2 p.length_outerComposition
  have := p.sum_eq
  have := p.one_le_s
  rw [Composition.coe_embedding, p.sizeUpTo_outerComposition]
  split_ifs <;> omega

/-- The block of the inputs of the inner operation, among the blocks of the outer composition. -/
abbrev outerMiddle : Fin p.outerComposition.length :=
  p.middleIndex.cast p.length_outerComposition.symm

/-- The outer composition of an index triple, with the block of the inputs of the inner operation
marked. -/
abbrev outerMark : Σ c : Composition n, Fin c.length :=
  ⟨p.outerComposition, p.outerMiddle⟩

/-- An index triple is determined by its outer composition with its marked block. -/
lemma outerMark_injective : Function.Injective (outerMark (n := n)) := by
  intro p p' hp
  have hr : p.r = p'.r := congrArg (fun x : Σ c : Composition n, Fin c.length ↦ (x.2 : ℕ)) hp
  have hs : p.s = p'.s := p.blocksFun_outerComposition_middle.symm.trans
    ((congrArg (fun x : Σ c : Composition n, Fin c.length ↦ x.1.blocksFun x.2) hp).trans
      p'.blocksFun_outerComposition_middle)
  exact StasheffIndex.ext hr hs (by have := p.sum_eq; have := p'.sum_eq; omega)

/-- A composition all of whose blocks other than `m` have size one is the outer composition of
the index triple whose inner operation takes the inputs of the block `m`. -/
lemma outerComposition_eq_of_blocksFun_eq_one (c : Composition n) (m : Fin c.length)
    (h : ∀ l, l ≠ m → c.blocksFun l = 1) (hr : p.r = m) (hs : p.s = c.blocksFun m) :
    p.outerComposition = c := by
  have hlen := c.length_add_blocksFun_of_blocksFun_eq_one m h
  have := p.sum_eq
  refine Composition.ext_of_sizeUpTo _ (p.length_outerComposition.trans (by omega)) fun k ↦ ?_
  rw [p.sizeUpTo_outerComposition, hr, hs]
  rcases le_or_gt k c.length with hkl | hkl
  · have := c.sizeUpTo_le k
    rw [c.sizeUpTo_of_blocksFun_eq_one m h k hkl] at this ⊢
    exact min_eq_left this
  · rw [c.sizeUpTo_ofLength_le k hkl.le]
    split_ifs <;> omega

/-- A composition with a marked block is the outer composition of an index triple as soon as all
of its blocks other than the marked one have size one. -/
lemma mem_range_outerMark (x : Σ c : Composition n, Fin c.length)
    (h : ∀ l, l ≠ x.2 → x.1.blocksFun l = 1) : x ∈ Set.range (outerMark (n := n)) := by
  obtain ⟨c, m⟩ := x
  have := c.length_add_blocksFun_of_blocksFun_eq_one m h
  have := m.2
  exact ⟨⟨m, c.blocksFun m, c.length - m - 1, by omega, c.one_le_blocksFun m⟩,
    Composition.sigma_fin_ext (outerComposition_eq_of_blocksFun_eq_one _ c m h rfl rfl) rfl⟩

end StasheffIndex

end AInfinityTheory
