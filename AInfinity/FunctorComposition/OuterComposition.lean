/-
Copyright (c) 2026 Zhan Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhan Shi
-/
module

public import AInfinity.Composition
public import AInfinity.StasheffIndex

/-! # The outer composition of an index triple

An index triple (r, s, t) of the arity-n Stasheff identities determines a composition of `n`, the
composition `StasheffIndex.outerComposition` of the inputs into the inputs of the outer operation:
r blocks of size one, the block of size s of the inputs of the inner operation, and t blocks of
size one. Marking the middle block identifies the index triples with the compositions with a marked
block all of whose other blocks have size one. This is how the left-hand side of the A∞-functor
equation, a sum over index triples, is matched with a composite of composable multilinear maps in
`AInfinity.FunctorComposition.StasheffSum`.

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
