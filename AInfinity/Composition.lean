/-
Copyright (c) 2026 Zhan Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhan Shi, Marco David
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Combinatorics.Enumerative.Composition
public import Mathlib.Tactic.Ring

/-! # Lemmas on compositions

This file collects lemmas on Mathlib's `Composition n`, the decompositions i₁ + ⋯ + iₖ = n of `n`
into positive integers. A composition `c` cuts a string of `n` inputs into k blocks: the `l`-th
block has size `c.blocksFun l` and starts at position `c.sizeUpTo l`.

## Main results

* `Composition.neZero_blocksFun`, `Composition.neZero_length`: the blocks of a composition are
  nonempty, and a composition of a positive integer has at least one block.
* `Composition.ext_of_sizeUpTo`: a composition is determined by the positions of its blocks.
* `Composition.sizeUpTo_of_blocksFun_eq_one`: the positions of the blocks of a composition all of
  whose blocks but one have size one.
* `Composition.sizeUpTo_le_embedding_iff`: comparing the position of an input with the start of a
  block.

## Implementation notes

The declarations are generic and live in Mathlib's namespaces, as candidates for upstreaming. The
lemmas on two-level compositions, which need `Composition.gather`, are in
`AInfinity.CompositionGather`.
-/

@[expose] public section

namespace Composition

variable {n : ℕ} (c : Composition n)

/-- Every block of a composition is nonempty. -/
instance neZero_blocksFun (l : Fin c.length) : NeZero (c.blocksFun l) :=
  NeZero.of_pos (c.one_le_blocksFun l)

/-- A composition of a positive integer has at least one block. -/
instance neZero_length [NeZero n] : NeZero c.length :=
  NeZero.of_pos (c.length_pos_of_pos (NeZero.pos n))

lemma sizeUpTo_add_blocksFun_le (l : Fin c.length) : c.sizeUpTo l + c.blocksFun l ≤ n :=
  (c.sizeUpTo_succ' l).symm.trans_le (c.sizeUpTo_le _)

/-- Two blocks whose boundaries differ by the same offset `m` have the same size. -/
lemma blocksFun_eq_of_sizeUpTo_eq_add {n₁ n₂ : ℕ} {c₁ : Composition n₁}
    {c₂ : Composition n₂} {l₁ : Fin c₁.length} {l₂ : Fin c₂.length} {m : ℕ}
    (h : c₁.sizeUpTo l₁ = m + c₂.sizeUpTo l₂)
    (h' : c₁.sizeUpTo (l₁ + 1) = m + c₂.sizeUpTo (l₂ + 1)) :
    c₁.blocksFun l₁ = c₂.blocksFun l₂ := by
  have := c₁.sizeUpTo_succ' l₁
  have := c₂.sizeUpTo_succ' l₂
  omega

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

/-- The `i`-th input of the block `l` lies at or after the start of the block `k` exactly when
`k ≤ l`. -/
lemma sizeUpTo_le_embedding_iff (k : ℕ) (l : Fin c.length) (i : Fin (c.blocksFun l)) :
    c.sizeUpTo k ≤ c.embedding l i ↔ k ≤ l := by
  have := c.sizeUpTo_succ' l; have := i.2
  rw [c.coe_embedding]
  refine ⟨fun h ↦ ?_, fun h ↦ (c.monotone_sizeUpTo h).trans (Nat.le_add_right _ _)⟩
  by_contra! hl
  have := c.monotone_sizeUpTo (show (l : ℕ) + 1 ≤ k by omega)
  omega

/-- Summing σₗ - iₗ over the blocks of a composition c = (i₁, …, iₖ) of `n` and adding s - k
gives s + ∑ₗ (σₗ - 1) - n. These are the degrees of maps on the blocks of `c` and of an outer map
of arity k. -/
lemma sum_sub_blocksFun_add (s : ℤ) (σ : Fin c.length → ℤ) :
    (∑ l, (σ l - (c.blocksFun l : ℤ))) + (s - c.length) = s + ∑ l, (σ l - 1) - n := by
  have := congrArg (Nat.cast (R := ℤ)) c.sum_blocksFun
  push_cast at this
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, this]
  ring

end Composition
