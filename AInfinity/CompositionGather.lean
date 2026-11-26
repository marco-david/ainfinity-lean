/-
Copyright (c) 2026 Zhan Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhan Shi, Marco David
-/
module

public import Mathlib.Analysis.Analytic.Composition

/-! # Two-level compositions

For a composition `a` of `n` and a composition `b` of `a.length`, the blocks of `a.gather b` are
the groups of consecutive blocks of `a` given by `b`, and `a.sigmaCompositionAux b` records how
each of them splits into blocks of `a`. These are the two components of Mathlib's equivalence
`Composition.sigmaEquivSigmaPi`. This file describes the positions and the inputs of their blocks.

## Main results

* `Composition.sizeUpTo_gather`, `Composition.sizeUpTo_sizeUpTo_add_boundary`: the positions of
  the blocks of `a.gather b` and of `a.sigmaCompositionAux b`.
* `Composition.gather_embedding_sigmaCompositionAux_embedding`: an input of a block of `a` is the
  same input of the corresponding block of `a.sigmaCompositionAux b`, inside the corresponding block
  of `a.gather b`.
* `Composition.embedding_cast_eq_embedding_iff`: the blocks of `a` correspond to the pairs of a
  block of `a.gather b` and a block of `a.sigmaCompositionAux b` inside it.

## Implementation notes

The declarations are generic and live in Mathlib's namespaces, as candidates for upstreaming. They
are kept apart from `AInfinity.Composition` because `Mathlib.Analysis.Analytic.Composition` is a
heavy import.
-/

@[expose] public section

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

/-- A block of `a` inside a group of blocks given by `b` is determined by the group and its
position in the group, also after the identification of the groups with the blocks of
`a.gather b` and of the blocks in a group with the blocks of `a.sigmaCompositionAux b`. -/
lemma embedding_cast_eq_embedding_iff (i : Fin b.length) (j : Fin (b.blocksFun i))
    (l : Fin (a.gather b).length) (q : Fin (a.sigmaCompositionAux b l).length) :
    b.embedding (l.cast (a.length_gather b))
        (q.cast (a.length_sigmaCompositionAux b (l.cast (a.length_gather b)))) =
        b.embedding i j ↔
      (⟨l, q⟩ : Σ l : Fin (a.gather b).length, Fin (a.sigmaCompositionAux b l).length) =
        ⟨i.cast (a.length_gather b).symm, j.cast (a.length_sigmaCompositionAux b i).symm⟩ := by
  constructor
  · intro hE
    have hS := b.blocksFinEquiv.injective (a₁ := ⟨_, _⟩) (a₂ := ⟨i, j⟩) hE
    obtain ⟨rfl, hq⟩ := Sigma.mk.inj_iff.1 hS
    obtain rfl := eq_of_heq hq
    rfl
  · intro hS
    obtain ⟨rfl, hq⟩ := Sigma.mk.inj_iff.1 hS
    obtain rfl := eq_of_heq hq
    rfl

end Composition
