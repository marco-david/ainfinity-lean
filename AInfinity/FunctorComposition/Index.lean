/-
Copyright (c) 2026 Zhan Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhan Shi
-/
module

public import Mathlib.Analysis.Analytic.Composition
public import AInfinity.AInfinityFunctor

/-! # Index types for the functor equation of a composite of A∞-functors

The left-hand side of the functor equation for `G.comp F` is a sum of terms
$$G_k(F_{i_1}(\dots), \dots, F_{i_j}(\dots, m_s(\dots), \dots), \dots, F_{i_k}(\dots)),$$
and the left-hand side of the functor equation for `G` on the values of `F`, summed over all
compositions, is a sum of terms
$$G_k(F_{i_1}(\dots), \dots, m_s(F(\dots), \dots, F(\dots)), \dots, F_{i_k}(\dots)).$$
Each such term has two descriptions: the one in which it appears in the sum, and one by a
composition of `n` into the inputs of the outer component of `G`, the input that contains the
inner operation, and the position of the inner operation inside that input. This file records
both descriptions in the index types `MapCompIndex` and `CompMapIndex`, related only by
equalities of natural numbers, and states the combinatorial facts about them that the
reindexing in `AInfinity.FunctorComposition.Reindex` relies on: the projections onto the two
descriptions are bijections, and the Koszul signs of a term in its two descriptions are related
by `tailSign`.

Similarly, the right-hand side of the functor equation for `G.comp F` and the sum, over all
compositions, of the right-hand sides of the functor equations for `G` on the values of `F` are
sums of terms
$$m''_k(G(F(\dots), \dots, F(\dots)), \dots, G(F(\dots), \dots, F(\dots))),$$
whose two descriptions are recorded in the index type `CompMapMapIndex`. Mathlib's
`Composition.sigmaEquivSigmaPi` matches them; the lemmas on two-level compositions at the
beginning of this file relate it to `CompMapMapIndex`.

## Main definitions

* `AInfinityTheory.MapCompIndex`: the indices of the terms
  G_k(F, …, F(…, mₛ, …), …, F).
* `AInfinityTheory.CompMapIndex`: the indices of the terms G_k(F, …, mₛ(F, …, F), …, F).
* `AInfinityTheory.CompMapMapIndex`: the indices of the terms m''(G(F, …, F), …, G(F, …, F)).
* `AInfinityTheory.tailSign`: the Koszul sign of the inputs from a given position on.

## Main results

* `AInfinityTheory.MapCompIndex.bijective_toSigma`,
  `AInfinityTheory.MapCompIndex.bijective_toBlock`,
  `AInfinityTheory.CompMapIndex.bijective_toSigma`,
  `AInfinityTheory.CompMapIndex.bijective_toBlock`,
  `AInfinityTheory.CompMapMapIndex.bijective_toSigma`,
  `AInfinityTheory.CompMapMapIndex.bijective_toSigmaPi`: the projections of the index types onto the
  two descriptions of a term are bijections.
* `AInfinityTheory.MapCompIndex.stasheffSign_eq`, `AInfinityTheory.CompMapIndex.stasheffSign_eq`:
  the Koszul signs of a term in its two descriptions.

## Implementation notes

The bijectivity statements and the sign identities are still stubbed with `sorry`.
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

open GradedLinearQuiver

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

/-! ### The index types -/

/-- The indices of a term
G_k(F_{i₁}(…), …, F_{i_j}(…, mₛ(…), …), …, F_{i_k}(…))
of the left-hand side of the arity-n functor equation for a composite `G.comp F`, in its two
descriptions. In the sum, it is indexed by the triple q = (r, s, t) of the inner operation mₛ
and by a composition c of r + 1 + t into the blocks of inputs of the components of `F`. It is
also described by the composition c̃ of `n` into the blocks of original inputs consumed by the
components of `F`, the block j containing mₛ, and the index triple q' of mₛ inside that block.
-/
@[ext]
structure MapCompIndex (n : ℕ) where
  /-- The index triple q = (r, s, t) of the inner operation mₛ among the `n` inputs. -/
  stasheff : StasheffIndex n
  /-- The composition c of r + 1 + t into the blocks of inputs of the components of `F`. -/
  composition : Composition (stasheff.r + 1 + stasheff.t)
  /-- The composition c̃ of `n` into the blocks of original inputs consumed by the components
  of `F`. -/
  outer : Composition n
  /-- The block j of `outer` that contains the inner operation. -/
  block : Fin outer.length
  /-- The index triple q' of the inner operation inside the block `block`. -/
  inner : StasheffIndex (outer.blocksFun block)
  /-- Both descriptions have the same number of components of `F`. -/
  length_eq : composition.length = outer.length
  /-- The inner operation starts at the same input in both descriptions. -/
  r_eq : stasheff.r = outer.sizeUpTo block + inner.r
  /-- The inner operation has the same arity in both descriptions. -/
  s_eq : stasheff.s = inner.s
  /-- Up to the block of the inner operation, the blocks start at the same inputs. -/
  sizeUpTo_of_le : ∀ l ≤ (block : ℕ), composition.sizeUpTo l = outer.sizeUpTo l
  /-- After the block of the inner operation, the blocks of `composition` are shifted back by
  s - 1, the number of inputs absorbed by the inner operation beyond one. -/
  sizeUpTo_of_lt : ∀ l, (block : ℕ) < l →
    composition.sizeUpTo l + stasheff.s = outer.sizeUpTo l + 1

/-- The indices of a term G_k(F_{i₁}(…), …, mₛ(F(…), …, F(…)), …, F_{i_k}(…)) of the left-hand
side of the functor equation for `G` on the values of `F`, summed over all compositions, in its
two descriptions. In the sum, it is indexed by a composition c of `n` into the blocks of inputs
of the components of `F` and by the index triple p = (r, s, t) of mₛ among the values of `F`.
It is also described by the composition c̃ of `n` obtained by merging the s blocks of c fed to
mₛ, the merged block j, and the composition c'' of that block into the s blocks of c. -/
@[ext]
structure CompMapIndex (n : ℕ) where
  /-- The composition c of `n` into the blocks of inputs of the components of `F`. -/
  composition : Composition n
  /-- The index triple p = (r, s, t) of the inner operation among the values of `F`. -/
  stasheff : StasheffIndex composition.length
  /-- The composition c̃ of `n` into the blocks of original inputs of the inputs of the outer
  component of `G`. -/
  outer : Composition n
  /-- The block j of `outer` that contains the inner operation. -/
  block : Fin outer.length
  /-- The composition c'' of the block `block` into the blocks of `composition` it contains. -/
  inner : Composition (outer.blocksFun block)
  /-- The inner operation is the `block`-th input of the outer component of `G`. -/
  r_eq : stasheff.r = block
  /-- The inner operation is applied to the values of `F` on the blocks of `inner`. -/
  s_eq : stasheff.s = inner.length
  /-- Both descriptions give the outer component of `G` the same arity. -/
  length_eq : stasheff.r + 1 + stasheff.t = outer.length
  /-- Up to the merged block, the blocks of both compositions start at the same inputs. -/
  sizeUpTo_of_le : ∀ l ≤ (block : ℕ), composition.sizeUpTo l = outer.sizeUpTo l
  /-- Inside the merged block, the blocks of `composition` are those of `inner`. -/
  sizeUpTo_add : ∀ u ≤ inner.length,
    composition.sizeUpTo (block + u) = outer.sizeUpTo block + inner.sizeUpTo u
  /-- After the merged block, the blocks of both compositions start at the same inputs. -/
  sizeUpTo_add_length : ∀ v,
    composition.sizeUpTo (block + inner.length + v) = outer.sizeUpTo (block + 1 + v)

namespace MapCompIndex

/-- The description of a term of the left-hand side of the functor equation for `G.comp F` by
which it appears in the sum: an index triple q = (r, s, t) and a composition of r + 1 + t. -/
def toSigma (x : MapCompIndex n) : Σ q : StasheffIndex n, Composition (q.r + 1 + q.t) :=
  ⟨x.stasheff, x.composition⟩

/-- The description of a term of the left-hand side of the functor equation for `G.comp F` by a
composition of `n`, one of its blocks and an index triple inside that block. -/
def toBlock (x : MapCompIndex n) :
    Σ c : Composition n, Σ j : Fin c.length, StasheffIndex (c.blocksFun j) :=
  ⟨x.outer, x.block, x.inner⟩

lemma injective_toSigma_prod_toBlock :
    Function.Injective fun x : MapCompIndex n ↦ (x.toSigma, x.toBlock) := by
  rintro ⟨q, c, o, j, i, _⟩ ⟨q', c', o', j', i', _⟩ h
  simp only [toSigma, toBlock, Prod.mk.injEq, Sigma.mk.injEq] at h
  obtain ⟨⟨rfl, hc⟩, rfl, hb⟩ := h
  obtain ⟨rfl, hi⟩ := Sigma.mk.inj (eq_of_heq hb)
  cases hc
  cases hi
  rfl

/-- The indices of the terms of the left-hand side of the functor equation for `G.comp F` form a
finite type, through their two descriptions. -/
instance : Fintype (MapCompIndex n) :=
  .ofInjective _ injective_toSigma_prod_toBlock

/-- Every pair of an index triple q = (r, s, t) and a composition of r + 1 + t describes exactly
one term. -/
theorem bijective_toSigma : Function.Bijective (toSigma (n := n)) := by
  sorry

/-- Every triple of a composition of `n`, one of its blocks and an index triple inside that block
describes exactly one term. -/
theorem bijective_toBlock : Function.Bijective (toBlock (n := n)) := by
  sorry

variable (x : MapCompIndex n) (l : Fin x.composition.length)

/-- The blocks of `x.composition` and of `x.outer` match: the blocks before the block of the
inner operation are equal and lie before it, the block of the inner operation shrinks to its
index triple, and the blocks after it are equal and shifted by s - 1. -/
lemma block_cases :
    ((l : ℕ) < x.block ∧ x.composition.sizeUpTo l = x.outer.sizeUpTo l ∧
        x.composition.blocksFun l = x.outer.blocksFun (l.cast x.length_eq) ∧
        x.composition.sizeUpTo l + x.composition.blocksFun l ≤ x.stasheff.r) ∨
      ((l : ℕ) = x.block ∧ x.composition.sizeUpTo l = x.outer.sizeUpTo x.block ∧
        x.composition.blocksFun l = x.inner.r + 1 + x.inner.t) ∨
      ((x.block : ℕ) < l ∧ x.composition.sizeUpTo l + x.stasheff.s = x.outer.sizeUpTo l + 1 ∧
        x.composition.blocksFun l = x.outer.blocksFun (l.cast x.length_eq) ∧
        x.stasheff.r < x.composition.sizeUpTo l) := by
  have h₁ := x.composition.sizeUpTo_succ' l
  have h₂ := x.outer.sizeUpTo_succ' (l.cast x.length_eq)
  have h₃ := x.outer.sizeUpTo_succ' x.block
  have := x.r_eq; have := x.s_eq; have := x.inner.sum_eq; have := x.stasheff.one_le_s
  simp only [Fin.val_cast] at h₂
  rcases lt_trichotomy (l : ℕ) x.block with h | h | h
  · have := x.sizeUpTo_of_le l h.le; have := x.sizeUpTo_of_le (l + 1) h
    have := x.outer.monotone_sizeUpTo (show (l : ℕ) + 1 ≤ x.block by omega)
    omega
  · have := x.sizeUpTo_of_le x.block le_rfl; have := x.sizeUpTo_of_lt (x.block + 1) (by omega)
    rw [h] at h₁ ⊢
    omega
  · have := x.sizeUpTo_of_lt l h; have := x.sizeUpTo_of_lt (l + 1) (by omega)
    have := x.outer.monotone_sizeUpTo (show (x.block : ℕ) + 1 ≤ l by omega)
    omega

lemma sizeUpTo_of_eq (hl : (l : ℕ) = x.block) :
    x.composition.sizeUpTo l = x.outer.sizeUpTo x.block := by
  rcases x.block_cases l with ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨h, -⟩ <;> omega

lemma blocksFun_of_eq (hl : (l : ℕ) = x.block) :
    x.composition.blocksFun l = x.inner.r + 1 + x.inner.t := by
  rcases x.block_cases l with ⟨h, -⟩ | ⟨-, -, h⟩ | ⟨h, -⟩ <;> omega

/-- The boundaries of `x.outer` are the images of the boundaries of `x.composition` under the
positions of the objects of the outer operation of the index triple `x.stasheff`. -/
lemma outerBoundary_sizeUpTo (k : ℕ) :
    (if x.composition.sizeUpTo k ≤ x.stasheff.r then x.composition.sizeUpTo k
      else x.composition.sizeUpTo k + x.stasheff.s - 1) = x.outer.sizeUpTo k := by
  have h₃ := x.outer.sizeUpTo_succ' x.block
  have := x.r_eq; have := x.s_eq; have := x.inner.sum_eq; have := x.stasheff.one_le_s
  rcases le_or_gt k x.block with h | h
  · have := x.outer.monotone_sizeUpTo h
    rw [x.sizeUpTo_of_le k h, ite_eq_left_iff.2 fun h' ↦ absurd (by omega) h']
  · have := x.sizeUpTo_of_lt k h
    have := x.outer.monotone_sizeUpTo (show (x.block : ℕ) + 1 ≤ k by omega)
    split_ifs <;> omega

end MapCompIndex

namespace CompMapIndex

/-- The description of a term of the left-hand side of the functor equation for `G` on the
values of `F` by which it appears in the sum: a composition c of `n` and an index triple of
arity `c.length`. -/
def toSigma (x : CompMapIndex n) : Σ c : Composition n, StasheffIndex c.length :=
  ⟨x.composition, x.stasheff⟩

/-- The description of a term of the left-hand side of the functor equation for `G` on the
values of `F` by a composition of `n`, one of its blocks and a composition of that block. -/
def toBlock (x : CompMapIndex n) :
    Σ c : Composition n, Σ j : Fin c.length, Composition (c.blocksFun j) :=
  ⟨x.outer, x.block, x.inner⟩

lemma injective_toSigma_prod_toBlock :
    Function.Injective fun x : CompMapIndex n ↦ (x.toSigma, x.toBlock) := by
  rintro ⟨c, p, o, j, i, _⟩ ⟨c', p', o', j', i', _⟩ h
  simp only [toSigma, toBlock, Prod.mk.injEq, Sigma.mk.injEq] at h
  obtain ⟨⟨rfl, hp⟩, rfl, hb⟩ := h
  obtain ⟨rfl, hi⟩ := Sigma.mk.inj (eq_of_heq hb)
  cases hp
  cases hi
  rfl

/-- The indices of the terms of the left-hand side of the functor equation for `G` on the values
of `F` form a finite type, through their two descriptions. -/
instance : Fintype (CompMapIndex n) :=
  .ofInjective _ injective_toSigma_prod_toBlock

/-- Every pair of a composition c of `n` and an index triple of arity `c.length` describes
exactly one term. -/
theorem bijective_toSigma : Function.Bijective (toSigma (n := n)) := by
  sorry

/-- Every triple of a composition of `n`, one of its blocks and a composition of that block
describes exactly one term. -/
theorem bijective_toBlock : Function.Bijective (toBlock (n := n)) := by
  sorry

variable (x : CompMapIndex n)

/-- The boundaries of `x.outer` are the boundaries of `x.composition` at the positions of the
objects of the outer operation of the index triple `x.stasheff`. -/
lemma sizeUpTo_outerBoundary (k : ℕ) :
    x.composition.sizeUpTo (if k ≤ x.stasheff.r then k else k + x.stasheff.s - 1) =
      x.outer.sizeUpTo k := by
  have := x.r_eq; have := x.s_eq; have := x.stasheff.one_le_s
  split_ifs with h
  · exact x.sizeUpTo_of_le k (by omega)
  · have := x.sizeUpTo_add_length (k - x.block - 1)
    rwa [show (x.block : ℕ) + x.inner.length + (k - x.block - 1) = k + x.stasheff.s - 1 by omega,
      show (x.block : ℕ) + 1 + (k - x.block - 1) = k by omega] at this

lemma sizeUpTo_innerIndex (u : Fin x.stasheff.s) :
    x.composition.sizeUpTo (x.stasheff.innerIndex u) =
      x.outer.sizeUpTo x.block + x.inner.sizeUpTo (u.cast x.s_eq) := by
  have := x.s_eq
  simpa [x.r_eq] using x.sizeUpTo_add u (by omega)

lemma blocksFun_innerIndex (u : Fin x.stasheff.s) :
    x.composition.blocksFun (x.stasheff.innerIndex u) = x.inner.blocksFun (u.cast x.s_eq) := by
  have := x.s_eq
  exact Composition.blocksFun_eq_of_sizeUpTo_eq_add (x.sizeUpTo_innerIndex u)
    (by simpa [x.r_eq, add_assoc] using x.sizeUpTo_add (u + 1) (by omega))

/-- The value of `F` in the `l`-th input of the outer component of `G`, for `l ≠ r`, is on a block
of `x.composition` in the same position and of the same size as the `l`-th block of `x.outer`. -/
lemma sizeUpTo_blocksFun_of_ne (l : Fin (x.stasheff.r + 1 + x.stasheff.t))
    (i : Fin x.composition.length) (hl : (l : ℕ) ≠ x.stasheff.r)
    (hi : (i : ℕ) = if (l : ℕ) < x.stasheff.r then (l : ℕ) else (l : ℕ) + x.stasheff.s - 1) :
    x.composition.sizeUpTo i = x.outer.sizeUpTo (l.cast x.length_eq) ∧
      x.composition.blocksFun i = x.outer.blocksFun (l.cast x.length_eq) := by
  have h₁ := x.sizeUpTo_outerBoundary l
  have h₂ := x.sizeUpTo_outerBoundary (l + 1)
  have := x.stasheff.one_le_s
  have hs : x.composition.sizeUpTo i = x.outer.sizeUpTo (l.cast x.length_eq) := by
    rw [Fin.val_cast, ← h₁, hi]; congr 1; split_ifs <;> omega
  refine ⟨hs, Composition.blocksFun_eq_of_sizeUpTo_eq_add (m := 0) (by simpa using hs) ?_⟩
  rw [zero_add, Fin.val_cast, ← h₂, hi]; congr 1; split_ifs <;> omega

end CompMapIndex

/-- The indices of a term m''(G(F(…), …, F(…)), …, G(F(…), …, F(…))) of the right-hand side of
the functor equation for a composite `G.comp F`, in its two descriptions. In the sum, over all
compositions, of the right-hand sides of the functor equations for `G` on the values of `F`, it is
indexed by a composition c of `n` into the blocks of inputs of the components of `F` and by a
composition c' of `c.length` grouping the values of `F` into the inputs of the components of `G`.
In the right-hand side of the functor equation for `G.comp F`, it is indexed by a composition e of
`n` into the blocks of inputs of the components of `G.comp F` and by the compositions of the
blocks of `e` into the blocks of c. -/
@[ext]
structure CompMapMapIndex (n : ℕ) where
  /-- The composition c of `n` into the blocks of inputs of the components of `F`. -/
  composition : Composition n
  /-- The composition c' of `composition.length` grouping the values of `F` into the inputs of the
  components of `G`. -/
  grouping : Composition composition.length
  /-- The composition e of `n` into the blocks of original inputs consumed by the components of
  `G`. -/
  outer : Composition n
  /-- The composition of each block of `outer` into the blocks of `composition` it contains. -/
  inner : ∀ l : Fin outer.length, Composition (outer.blocksFun l)
  /-- Both descriptions have the same number of components of `G`. -/
  length_eq : grouping.length = outer.length
  /-- Each component of `G` is applied to the same number of values of `F` in both
  descriptions. -/
  length_inner : ∀ l : Fin grouping.length,
    (inner (l.cast length_eq)).length = grouping.blocksFun l
  /-- Inside each input of the outer operation, the blocks of `composition` are those of
  `inner`. -/
  sizeUpTo_add : ∀ (l : Fin grouping.length), ∀ u ≤ grouping.blocksFun l,
    composition.sizeUpTo (grouping.sizeUpTo l + u) =
      outer.sizeUpTo l + (inner (l.cast length_eq)).sizeUpTo u

namespace CompMapMapIndex

/-- The description of a term of the right-hand side of the functor equation for `G.comp F` by
which it appears in the sum of the right-hand sides of the functor equations for `G` on the values
of `F`: a composition c of `n` and a composition of `c.length`. -/
def toSigma (x : CompMapMapIndex n) : Σ c : Composition n, Composition c.length :=
  ⟨x.composition, x.grouping⟩

/-- The description of a term of the right-hand side of the functor equation for `G.comp F` by
which it appears in that sum: a composition of `n` and a composition of each of its blocks. -/
def toSigmaPi (x : CompMapMapIndex n) :
    Σ e : Composition n, ∀ l : Fin e.length, Composition (e.blocksFun l) :=
  ⟨x.outer, x.inner⟩

lemma injective_toSigma_prod_toSigmaPi :
    Function.Injective fun x : CompMapMapIndex n ↦ (x.toSigma, x.toSigmaPi) := by
  rintro ⟨c, g, o, i, _⟩ ⟨c', g', o', i', _⟩ h
  simp only [toSigma, toSigmaPi, Prod.mk.injEq, Sigma.mk.injEq] at h
  obtain ⟨⟨rfl, hg⟩, rfl, hi⟩ := h
  cases hg
  cases hi
  rfl

/-- The indices of the terms of the right-hand side of the functor equation for `G.comp F` form a
finite type, through their two descriptions. -/
instance : Fintype (CompMapMapIndex n) :=
  .ofInjective _ injective_toSigma_prod_toSigmaPi

/-- Every pair of a composition c of `n` and a composition of `c.length` describes exactly one
term. It is the image of the pair under `Composition.sigmaEquivSigmaPi`, whose relations to the
pair are `Composition.sizeUpTo_sizeUpTo_add_boundary` and `Composition.length_sigmaCompositionAux`.
-/
theorem bijective_toSigma : Function.Bijective (toSigma (n := n)) := by
  sorry

/-- Every pair of a composition of `n` and a composition of each of its blocks describes exactly
one term. -/
theorem bijective_toSigmaPi : Function.Bijective (toSigmaPi (n := n)) := by
  sorry

variable (x : CompMapMapIndex n)

/-- The boundaries of `x.outer` are the boundaries of `x.composition` at the boundaries of
`x.grouping`. -/
lemma sizeUpTo_sizeUpTo (k : ℕ) :
    x.composition.sizeUpTo (x.grouping.sizeUpTo k) = x.outer.sizeUpTo k := by
  rcases lt_or_ge k x.grouping.length with hk | hk
  · simpa using x.sizeUpTo_add ⟨k, hk⟩ 0 (Nat.zero_le _)
  · rw [x.grouping.sizeUpTo_ofLength_le k hk, x.composition.sizeUpTo_length,
      x.outer.sizeUpTo_ofLength_le k (x.length_eq ▸ hk)]

lemma sizeUpTo_embedding (l : Fin x.grouping.length) (j : Fin (x.grouping.blocksFun l)) :
    x.composition.sizeUpTo (x.grouping.embedding l j) =
      x.outer.sizeUpTo (l.cast x.length_eq) +
        (x.inner (l.cast x.length_eq)).sizeUpTo (j.cast (x.length_inner l).symm) := by
  simpa [Composition.coe_embedding] using x.sizeUpTo_add l j j.2.le

lemma blocksFun_embedding (l : Fin x.grouping.length) (j : Fin (x.grouping.blocksFun l)) :
    x.composition.blocksFun (x.grouping.embedding l j) =
      (x.inner (l.cast x.length_eq)).blocksFun (j.cast (x.length_inner l).symm) :=
  Composition.blocksFun_eq_of_sizeUpTo_eq_add (x.sizeUpTo_embedding l j)
    (by simpa [Composition.coe_embedding, add_assoc] using x.sizeUpTo_add l (j + 1) j.2)

end CompMapMapIndex

/-! ### Koszul signs -/

section Signs

variable {β : Type*} [AddCommGroup β] [Grading β]

/-- The Koszul sign of the inputs from position `N` on: (-1) raised to the sum of the reduced
degrees ‖a‖ = |a| - 1 of the inputs at positions `i ≥ N`. -/
def tailSign (deg : Fin n → β) (N : ℕ) : ℤˣ :=
  ∏ i ∈ Finset.univ.filter (fun i : Fin n ↦ N ≤ (i : ℕ)), (sign (deg i - degOne)).toMul

/-- The Koszul sign of a term of the left-hand side of the functor equation for `G.comp F` is the
Koszul sign of the inner operation inside its block, times the Koszul sign of the inputs after
that block. -/
theorem MapCompIndex.stasheffSign_eq (deg : Fin n → β) (x : MapCompIndex n) :
    stasheffSign deg x.stasheff =
      stasheffSign (fun i ↦ deg (x.outer.embedding x.block i)) x.inner *
        tailSign deg (x.outer.sizeUpTo (x.block + 1)) := by
  sorry

/-- The Koszul sign of a term of the left-hand side of the functor equation for `G` on the
values of `F` is the Koszul sign of the original inputs after the merged block. -/
theorem CompMapIndex.stasheffSign_eq {β' : Type*} [AddCommGroup β'] [Grading β'] (φ : β →+ᵍ β')
    (deg : Fin n → β) (x : CompMapIndex n) :
    stasheffSign (fun l ↦ φ (functorTargetDeg fun i ↦ deg (x.composition.embedding l i)))
        x.stasheff =
      tailSign deg (x.outer.sizeUpTo (x.block + 1)) := by
  sorry

end Signs

end AInfinityTheory
