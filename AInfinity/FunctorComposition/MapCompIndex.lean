/-
Copyright (c) 2026 Zhan Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhan Shi
-/
module

public import AInfinity.FunctorComposition.Lemmas

/-! # The index type of the left-hand side of the functor equation for a composite

The left-hand side of the functor equation for a composite `G.comp F` of A∞-functors is a sum of
terms
$$G_k(F_{i_1}(\dots), \dots, F_{i_j}(\dots, m_s(\dots), \dots), \dots, F_{i_k}(\dots)).$$
Each such term has two descriptions: the one in which it appears in the sum, by an index triple
q = (r, s, t) and a composition of r + 1 + t, and one by a composition of `n` into the inputs of
the outer component of `G`, the input that contains the inner operation, and the position of the
inner operation inside that input. This file records both descriptions in the index type
`MapCompIndex`, related only by equalities of natural numbers, and states the combinatorial facts
about it that the reindexing in `AInfinity.FunctorComposition.Reindex` relies on.

## Main definitions

* `AInfinityTheory.MapCompIndex`: the indices of the terms G_k(F, …, F(…, mₛ, …), …, F).
* `AInfinityTheory.MapCompIndex.ofSetBlock`: the index given by the block description and a
  matching index triple, when the composition of r + 1 + t is given by shrinking the block of
  the inner operation.
* `AInfinityTheory.MapCompIndex.ofSigma`: the inverse of `MapCompIndex.toSigma`.
* `AInfinityTheory.MapCompIndex.ofBlock`: the inverse of `MapCompIndex.toBlock`.

## Main results

* `AInfinityTheory.MapCompIndex.bijective_toSigma`,
  `AInfinityTheory.MapCompIndex.bijective_toBlock`: the projections onto the two descriptions of
  a term are bijections.

The Koszul signs of a term in its two descriptions are compared in
`AInfinity.FunctorComposition.Signs`.

## Implementation notes

`MapCompIndex.ofSetBlock` reduces the relations between the two descriptions to a single
equation `composition = outer.setBlock …`, which holds for every index
(`MapCompIndex.composition_eq_setBlock`). `MapCompIndex.bijective_toSigma` and
`MapCompIndex.bijective_toBlock` are proved by the explicit inverses `MapCompIndex.ofSigma` and
`MapCompIndex.ofBlock`, both built with `MapCompIndex.ofSetBlock`.
-/

@[expose] public section

noncomputable section

namespace AInfinityTheory

variable {n : ℕ}

/-- The indices of a term
G_k(F_{i₁}(…), …, F_{i_j}(…, mₛ(…), …), …, F_{i_k}(…))
of the left-hand side of the arity-n functor equation for a composite `G.comp F`, in its two
descriptions. In the sum, it is indexed by the triple q = (r, s, t) of the inner operation mₛ
and by a composition c of r + 1 + t into the blocks of inputs of the components of `F`. It is
also described by the composition c̃ of `n` into the blocks of original inputs consumed by the
components of `F`, the block j containing mₛ, and the index triple q' of mₛ inside that block.
-/
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

/-! #### Construction from the block description -/

/-- The index of a term described by a composition `o` of `n`, one of its blocks `j`, an index
triple `i` inside that block and a matching index triple `q`, when the composition of r + 1 + t
is `o` with the block `j` shrunk to the r + 1 + t inputs of the outer operation of `i`. -/
def ofSetBlock (q : StasheffIndex n) (o : Composition n) (j : Fin o.length)
    (i : StasheffIndex (o.blocksFun j)) (r_eq : q.r = o.sizeUpTo j + i.r) (s_eq : q.s = i.s)
    (c : Composition (q.r + 1 + q.t))
    (hc : c = o.setBlock j (i.r + 1 + i.t) (by omega)
      (by have := q.sum_eq; have := i.sum_eq; omega)) : MapCompIndex n where
  stasheff := q
  composition := c
  outer := o
  block := j
  inner := i
  length_eq := by subst hc; simp
  r_eq := r_eq
  s_eq := s_eq
  sizeUpTo_of_le l hl := hc ▸ o.sizeUpTo_setBlock_of_le j _ _ _ hl
  sizeUpTo_of_lt l hl := by
    have := i.sum_eq
    have := o.sizeUpTo_setBlock_of_lt (m := q.r + 1 + q.t) j (i.r + 1 + i.t) (by omega)
      (by have := q.sum_eq; omega) hl
    rw [hc]
    omega

/-- The composition of r + 1 + t of an index is its composition of `n` with the block of the
inner operation shrunk to the r + 1 + t inputs of the outer operation of the inner index
triple. In particular, every index is given by `ofSetBlock`. -/
lemma composition_eq_setBlock (x : MapCompIndex n) :
    x.composition = x.outer.setBlock x.block (x.inner.r + 1 + x.inner.t) (by omega)
      (by have := x.stasheff.sum_eq; have := x.inner.sum_eq; have := x.s_eq; omega) := by
  refine Composition.ext_of_sizeUpTo _ (by simp [x.length_eq]) fun k ↦ ?_
  rcases le_or_gt k x.block with h | h
  · rw [x.sizeUpTo_of_le k h, x.outer.sizeUpTo_setBlock_of_le _ _ _ _ h]
  · have := x.outer.sizeUpTo_setBlock_of_lt (m := x.stasheff.r + 1 + x.stasheff.t) x.block
      (x.inner.r + 1 + x.inner.t) (by omega)
      (by have := x.stasheff.sum_eq; have := x.inner.sum_eq; have := x.s_eq; omega) h
    have := x.sizeUpTo_of_lt k h; have := x.inner.sum_eq; have := x.s_eq
    omega

lemma eq_ofSetBlock (x : MapCompIndex n) :
    x = ofSetBlock x.stasheff x.outer x.block x.inner x.r_eq x.s_eq x.composition
      x.composition_eq_setBlock :=
  rfl

/-! #### The inverse of `toSigma` -/

/-- An index is determined by its first description and the position of the block of the inner
operation: the relations between `composition` and `outer` determine `outer`, and `inner` is
then determined by `r_eq` and `s_eq`. -/
lemma ext_of_block {x₁ x₂ : MapCompIndex n} (hq : x₁.stasheff = x₂.stasheff)
    (hc : x₁.composition.blocks = x₂.composition.blocks) (hb : (x₁.block : ℕ) = x₂.block) :
    x₁ = x₂ := by
  rcases x₁ with ⟨q, c, o, b, i, hl, hr, hs, hle, hlt⟩
  rcases x₂ with ⟨q', c', o', b', i', hl', hr', hs', hle', hlt'⟩
  dsimp only at hq hc hb
  subst hq
  obtain rfl : c = c' := Composition.ext hc
  obtain rfl : o = o' := Composition.ext_of_sizeUpTo _ (hl.symm.trans hl') fun k ↦ by
    rcases le_or_gt k b with h | h
    · rw [← hle k h, hle' k (by omega)]
    · have := hlt k h; have := hlt' k (by omega); omega
  obtain rfl : b = b' := Fin.ext hb
  obtain rfl : i = i' :=
    StasheffIndex.ext (by omega) (by omega) (by have := i.sum_eq; have := i'.sum_eq; omega)
  rfl

/-- The inverse of `toSigma`. For an index triple q = (r, s, t) and a composition c of r + 1 + t,
the block j of `c` that contains the inner output, i.e. the input r of the outer operation, is
enlarged by the s - 1 further inputs of the inner operation. The inner operation starts at
position r - c.sizeUpTo j inside it. -/
def ofSigma (σ : Σ q : StasheffIndex n, Composition (q.r + 1 + q.t)) : MapCompIndex n :=
  let j := σ.2.index ⟨σ.1.r, by omega⟩
  have : σ.2.sizeUpTo j ≤ σ.1.r := σ.2.sizeUpTo_index_le _
  have : σ.1.r < σ.2.sizeUpTo j + σ.2.blocksFun j :=
    σ.2.lt_sizeUpTo_index_add_blocksFun ⟨σ.1.r, by omega⟩
  have := σ.1.one_le_s; have := σ.1.sum_eq; have := σ.2.one_le_blocksFun j
  let o := σ.2.setBlock j (σ.2.blocksFun j + σ.1.s - 1) (by omega) (by omega)
  let i : StasheffIndex (o.blocksFun (j.cast (by simp [o]))) :=
    ⟨σ.1.r - σ.2.sizeUpTo j, σ.1.s, σ.2.sizeUpTo j + σ.2.blocksFun j - 1 - σ.1.r,
      by rw [Composition.blocksFun_setBlock_self]; omega, σ.1.one_le_s⟩
  ofSetBlock σ.1 o (j.cast _) i
    (by rw [Fin.val_cast, σ.2.sizeUpTo_setBlock_of_le j _ _ _ le_rfl]; dsimp only [i]; omega) rfl
    σ.2 (σ.2.setBlock_setBlock j _ _ _ (by dsimp only [i]; omega)).symm

lemma toSigma_ofSigma (σ : Σ q : StasheffIndex n, Composition (q.r + 1 + q.t)) :
    (ofSigma σ).toSigma = σ :=
  rfl

/-- The block of `x.composition` that contains the inner output is the block of the inner
operation. -/
lemma val_index : (x.composition.index ⟨x.stasheff.r, by omega⟩ : ℕ) = x.block := by
  have := x.blocksFun_of_eq (x.block.cast x.length_eq.symm) rfl
  have := x.sizeUpTo_of_eq (x.block.cast x.length_eq.symm) rfl
  have := x.r_eq
  rw [show (⟨x.stasheff.r, _⟩ : Fin _) = x.composition.embedding (x.block.cast x.length_eq.symm)
    ⟨x.inner.r, by omega⟩ from Fin.ext (by simp only [Composition.coe_embedding]; omega),
    Composition.index_embedding, Fin.val_cast]

lemma ofSigma_toSigma : ofSigma x.toSigma = x :=
  ext_of_block rfl rfl x.val_index

/-- Every pair of an index triple q = (r, s, t) and a composition of r + 1 + t describes exactly
one term, given by `ofSigma`. -/
theorem bijective_toSigma : Function.Bijective (toSigma (n := n)) :=
  Function.bijective_iff_has_inverse.2 ⟨ofSigma, ofSigma_toSigma, toSigma_ofSigma⟩

/-- The indices of the terms of the left-hand side of the functor equation for `G.comp F` form a
finite type, through their description by an index triple and a composition. -/
instance : Fintype (MapCompIndex n) :=
  .ofEquiv _ (Equiv.ofBijective _ bijective_toSigma).symm

/-! #### The inverse of `toBlock` -/

/-- The inverse of `toBlock`. For a composition `o` of `n`, a block j of `o` and an index triple
i = (r', s, t') inside it, the inner operation takes the s inputs starting at input
o.sizeUpTo j + r', and the block j shrinks to the r' + 1 + t' inputs of the outer operation of
i. -/
def ofBlock (τ : Σ c : Composition n, Σ j : Fin c.length, StasheffIndex (c.blocksFun j)) :
    MapCompIndex n :=
  have := τ.1.sizeUpTo_succ' τ.2.1; have := τ.1.sizeUpTo_le (τ.2.1 + 1)
  have := τ.2.2.sum_eq
  ofSetBlock
    ⟨τ.1.sizeUpTo τ.2.1 + τ.2.2.r, τ.2.2.s, n - (τ.1.sizeUpTo τ.2.1 + τ.2.2.r + τ.2.2.s),
      by omega, τ.2.2.one_le_s⟩
    τ.1 τ.2.1 τ.2.2 rfl rfl _ rfl

lemma toBlock_ofBlock
    (τ : Σ c : Composition n, Σ j : Fin c.length, StasheffIndex (c.blocksFun j)) :
    (ofBlock τ).toBlock = τ :=
  rfl

lemma ofBlock_toBlock : ofBlock x.toBlock = x := by
  rcases x with ⟨q, c, o, j, i, hl, hr, hs, hle, hlt⟩
  have := q.sum_eq; have := i.sum_eq
  have hc : c = o.setBlock j (i.r + 1 + i.t) (by clear hl; omega) (by clear hl; omega) :=
    composition_eq_setBlock ⟨q, c, o, j, i, hl, hr, hs, hle, hlt⟩
  obtain rfl : q = (ofBlock ⟨o, j, i⟩).stasheff :=
    StasheffIndex.ext hr hs (by dsimp only [ofBlock, ofSetBlock]; omega)
  subst hc
  rfl

/-- Every triple of a composition of `n`, one of its blocks and an index triple inside that block
describes exactly one term, given by `ofBlock`. -/
theorem bijective_toBlock : Function.Bijective (toBlock (n := n)) :=
  Function.bijective_iff_has_inverse.2 ⟨ofBlock, ofBlock_toBlock, toBlock_ofBlock⟩

end MapCompIndex

end AInfinityTheory
