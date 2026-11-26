/-
Copyright (c) 2026 Zhan Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhan Shi
-/
module

public import AInfinity.AInfinityFunctor
public import AInfinity.FunctorComposition.Lemmas

/-! # The index type of the left-hand sides of the functor equations for `G` on the values of `F`

The left-hand side of the functor equation for `G` on the values of `F`, summed over all
compositions, is a sum of terms
$$G_k(F_{i_1}(\dots), \dots, m_s(F(\dots), \dots, F(\dots)), \dots, F_{i_k}(\dots)).$$
Each such term has two descriptions: the one in which it appears in the sum, by a composition c
of `n` and an index triple of arity `c.length`, and one by a composition of `n` into the inputs of
the outer component of `G`, the input that contains the inner operation, and the composition of
that input into the blocks of `c`. This file records both descriptions in the index type
`CompMapIndex`, related only by equalities of natural numbers, and states the combinatorial facts
about it that the reindexing in `AInfinity.FunctorComposition.Reindex` relies on.

## Main definitions

* `AInfinityTheory.CompMapIndex`: the indices of the terms G_k(F, …, mₛ(F, …, F), …, F).
* `AInfinityTheory.CompMapIndex.ofSplitBlock`: the index given by the block description and a
  matching composition with an index triple, when the composition is given by splitting the merged
  block.
* `AInfinityTheory.CompMapIndex.ofSigma`: the inverse of `CompMapIndex.toSigma`.
* `AInfinityTheory.CompMapIndex.ofBlock`: the inverse of `CompMapIndex.toBlock`.

## Main results

* `AInfinityTheory.CompMapIndex.bijective_toSigma`,
  `AInfinityTheory.CompMapIndex.bijective_toBlock`: the projections onto the two descriptions of
  a term are bijections.

The Koszul signs of a term in its two descriptions are compared in
`AInfinity.FunctorComposition.Signs`.

## Implementation notes

`CompMapIndex.ofSplitBlock` reduces the relations between the two descriptions to a single
equation `composition = outer.splitBlock block inner`, which holds for every index
(`CompMapIndex.composition_eq_splitBlock`). `CompMapIndex.bijective_toSigma` and
`CompMapIndex.bijective_toBlock` are proved by the explicit inverses `CompMapIndex.ofSigma` and
`CompMapIndex.ofBlock`, both built with `CompMapIndex.ofSplitBlock`. In `CompMapIndex.ofSigma`,
the merged block is obtained with `Composition.gather` along
`AInfinityTheory.StasheffIndex.outerComposition`.
-/

@[expose] public section

noncomputable section

namespace AInfinityTheory

variable {n : ℕ}

/-- The indices of a term G_k(F_{i₁}(…), …, mₛ(F(…), …, F(…)), …, F_{i_k}(…)) of the left-hand
side of the functor equation for `G` on the values of `F`, summed over all compositions, in its
two descriptions. In the sum, it is indexed by a composition c of `n` into the blocks of inputs
of the components of `F` and by the index triple p = (r, s, t) of mₛ among the values of `F`.
It is also described by the composition c̃ of `n` obtained by merging the s blocks of c fed to
mₛ, the merged block j, and the composition c'' of that block into the s blocks of c. -/
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

/-! #### Construction from the block description -/

/-- The index of a term described by a composition `o` of `n`, one of its blocks `j`, a
composition `i` of that block and a matching composition `c` with index triple `p`, when `c` is
`o` with the block `j` split into the blocks of `i`. -/
def ofSplitBlock (c : Composition n) (p : StasheffIndex c.length) (o : Composition n)
    (j : Fin o.length) (i : Composition (o.blocksFun j)) (r_eq : p.r = j)
    (s_eq : p.s = i.length) (hc : c = o.splitBlock j i) : CompMapIndex n where
  composition := c
  stasheff := p
  outer := o
  block := j
  inner := i
  r_eq := r_eq
  s_eq := s_eq
  length_eq := by
    have h := o.length_splitBlock j i
    rw [← hc] at h
    have := p.sum_eq; have := j.2
    omega
  sizeUpTo_of_le _ hl := hc ▸ o.sizeUpTo_splitBlock_of_le j i hl
  sizeUpTo_add _ hu := hc ▸ o.sizeUpTo_splitBlock_add j i hu
  sizeUpTo_add_length v := hc ▸ o.sizeUpTo_splitBlock_add_length j i v

/-- The composition of `n` into the blocks of inputs of the components of `F` is the composition
`x.outer` with the merged block split into the blocks of `x.inner`. In particular, every index
is given by `ofSplitBlock`. -/
lemma composition_eq_splitBlock : x.composition = x.outer.splitBlock x.block x.inner := by
  have := x.stasheff.sum_eq; have := x.length_eq; have := x.r_eq; have := x.s_eq
  have := x.outer.length_splitBlock x.block x.inner
  refine Composition.ext_of_sizeUpTo _ (by omega) fun k ↦ ?_
  rcases le_or_gt k x.block with h | h
  · rw [x.sizeUpTo_of_le k h, x.outer.sizeUpTo_splitBlock_of_le _ _ h]
  rcases le_or_gt k (x.block + x.inner.length) with h' | h'
  · obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le h.le
    rw [x.sizeUpTo_add u (by omega), x.outer.sizeUpTo_splitBlock_add _ _ (by omega)]
  · obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_le h'.le
    rw [x.sizeUpTo_add_length v, x.outer.sizeUpTo_splitBlock_add_length]

lemma eq_ofSplitBlock :
    x = ofSplitBlock x.composition x.stasheff x.outer x.block x.inner x.r_eq x.s_eq
      x.composition_eq_splitBlock :=
  rfl

/-! #### The inverse of `toSigma` -/

/-- The composition of `n` into the inputs of the outer component of `G` is obtained from
`x.composition` by merging the s blocks fed to the inner operation. -/
lemma outer_eq_gather : x.outer = x.composition.gather x.stasheff.outerComposition := by
  refine Composition.ext_of_sizeUpTo _
    (by rw [StasheffIndex.length_gather_outerComposition, x.length_eq]) fun k ↦ ?_
  rw [← x.sizeUpTo_outerBoundary, StasheffIndex.sizeUpTo_gather_outerComposition]

/-- The inverse of `toSigma`. For a composition c of `n` and an index triple p = (r, s, t) of
arity `c.length`, the s blocks of `c` fed to the inner operation are merged into the block r of
the composition of `n` into the inputs of the outer component of `G`. -/
def ofSigma (σ : Σ c : Composition n, StasheffIndex c.length) : CompMapIndex n :=
  let j := σ.2.middleIndex.cast (StasheffIndex.length_gather_outerComposition σ.1 σ.2).symm
  ofSplitBlock σ.1 σ.2 (σ.1.gather σ.2.outerComposition) j
    (σ.1.sigmaCompositionAux σ.2.outerComposition j) rfl
    (StasheffIndex.length_sigmaCompositionAux_outerComposition σ.1 σ.2 j rfl).symm
    (StasheffIndex.splitBlock_gather_outerComposition σ.1 σ.2 j rfl).symm

lemma toSigma_ofSigma (σ : Σ c : Composition n, StasheffIndex c.length) :
    (ofSigma σ).toSigma = σ :=
  rfl

lemma ofSigma_toSigma : ofSigma x.toSigma = x := by
  have ho := x.outer_eq_gather
  rcases x with ⟨c, p, o, j, i, hr, hs, hl, hle, hadd, hlen⟩
  dsimp only at ho
  subst ho
  obtain rfl : j = p.middleIndex.cast (StasheffIndex.length_gather_outerComposition c p).symm :=
    Fin.ext hr.symm
  have hs' := StasheffIndex.length_sigmaCompositionAux_outerComposition c p
    (p.middleIndex.cast (StasheffIndex.length_gather_outerComposition c p).symm) rfl
  obtain rfl : i = c.sigmaCompositionAux p.outerComposition
      (p.middleIndex.cast (StasheffIndex.length_gather_outerComposition c p).symm) := by
    refine Composition.ext_of_sizeUpTo _ (hs.symm.trans hs'.symm) fun u ↦ ?_
    rcases le_or_gt u p.s with hu | hu
    · have h₁ := hadd u (by omega)
      rw [← hr] at h₁
      have := StasheffIndex.sizeUpTo_add_sigmaCompositionAux c p
        (p.middleIndex.cast (StasheffIndex.length_gather_outerComposition c p).symm) rfl hu
      omega
    · rw [Composition.sizeUpTo_ofLength_le _ _ (by omega),
        Composition.sizeUpTo_ofLength_le _ _ (by omega)]
  rfl

/-- Every pair of a composition c of `n` and an index triple of arity `c.length` describes
exactly one term, given by `ofSigma`. -/
theorem bijective_toSigma : Function.Bijective (toSigma (n := n)) :=
  Function.bijective_iff_has_inverse.2 ⟨ofSigma, ofSigma_toSigma, toSigma_ofSigma⟩

/-- The indices of the terms of the left-hand side of the functor equation for `G` on the values
of `F` form a finite type, through their description by a composition and an index triple. -/
instance : Fintype (CompMapIndex n) :=
  .ofEquiv _ (Equiv.ofBijective _ bijective_toSigma).symm

/-! #### The inverse of `toBlock` -/

/-- The inverse of `toBlock`. For a composition `o` of `n`, a block j of `o` and a composition
`i` of that block, the block j of `o` is split into the blocks of `i`, and the inner operation is
applied to the values of `F` on these blocks. -/
def ofBlock (τ : Σ c : Composition n, Σ j : Fin c.length, Composition (c.blocksFun j)) :
    CompMapIndex n :=
  have := τ.1.length_splitBlock τ.2.1 τ.2.2; have := τ.2.1.2
  ofSplitBlock (τ.1.splitBlock τ.2.1 τ.2.2)
    ⟨τ.2.1, τ.2.2.length, τ.1.length - 1 - τ.2.1, by omega,
      τ.2.2.length_pos_of_pos (τ.1.one_le_blocksFun _)⟩
    τ.1 τ.2.1 τ.2.2 rfl rfl rfl

lemma toBlock_ofBlock
    (τ : Σ c : Composition n, Σ j : Fin c.length, Composition (c.blocksFun j)) :
    (ofBlock τ).toBlock = τ :=
  rfl

lemma ofBlock_toBlock : ofBlock x.toBlock = x := by
  have hc := x.composition_eq_splitBlock
  rcases x with ⟨c, p, o, j, i, hr, hs, hl, hle, hadd, hlen⟩
  dsimp only at hc
  subst hc
  obtain rfl : p = (ofBlock ⟨o, j, i⟩).stasheff :=
    StasheffIndex.ext hr hs (by
      have := p.sum_eq; have := o.length_splitBlock j i
      dsimp only [ofBlock, ofSplitBlock]
      omega)
  rfl

/-- Every triple of a composition of `n`, one of its blocks and a composition of that block
describes exactly one term, given by `ofBlock`. -/
theorem bijective_toBlock : Function.Bijective (toBlock (n := n)) :=
  Function.bijective_iff_has_inverse.2 ⟨ofBlock, ofBlock_toBlock, toBlock_ofBlock⟩

end CompMapIndex

end AInfinityTheory
