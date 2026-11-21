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

## Main results

* `AInfinityTheory.CompMapIndex.bijective_toSigma`,
  `AInfinityTheory.CompMapIndex.bijective_toBlock`: the projections onto the two descriptions of
  a term are bijections.
* `AInfinityTheory.CompMapIndex.stasheffSign_eq`: the Koszul signs of a term in its two
  descriptions.

## Implementation notes

The bijectivity statements and the sign identity are still stubbed with `sorry`.
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

section Signs

variable {β : Type*} [AddCommGroup β] [Grading β]

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
