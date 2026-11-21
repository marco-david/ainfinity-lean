/-
Copyright (c) 2026 Zhan Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhan Shi
-/
module

public import AInfinity.FunctorComposition.Lemmas

/-! # The index type of the right-hand side of the functor equation for a composite

The right-hand side of the functor equation for a composite `G.comp F` of A∞-functors and the
sum, over all compositions, of the right-hand sides of the functor equations for `G` on the values
of `F` are sums of terms
$$m''_k(G(F(\dots), \dots, F(\dots)), \dots, G(F(\dots), \dots, F(\dots))).$$
In the second sum, such a term is described by a composition c of `n` and a composition of
`c.length`. In the first, it is described by a composition of `n` and a composition of each of its
blocks. This file records both descriptions in the index type `CompMapMapIndex`, related only by
equalities of natural numbers, and states the combinatorial facts about it that the reindexing in
`AInfinity.FunctorComposition.Reindex` relies on. Mathlib's `Composition.sigmaEquivSigmaPi`
matches the two descriptions; the lemmas on two-level compositions in
`AInfinity.FunctorComposition.Lemmas` relate it to `CompMapMapIndex`.

## Main definitions

* `AInfinityTheory.CompMapMapIndex`: the indices of the terms m''(G(F, …, F), …, G(F, …, F)).

## Main results

* `AInfinityTheory.CompMapMapIndex.bijective_toSigma`,
  `AInfinityTheory.CompMapMapIndex.bijective_toSigmaPi`: the projections onto the two
  descriptions of a term are bijections.

## Implementation notes

The bijectivity statements are still stubbed with `sorry`.
-/

@[expose] public section

noncomputable section

namespace AInfinityTheory

variable {n : ℕ}

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

end AInfinityTheory
