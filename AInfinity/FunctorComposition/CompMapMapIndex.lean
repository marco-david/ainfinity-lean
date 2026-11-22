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
* `AInfinityTheory.CompMapMapIndex.ofGather`: the index given by both descriptions, when the
  second is the image of the first under `Composition.sigmaEquivSigmaPi`.
* `AInfinityTheory.CompMapMapIndex.ofSigma`: the inverse of `CompMapMapIndex.toSigma`.
* `AInfinityTheory.CompMapMapIndex.ofSigmaPi`: the inverse of `CompMapMapIndex.toSigmaPi`.

## Main results

* `AInfinityTheory.CompMapMapIndex.bijective_toSigma`,
  `AInfinityTheory.CompMapMapIndex.bijective_toSigmaPi`: the projections onto the two
  descriptions of a term are bijections.

## Implementation notes

`CompMapMapIndex.ofGather` reduces the relations between the two descriptions to a single
equation `toSigmaPi = Composition.sigmaEquivSigmaPi n toSigma`, which holds for every index
(`CompMapMapIndex.toSigmaPi_eq`). `CompMapMapIndex.bijective_toSigma` and
`CompMapMapIndex.bijective_toSigmaPi` are proved by the explicit inverses
`CompMapMapIndex.ofSigma` and `CompMapMapIndex.ofSigmaPi`, both built with
`CompMapMapIndex.ofGather`; the latter uses the inverse of `Composition.sigmaEquivSigmaPi`.
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

/-! #### Construction from both descriptions -/

/-- The index of a term described by a composition `c` of `n` with a composition `g` of
`c.length`, and by a composition `o` of `n` with a composition `i` of each of its blocks, when
`⟨o, i⟩` is the image of `⟨c, g⟩` under `Composition.sigmaEquivSigmaPi`: `o` is obtained from `c`
by gathering its blocks along `g`, and `i` records how each block of `o` splits into blocks
of `c`. -/
def ofGather (c : Composition n) (g : Composition c.length) (o : Composition n)
    (i : ∀ l : Fin o.length, Composition (o.blocksFun l))
    (h : (⟨o, i⟩ : Σ e : Composition n, ∀ l : Fin e.length, Composition (e.blocksFun l)) =
      Composition.sigmaEquivSigmaPi n ⟨c, g⟩) : CompMapMapIndex n where
  composition := c
  grouping := g
  outer := o
  inner := i
  length_eq := by cases h; exact (c.length_gather g).symm
  length_inner l := by cases h; exact c.length_sigmaCompositionAux g l
  sizeUpTo_add l u hu := by cases h; exact c.sizeUpTo_sizeUpTo_add_boundary g l ⟨u, by omega⟩

/-- The composition of `n` into the inputs of the components of `G` is obtained from
`x.composition` by gathering its blocks along `x.grouping`. -/
lemma outer_eq_gather : x.outer = x.composition.gather x.grouping :=
  Composition.ext_of_sizeUpTo _ (by rw [Composition.length_gather, x.length_eq]) fun k ↦ by
    rw [Composition.sizeUpTo_gather, x.sizeUpTo_sizeUpTo]

/-- The block description of an index is the image of its other description under
`Composition.sigmaEquivSigmaPi`. In particular, every index is given by `ofGather`. -/
lemma toSigmaPi_eq : x.toSigmaPi = Composition.sigmaEquivSigmaPi n x.toSigma := by
  have ho := x.outer_eq_gather
  rcases x with ⟨c, g, o, i, hl, hi, hadd⟩
  dsimp only at ho
  subst ho
  obtain rfl : i = c.sigmaCompositionAux g := funext fun l ↦ by
    have h₁ := hi (l.cast hl.symm)
    have h₂ : (c.sigmaCompositionAux g l).length = _ :=
      c.length_sigmaCompositionAux g (l.cast hl.symm)
    simp only [Fin.cast_cast, Fin.cast_eq_self] at h₁
    refine Composition.ext_of_sizeUpTo _ (h₁.trans h₂.symm) fun u ↦ ?_
    rcases le_or_gt u (g.blocksFun (l.cast hl.symm)) with hu | hu
    · have h₃ := hadd (l.cast hl.symm) u hu
      have h₄ := c.sizeUpTo_sizeUpTo_add_boundary g (l.cast hl.symm) ⟨u, by omega⟩
      simp only [Fin.cast_cast, Fin.cast_eq_self] at h₃
      exact Nat.add_left_cancel (h₃.symm.trans h₄)
    · rw [Composition.sizeUpTo_ofLength_le _ _ (by omega),
        Composition.sizeUpTo_ofLength_le _ _ (by omega)]
  rfl

lemma eq_ofGather :
    x = ofGather x.composition x.grouping x.outer x.inner x.toSigmaPi_eq :=
  rfl

/-! #### The inverse of `toSigma` -/

/-- The inverse of `toSigma`. For a composition c of `n` and a composition g of `c.length`, the
blocks of `c` are gathered along `g` into the inputs of the components of `G`, and each of these
splits into the blocks of `c` it contains. -/
def ofSigma (σ : Σ c : Composition n, Composition c.length) : CompMapMapIndex n :=
  ofGather σ.1 σ.2 _ _ rfl

/-- An index given by `ofGather` only depends on its description by a composition and a
composition of its length. -/
lemma ofGather_eq_ofSigma (c : Composition n) (g : Composition c.length) (o : Composition n)
    (i : ∀ l : Fin o.length, Composition (o.blocksFun l))
    (h : (⟨o, i⟩ : Σ e : Composition n, ∀ l : Fin e.length, Composition (e.blocksFun l)) =
      Composition.sigmaEquivSigmaPi n ⟨c, g⟩) :
    ofGather c g o i h = ofSigma ⟨c, g⟩ := by
  cases h
  rfl

lemma toSigma_ofSigma (σ : Σ c : Composition n, Composition c.length) :
    (ofSigma σ).toSigma = σ :=
  rfl

lemma ofSigma_toSigma : ofSigma x.toSigma = x :=
  (ofGather_eq_ofSigma _ _ _ _ x.toSigmaPi_eq).symm

/-- Every pair of a composition c of `n` and a composition of `c.length` describes exactly one
term, given by `ofSigma`. -/
theorem bijective_toSigma : Function.Bijective (toSigma (n := n)) :=
  Function.bijective_iff_has_inverse.2 ⟨ofSigma, ofSigma_toSigma, toSigma_ofSigma⟩

/-- The indices of the terms of the right-hand side of the functor equation for `G.comp F` form a
finite type, through their description by a composition and a composition of its length. -/
instance : Fintype (CompMapMapIndex n) :=
  .ofEquiv _ (Equiv.ofBijective _ bijective_toSigma).symm

/-! #### The inverse of `toSigmaPi` -/

/-- The inverse of `toSigmaPi`. For a composition of `n` and a composition of each of its blocks,
the blocks of all these compositions form the composition of `n` into the blocks of inputs of the
components of `F`, grouped by the blocks they lie in. -/
def ofSigmaPi (τ : Σ e : Composition n, ∀ l : Fin e.length, Composition (e.blocksFun l)) :
    CompMapMapIndex n :=
  ofGather ((Composition.sigmaEquivSigmaPi n).symm τ).1
    ((Composition.sigmaEquivSigmaPi n).symm τ).2 τ.1 τ.2
    ((Composition.sigmaEquivSigmaPi n).apply_symm_apply τ).symm

lemma toSigmaPi_ofSigmaPi
    (τ : Σ e : Composition n, ∀ l : Fin e.length, Composition (e.blocksFun l)) :
    (ofSigmaPi τ).toSigmaPi = τ :=
  rfl

lemma ofSigmaPi_toSigmaPi : ofSigmaPi x.toSigmaPi = x := by
  rw [ofSigmaPi, ofGather_eq_ofSigma, x.toSigmaPi_eq, Equiv.symm_apply_apply]
  exact x.ofSigma_toSigma

/-- Every pair of a composition of `n` and a composition of each of its blocks describes exactly
one term, given by `ofSigmaPi`. -/
theorem bijective_toSigmaPi : Function.Bijective (toSigmaPi (n := n)) :=
  Function.bijective_iff_has_inverse.2 ⟨ofSigmaPi, ofSigmaPi_toSigmaPi, toSigmaPi_ofSigmaPi⟩

end CompMapMapIndex

end AInfinityTheory
