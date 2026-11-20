/-
Copyright (c) 2026 Annie Yao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Annie Yao, Marco David, Zhan Shi
-/
module

public import AInfinity.AInfinityFunctor
public import Mathlib.Analysis.Analytic.Composition

/-! # Composition of A∞-functors

The composite of A∞-functor data `F` from `Obj` to `Obj'` and `G` from `Obj'` to `Obj''` acts on
objects and degrees by composition, and its functor component of arity n is
$$(G \circ F)_n(a_1, \dots, a_n) = \sum_{k \ge 1} \sum_{i_1 + \dots + i_k = n}
  G_k(F_{i_1}(a_1, \dots, a_{i_1}), \dots, F_{i_k}(a_{n-i_k+1}, \dots, a_n)).$$
Composition of A∞-functor data is associative, and the composite of two A∞-functors satisfies
the A∞-functor equations.

## Main definitions

* `MultilinearMap.compComposition`: the composite of a multilinear map in k variables with k
  multilinear maps, one on each block of a composition of `n`.
* `AInfinityTheory.AInfinityFunctorData.comp`: the composite `G.comp F` of A∞-functor data.
* `AInfinityTheory.AInfinityFunctor.comp`: the composite `G.comp F` of A∞-functors.

## Main results

* `AInfinityTheory.AInfinityFunctorData.comp_assoc`: composition of A∞-functor data is
  associative.
* `AInfinityTheory.AInfinityFunctor.comp_mapCompSum_eq_compMapSum`: the composite of two
  A∞-functors satisfies the A∞-functor equations.

## Implementation notes

Both proofs are work in progress and still contain `sorry`. Associativity reindexes a two-level
sum over compositions along Mathlib's `Composition.sigmaEquivSigmaPi`, as in the proof of
associativity of the composition of formal multilinear series
(`FormalMultilinearSeries.comp_assoc`). The functor equation for `G.comp F` is reduced to the
functor equations of `F`, applied blockwise, and of `G`, applied to the outputs of `F`.

Changes of objects are transported with `homCongr`, as in `AInfinity.AInfinityFunctor`.
-/

@[expose] public section

noncomputable section

/-! ### Multilinear maps composed along a composition -/

namespace MultilinearMap

variable {R : Type*} [Semiring R] {n : ℕ} (c : Composition n)
variable {M : Fin n → Type*} {N : Fin c.length → Type*} {P : Type*}
variable [∀ i, AddCommMonoid (M i)] [∀ l, AddCommMonoid (N l)] [AddCommMonoid P]
variable [∀ i, Module R (M i)] [∀ l, Module R (N l)] [Module R P]

/-- The composite of a multilinear map `g` in k variables with k multilinear maps `f l`, one on
each block of a composition `c` of `n` into k blocks: the multilinear map in n variables
`x ↦ g (f 0 (x on block 0), …, f (k - 1) (x on block k - 1))`. -/
def compComposition (g : MultilinearMap R N P)
    (f : ∀ l, MultilinearMap R (fun j ↦ M (c.embedding l j)) (N l)) : MultilinearMap R M P :=
  (domDomCongrLinearEquiv' R ℕ M P c.blocksFinEquiv.symm).symm (g.compMultilinearMap f)

@[simp]
theorem compComposition_apply (g : MultilinearMap R N P)
    (f : ∀ l, MultilinearMap R (fun j ↦ M (c.embedding l j)) (N l)) (x : ∀ i, M i) :
    compComposition c g f x = g fun l ↦ f l fun j ↦ x (c.embedding l j) :=
  rfl

/-- Composition along a composition is additive in the outer multilinear map. -/
theorem compComposition_sum_left {α : Type*} [Fintype α] (g : α → MultilinearMap R N P)
    (f : ∀ l, MultilinearMap R (fun j ↦ M (c.embedding l j)) (N l)) :
    compComposition c (∑ a, g a) f = ∑ a, compComposition c (g a) f := by
  ext x
  simp

/-- Composition along a composition expands finite sums in every block. -/
theorem compComposition_sum_right (g : MultilinearMap R N P) {α : Fin c.length → Type*}
    [∀ l, Fintype (α l)]
    (f : ∀ l, α l → MultilinearMap R (fun j ↦ M (c.embedding l j)) (N l)) :
    compComposition c g (fun l ↦ ∑ a, f l a) =
      ∑ a : ∀ l, α l, compComposition c g fun l ↦ f l (a l) := by
  -- classical
  ext x
  simp [MultilinearMap.map_sum]

end MultilinearMap

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

/-! ### Degrees -/

section Degrees

variable {β : Type*} [AddCommGroup β] [Grading β] (deg : Fin n → β)

/-- Applying the functor components of arities i₁, …, iₖ to the blocks of a composition of
`n`, and then a functor component of arity k to their values, gives the degree of a functor
component of arity n. -/
lemma functorTargetDeg_functorTargetDeg_embedding (c : Composition n) :
    functorTargetDeg (fun l ↦ functorTargetDeg fun j ↦ deg (c.embedding l j)) =
      functorTargetDeg deg := by
  apply add_right_cancel (b := (degOne : β))
  rw [← operationTargetDeg_eq_functorTargetDeg_add_degOne,
    ← operationTargetDeg_eq_functorTargetDeg_add_degOne,
    operationTargetDeg_functorTargetDeg_embedding]

end Degrees

namespace AInfinityFunctorData

variable {β β' β'' β''' : Type*} [AddCommGroup β] [Grading β] [AddCommGroup β'] [Grading β']
  [AddCommGroup β''] [Grading β''] [AddCommGroup β'''] [Grading β''']
  {R : Type*} [Semiring R] {Obj Obj' Obj'' Obj''' : Type*}

section GradedLinearQuiver

variable [GradedLinearQuiver β R Obj] [GradedLinearQuiver β' R Obj']
  [GradedLinearQuiver β'' R Obj''] [GradedLinearQuiver β''' R Obj''']

lemma functorTargetDeg_degMap (F : AInfinityFunctorData β β' R Obj Obj') {k : ℕ}
    (b : Fin k → β) :
    functorTargetDeg (fun i ↦ F.degMap (b i)) = F.degMap (functorTargetDeg b) := by
  simp only [functorTargetDeg, map_add, map_sum, map_zsmul, GradingHom.map_degOne]

/-- `functorTargetDeg_functorTargetDeg_embedding` translated along `degMap`: the outer functor
component of a term of the composite `G.comp F`, indexed by a composition of `n`, has inputs
whose degrees add up to `degMap j`, where `j` is the degree of the composite component. -/
lemma functorTargetDeg_degMap_functorTargetDeg_embedding
    (F : AInfinityFunctorData β β' R Obj Obj') {deg : Fin n → β} (c : Composition n) (j : β)
    (hj : functorTargetDeg deg = j) :
    functorTargetDeg (fun l ↦ F.degMap (functorTargetDeg fun i ↦ deg (c.embedding l i))) =
      F.degMap j :=
  (F.functorTargetDeg_degMap _).trans
    (congrArg F.degMap ((functorTargetDeg_functorTargetDeg_embedding deg c).trans hj))

/-! ### The composite of A∞-functor data -/

variable (G : AInfinityFunctorData β' β'' R Obj' Obj'')
  (F : AInfinityFunctorData β β' R Obj Obj') (X : Fin (n + 1) → Obj) (deg : Fin n → β)

/-- The functor component of arity iₗ on the `l`-th block of a composition c = (i₁, …, iₖ)
of `n`, as a multilinear map into the hom space of the `l`-th input of an outer operation of
arity k. Evaluated on composable inputs, it is `compositionBlockMap`. -/
def compositionBlockMultilinearMap (c : Composition n) (l : Fin c.length) :
    MultilinearMap R (fun j ↦ ComposableHom β R X (c.embedding l j) (deg (c.embedding l j)))
      (ComposableHom β' R (fun k ↦ F.obj (X (c.boundary k))) l
        (F.degMap (functorTargetDeg fun j ↦ deg (c.embedding l j)))) :=
  (homCongr R (congrArg F.obj (compositionBlockObj_zero X c l))
    (congrArg F.obj (compositionBlockObj_last X c l)) rfl).toLinearMap.compMultilinearMap
    ((F.map (compositionBlockObj X c l)).v (fun j ↦ deg (c.embedding l j)) _ rfl)

@[simp]
lemma compositionBlockMultilinearMap_apply (a : ∀ i : Fin n, ComposableHom β R X i (deg i))
    (c : Composition n) (l : Fin c.length) :
    F.compositionBlockMultilinearMap X deg c l (fun j ↦ a (c.embedding l j)) =
      F.compositionBlockMap a c l :=
  rfl

variable [NeZero n]

/-- The term of the composite functor component (G ∘ F)ₙ indexed by a composition
c = (i₁, …, iₖ) of `n`: the multilinear map
(a₁, …, aₙ) ↦ Gₖ(F_{i₁}(a₁, …, a_{i₁}), …, F_{iₖ}(a_{n-iₖ+1}, …, aₙ)),
on inputs of degrees `deg`, in degree `G.degMap (F.degMap j)` for any `j` equal to the degree
of the composite component. -/
def compMapTermMultilinearMap (c : Composition n) (j : β) (hj : functorTargetDeg deg = j) :
    MultilinearMap R (fun i ↦ ComposableHom β R X i (deg i))
      ((G.obj (F.obj (X 0)) →ᵍ[R] G.obj (F.obj (X (Fin.last n)))) (G.degMap (F.degMap j))) :=
  (homCongr R (congrArg (fun k ↦ G.obj (F.obj (X k))) c.boundary_zero)
    (congrArg (fun k ↦ G.obj (F.obj (X k))) c.boundary_last) rfl).toLinearMap.compMultilinearMap
    (MultilinearMap.compComposition c
      ((G.map fun k ↦ F.obj (X (c.boundary k))).v _ (F.degMap j)
        (F.functorTargetDeg_degMap_functorTargetDeg_embedding c j hj))
      (F.compositionBlockMultilinearMap X deg c))

/-- The functor component (G ∘ F)ₙ of the composite of A∞-functor data: the sum, over all
compositions c = (i₁, …, iₖ) of `n`, of Gₖ applied to the values of F_{i₁}, …, F_{iₖ} on
the k blocks of c. -/
def compMap :
    GradedMultilinearMap R (ComposableHom β R X)
      (fun b : β ↦ (G.obj (F.obj (X 0)) →ᵍ[R] G.obj (F.obj (X (Fin.last n)))) (G.degMap
        (F.degMap b)))
      ((1 - n : ℤ) • degOne) :=
  .mk fun deg j hj ↦ ∑ c : Composition n, compMapTermMultilinearMap G F X deg c j hj

omit [NeZero n] in
/-- The composite `G.comp F` of A∞-functor data `F` from `Obj` to `Obj'` and `G` from `Obj'` to
`Obj''`, written in Mathlib's order: it acts on objects by `G.obj ∘ F.obj`, translates degrees
along `G.degMap.comp F.degMap`, and its functor component (G ∘ F)ₙ is the sum, over all
compositions i₁ + ⋯ + iₖ = n, of Gₖ applied to the values of F_{i₁}, …, F_{iₖ}. -/
protected def comp : AInfinityFunctorData β β'' R Obj Obj'' where
  obj X := G.obj (F.obj X)
  degMap := G.degMap.comp F.degMap
  map X := compMap G F X

omit [NeZero n] in
@[simp]
lemma comp_obj : (G.comp F).obj = G.obj ∘ F.obj :=
  rfl

omit [NeZero n] in
@[simp]
lemma comp_degMap : (G.comp F).degMap = G.degMap.comp F.degMap :=
  rfl

@[simp]
lemma comp_map_v (j : β) (hj : functorTargetDeg deg = j) :
    ((G.comp F).map X).v deg j hj =
      ∑ c : Composition n, compMapTermMultilinearMap G F X deg c j hj :=
  rfl

end GradedLinearQuiver

/-! ### Associativity -/

section Associativity

variable [GradedLinearQuiver β R Obj] [GradedLinearQuiver β' R Obj']
  [GradedLinearQuiver β'' R Obj''] [GradedLinearQuiver β''' R Obj''']
variable (H : AInfinityFunctorData β'' β''' R Obj'' Obj''')
  (G : AInfinityFunctorData β' β'' R Obj' Obj'') (F : AInfinityFunctorData β β' R Obj Obj')
  (X : Fin (n + 1) → Obj) (deg : Fin n → β) [NeZero n] (j : β) (hj : functorTargetDeg deg = j)

/-- The summand of the component of `(H.comp G).comp F` indexed by a composition `a` of `n` and a
composition `b` of its number of blocks: H applied, along `b`, to the values of G on the outputs
of F on the blocks of `a`. -/
def compAssocTermLeft (I : Σ a : Composition n, Composition a.length) :
    MultilinearMap R (fun i ↦ ComposableHom β R X i (deg i))
      ((H.obj (G.obj (F.obj (X 0))) →ᵍ[R] H.obj (G.obj (F.obj (X (Fin.last n)))))
        (H.degMap (G.degMap (F.degMap j)))) :=
  (homCongr R (congrArg (fun k ↦ H.obj (G.obj (F.obj (X k)))) I.1.boundary_zero)
    (congrArg (fun k ↦ H.obj (G.obj (F.obj (X k)))) I.1.boundary_last)
    rfl).toLinearMap.compMultilinearMap
    (MultilinearMap.compComposition I.1
      (compMapTermMultilinearMap H G (fun k ↦ F.obj (X (I.1.boundary k))) _ I.2 (F.degMap j)
        (F.functorTargetDeg_degMap_functorTargetDeg_embedding I.1 j hj))
      (F.compositionBlockMultilinearMap X deg I.1))

/-- The summand of the component of `H.comp (G.comp F)` indexed by a composition `c` of `n` and a
composition `d l` of each of its blocks: H applied, along `c`, to the values of `G` along `d l`
on the outputs of F on the blocks of `d l`. -/
def compAssocTermRight (I : Σ c : Composition n, ∀ l, Composition (c.blocksFun l)) :
    MultilinearMap R (fun i ↦ ComposableHom β R X i (deg i))
      ((H.obj (G.obj (F.obj (X 0))) →ᵍ[R] H.obj (G.obj (F.obj (X (Fin.last n)))))
        (H.degMap (G.degMap (F.degMap j)))) :=
  (homCongr R (congrArg (fun k ↦ H.obj (G.obj (F.obj (X k)))) I.1.boundary_zero)
    (congrArg (fun k ↦ H.obj (G.obj (F.obj (X k)))) I.1.boundary_last)
    rfl).toLinearMap.compMultilinearMap
    (MultilinearMap.compComposition I.1
      ((H.map fun k ↦ G.obj (F.obj (X (I.1.boundary k)))).v _ (G.degMap (F.degMap j))
        ((G.comp F).functorTargetDeg_degMap_functorTargetDeg_embedding I.1 j hj))
      fun l ↦ (homCongr R (congrArg (G.comp F).obj (compositionBlockObj_zero X I.1 l))
        (congrArg (G.comp F).obj (compositionBlockObj_last X I.1 l))
        rfl).toLinearMap.compMultilinearMap
        (compMapTermMultilinearMap G F (compositionBlockObj X I.1 l) _ (I.2 l) _ rfl))

/-- Expanding the inner composite `H.comp G` in a term of `(H.comp G).comp F`. -/
lemma compMapTermMultilinearMap_comp_left (a : Composition n) :
    compMapTermMultilinearMap (H.comp G) F X deg a j hj =
      ∑ b : Composition a.length, compAssocTermLeft H G F X deg j hj ⟨a, b⟩ := by
  sorry

/-- Expanding the inner composite `G.comp F` in every block of a term of `H.comp (G.comp F)`. -/
lemma compMapTermMultilinearMap_comp_right (c : Composition n) :
    compMapTermMultilinearMap H (G.comp F) X deg c j hj =
      ∑ d : ∀ l, Composition (c.blocksFun l),
        compAssocTermRight H G F X deg j hj ⟨c, d⟩ := by
  sorry

/-- The summands of the two bracketings agree along `Composition.sigmaEquivSigmaPi`, which
sends `(a, b)` to `(a.gather b, a.sigmaCompositionAux b)`. -/
lemma compAssocTermRight_sigmaEquivSigmaPi (I : Σ a : Composition n, Composition a.length) :
    compAssocTermRight H G F X deg j hj (Composition.sigmaEquivSigmaPi n I) =
      compAssocTermLeft H G F X deg j hj I := by
  sorry

omit [NeZero n] in
/-- The functor components of the two bracketings of a triple composite agree. -/
lemma comp_assoc_map [NeZero n] :
    ((H.comp G).comp F).map X = (H.comp (G.comp F)).map X := by
  refine GradedMultilinearMap.ext fun deg j hj ↦ ?_
  have hleft := (Fintype.sum_congr _ _ fun a ↦
    compMapTermMultilinearMap_comp_left H G F X deg j hj a).trans (Fintype.sum_sigma _).symm
  have hright := (Fintype.sum_congr _ _ fun c ↦
    compMapTermMultilinearMap_comp_right H G F X deg j hj c).trans (Fintype.sum_sigma _).symm
  have hmid : ∑ I, compAssocTermLeft H G F X deg j hj I =
      ∑ I, compAssocTermRight H G F X deg j hj I := by
    rw [← (Composition.sigmaEquivSigmaPi n).sum_comp]
    exact Fintype.sum_congr _ _ fun I ↦
      (compAssocTermRight_sigmaEquivSigmaPi H G F X deg j hj I).symm
  exact hleft.trans (hmid.trans hright.symm)

omit [NeZero n] in
/-- Composition of A∞-functor data is associative. -/
theorem comp_assoc : (H.comp G).comp F = H.comp (G.comp F) := by
  change AInfinityFunctorData.mk _ _ _ = AInfinityFunctorData.mk _ _ _
  congr 1
  funext n _ X
  exact comp_assoc_map H G F X

end Associativity

end AInfinityFunctorData

/-! ### The composite of A∞-functors -/

namespace AInfinityFunctor

variable {β β' β'' : Type*} [AddCommGroup β] [Grading β] [AddCommGroup β'] [Grading β']
  [AddCommGroup β''] [Grading β''] {R : Type*} [Semiring R] {Obj Obj' Obj'' : Type*}
  [AInfinityCategory β R Obj] [AInfinityCategory β' R Obj'] [AInfinityCategory β'' R Obj'']
variable (G : AInfinityFunctor β' β'' R Obj' Obj'') (F : AInfinityFunctor β β' R Obj Obj')
variable [NeZero n] {X : Fin (n + 1) → Obj} {deg : Fin n → β}
  (a : ∀ i : Fin n, ComposableHom β R X i (deg i)) {d : β} (hd : operationTargetDeg deg = d)

/-- Applying the functor equations of `F` blockwise: the left-hand side of the functor equation
for `G.comp F` is the sum, over all compositions `c` of `n`, of the left-hand side of the
functor equation for `G` on the values of the components of `F` on the blocks of `c`. -/
lemma mapCompSum_comp_eq_sum_mapCompSum :
    (G.toAInfinityFunctorData.comp F.toAInfinityFunctorData).mapCompSum a d hd =
      ∑ c : Composition n, homCongr R (congrArg (fun k ↦ G.obj (F.obj (X k))) c.boundary_zero)
        (congrArg (fun k ↦ G.obj (F.obj (X k))) c.boundary_last) rfl
        (G.mapCompSum (F.compositionBlockMap a c) (F.degMap d)
          (F.operationTargetDeg_degMap_functorTargetDeg_embedding c d hd)) := by
  sorry

/-- Applying the functor equations of `G` to the values of the components of `F` on the blocks
of every composition of `n`. -/
lemma sum_mapCompSum_eq_sum_compMapSum :
    ∑ c : Composition n, homCongr R (congrArg (fun k ↦ G.obj (F.obj (X k))) c.boundary_zero)
        (congrArg (fun k ↦ G.obj (F.obj (X k))) c.boundary_last) rfl
        (G.mapCompSum (F.compositionBlockMap a c) (F.degMap d)
          (F.operationTargetDeg_degMap_functorTargetDeg_embedding c d hd)) =
      ∑ c : Composition n, homCongr R (congrArg (fun k ↦ G.obj (F.obj (X k))) c.boundary_zero)
        (congrArg (fun k ↦ G.obj (F.obj (X k))) c.boundary_last) rfl
        (G.compMapSum (F.compositionBlockMap a c) (F.degMap d)
          (F.operationTargetDeg_degMap_functorTargetDeg_embedding c d hd)) :=
  Finset.sum_congr rfl fun c _ ↦ by rw [G.mapCompSum_eq_compMapSum]

/-- Reindexing the resulting two-level sum over compositions along
`Composition.sigmaEquivSigmaPi` gives the right-hand side of the functor equation for
`G.comp F`. -/
lemma sum_compMapSum_eq_compMapSum_comp :
    ∑ c : Composition n, homCongr R (congrArg (fun k ↦ G.obj (F.obj (X k))) c.boundary_zero)
        (congrArg (fun k ↦ G.obj (F.obj (X k))) c.boundary_last) rfl
        (G.compMapSum (F.compositionBlockMap a c) (F.degMap d)
          (F.operationTargetDeg_degMap_functorTargetDeg_embedding c d hd)) =
      (G.toAInfinityFunctorData.comp F.toAInfinityFunctorData).compMapSum a d hd := by
  sorry

/-- The composite of two A∞-functors satisfies the A∞-functor equations. -/
theorem comp_mapCompSum_eq_compMapSum :
    (G.toAInfinityFunctorData.comp F.toAInfinityFunctorData).mapCompSum a d hd =
      (G.toAInfinityFunctorData.comp F.toAInfinityFunctorData).compMapSum a d hd :=
  (mapCompSum_comp_eq_sum_mapCompSum G F a hd).trans
    ((sum_mapCompSum_eq_sum_compMapSum G F a hd).trans (sum_compMapSum_eq_compMapSum_comp G F a hd))

omit [NeZero n] in
/-- The composite `G.comp F` of A∞-functors `F` from `Obj` to `Obj'` and `G` from `Obj'` to
`Obj''`, written in Mathlib's order: the composite of the underlying A∞-functor data, which
satisfies the A∞-functor equations by `comp_mapCompSum_eq_compMapSum`. -/
protected def comp : AInfinityFunctor β β'' R Obj Obj'' where
  toAInfinityFunctorData := G.toAInfinityFunctorData.comp F.toAInfinityFunctorData
  mapCompSum_eq_compMapSum a _ hd := comp_mapCompSum_eq_compMapSum G F a hd

omit [NeZero n] in
@[simp]
lemma comp_toAInfinityFunctorData :
    (G.comp F).toAInfinityFunctorData = G.toAInfinityFunctorData.comp F.toAInfinityFunctorData :=
  rfl

end AInfinityFunctor

end AInfinityTheory
