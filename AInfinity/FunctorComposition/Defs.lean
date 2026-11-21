/-
Copyright (c) 2026 Annie Yao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Annie Yao, Marco David, Zhan Shi
-/
module

public import AInfinity.AInfinityFunctor

/-! # The composite of A∞-functor data

The composite of A∞-functor data `F` from `Obj` to `Obj'` and `G` from `Obj'` to `Obj''` acts on
objects and degrees by composition, and its functor component of arity n is
$$(G \circ F)_n(a_1, \dots, a_n) = \sum_{k \ge 1} \sum_{i_1 + \dots + i_k = n}
  G_k(F_{i_1}(a_1, \dots, a_{i_1}), \dots, F_{i_k}(a_{n-i_k+1}, \dots, a_n)).$$
That the composite of two A∞-functors satisfies the A∞-functor equations is proved in
`AInfinity.FunctorComposition.Basic`.

## Main definitions

* `MultilinearMap.compComposition`: the composite of a multilinear map in k variables with k
  multilinear maps, one on each block of a composition of `n`.
* `AInfinityTheory.AInfinityFunctorData.compMap`: the functor component (G ∘ F)ₙ of the
  composite.
* `AInfinityTheory.AInfinityFunctorData.comp`: the composite `G.comp F` of A∞-functor data.

## Implementation notes

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
  ext x
  simp [MultilinearMap.map_sum]

end MultilinearMap

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

variable {β β' β'' : Type*} [AddCommGroup β] [Grading β] [AddCommGroup β'] [Grading β']
  [AddCommGroup β''] [Grading β''] {R : Type*} [Semiring R] {Obj Obj' Obj'' : Type*}

section GradedLinearQuiver

variable [GradedLinearQuiver β R Obj] [GradedLinearQuiver β' R Obj']
  [GradedLinearQuiver β'' R Obj'']

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

@[simp]
lemma compMapTermMultilinearMap_apply (a : ∀ i : Fin n, ComposableHom β R X i (deg i))
    (c : Composition n) (j : β) (hj : functorTargetDeg deg = j) :
    compMapTermMultilinearMap G F X deg c j hj a =
      homCongr R (congrArg (fun k ↦ G.obj (F.obj (X k))) c.boundary_zero)
        (congrArg (fun k ↦ G.obj (F.obj (X k))) c.boundary_last) rfl
        ((G.map fun k ↦ F.obj (X (c.boundary k))).v _ (F.degMap j)
          (F.functorTargetDeg_degMap_functorTargetDeg_embedding c j hj)
          (F.compositionBlockMap a c)) :=
  rfl

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

end AInfinityFunctorData

end AInfinityTheory
