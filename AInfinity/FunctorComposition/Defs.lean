/-
Copyright (c) 2026 Annie Yao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Annie Yao, Marco David, Zhan Shi
-/
module

public import AInfinity.AInfinityFunctor

/-! # The composite of a composable multilinear map with A∞-functor data

The composite of a composable multilinear map `H` from `Obj'` to `Obj''` with A∞-functor data `F`
from `Obj` to `Obj'` acts on objects and degrees by composition, and its component of arity n is
$$(H \circ F)_n(a_1, \dots, a_n) = \sum_{k \ge 1} \sum_{i_1 + \dots + i_k = n}
  H_k(F_{i_1}(a_1, \dots, a_{i_1}), \dots, F_{i_k}(a_{n-i_k+1}, \dots, a_n)).$$
It has the same degree `s` as `H`. Two special cases organize the theory of A∞-functors:

* for A∞-functor data `H = G`, it is the composite `G.comp F` of A∞-functor data. That the
  composite of two A∞-functors satisfies the A∞-functor equations is proved in
  `AInfinity.FunctorComposition.Basic`, and that the composition is associative in
  `AInfinity.FunctorComposition.Assoc`;
* for the operations m' of the target, it is the right-hand side of the A∞-functor equation of
  `F` (`ComposableMultilinearMap.compMapSum_eq_comp_map_v`).

## Main definitions

* `MultilinearMap.compComposition`: the composite of a multilinear map in k variables with k
  multilinear maps, one on each block of a composition of `n`.
* `AInfinityTheory.ComposableMultilinearMap.compMap`: the component (H ∘ F)ₙ of the
  composite.
* `AInfinityTheory.ComposableMultilinearMap.comp`: the composite `H.comp F` of a composable
  multilinear map with A∞-functor data.

## Main results

* `AInfinityTheory.ComposableMultilinearMap.compMapSum_eq_comp_map_v`: the right-hand side of the
  functor equation of `F` is the value of the composite of the operations of the target with `F`.

## Implementation notes

Changes of objects are transported with `homCongr`, as in `AInfinity.AInfinityFunctor`.

The inner argument of `comp` is A∞-functor data, i.e. has `s = 1`: in reduced degrees its
components have degree zero, so every term of (H ∘ F)ₙ has the degree of H. For an inner map of
another degree, the terms would have different degrees depending on the number of blocks.
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

open GradedLinearQuiver AInfinityCategoryStruct

variable {n : ℕ}

namespace ComposableMultilinearMap

variable {β β' β'' : Type*} [AddCommGroup β] [Grading β] [AddCommGroup β'] [Grading β']
  [AddCommGroup β''] [Grading β''] {R : Type*} [Semiring R] {Obj Obj' Obj'' : Type*}

section GradedLinearQuiver

variable [GradedLinearQuiver β R Obj] [GradedLinearQuiver β' R Obj']
  [GradedLinearQuiver β'' R Obj''] {s : ℤ}

/-! ### The composite of a composable multilinear map with A∞-functor data -/

variable (H : ComposableMultilinearMap β' β'' R Obj' Obj'' s)
  (F : AInfinityFunctorData β β' R Obj Obj') (X : Fin (n + 1) → Obj) (deg : Fin n → β)

/-- The functor component of arity iₗ on the `l`-th block of a composition c = (i₁, …, iₖ)
of `n`, as a multilinear map into the hom space of the `l`-th input of an outer map of
arity k. Evaluated on composable inputs, it is `compositionBlockMap`. -/
def compositionBlockMultilinearMap (c : Composition n) (l : Fin c.length) :
    MultilinearMap R (fun j ↦ ComposableHom β R X (c.embedding l j) (deg (c.embedding l j)))
      (ComposableHom β' R (fun k ↦ F.obj (X (c.boundary k))) l
        (F.degMap (targetDeg 1 fun j ↦ deg (c.embedding l j)))) :=
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

/-- The term of the composite component (H ∘ F)ₙ indexed by a composition
c = (i₁, …, iₖ) of `n`: the multilinear map
(a₁, …, aₙ) ↦ Hₖ(F_{i₁}(a₁, …, a_{i₁}), …, F_{iₖ}(a_{n-iₖ+1}, …, aₙ)),
on inputs of degrees `deg`, in degree `H.degMap (F.degMap j)` for any `j` equal to the degree
of the composite component. -/
def compMapTermMultilinearMap (c : Composition n) (j : β) (hj : targetDeg s deg = j) :
    MultilinearMap R (fun i ↦ ComposableHom β R X i (deg i))
      ((H.obj (F.obj (X 0)) →ᵍ[R] H.obj (F.obj (X (Fin.last n)))) (H.degMap (F.degMap j))) :=
  (homCongr R (congrArg (fun k ↦ H.obj (F.obj (X k))) c.boundary_zero)
    (congrArg (fun k ↦ H.obj (F.obj (X k))) c.boundary_last) rfl).toLinearMap.compMultilinearMap
    (MultilinearMap.compComposition c
      ((H.map fun k ↦ F.obj (X (c.boundary k))).v _ (F.degMap j)
        (F.targetDeg_degMap_targetDeg_embedding c j hj))
      (F.compositionBlockMultilinearMap X deg c))

@[simp]
lemma compMapTermMultilinearMap_apply (a : ∀ i : Fin n, ComposableHom β R X i (deg i))
    (c : Composition n) (j : β) (hj : targetDeg s deg = j) :
    compMapTermMultilinearMap H F X deg c j hj a =
      homCongr R (congrArg (fun k ↦ H.obj (F.obj (X k))) c.boundary_zero)
        (congrArg (fun k ↦ H.obj (F.obj (X k))) c.boundary_last) rfl
        ((H.map fun k ↦ F.obj (X (c.boundary k))).v _ (F.degMap j)
          (F.targetDeg_degMap_targetDeg_embedding c j hj)
          (F.compositionBlockMap a c)) :=
  rfl

/-- The component (H ∘ F)ₙ of the composite of a composable multilinear map `H` with A∞-functor
data `F`: the sum, over all compositions c = (i₁, …, iₖ) of `n`, of Hₖ applied to the values of
F_{i₁}, …, F_{iₖ} on the k blocks of c. -/
def compMap :
    GradedMultilinearMap R (ComposableHom β R X)
      (fun b : β ↦ (H.obj (F.obj (X 0)) →ᵍ[R] H.obj (F.obj (X (Fin.last n)))) (H.degMap
        (F.degMap b)))
      ((s - n : ℤ) • degOne) :=
  .mk fun deg j hj ↦ ∑ c : Composition n, compMapTermMultilinearMap H F X deg c j hj

omit [NeZero n] in
/-- The composite `H.comp F` of a composable multilinear map `H` from `Obj'` to `Obj''` with
A∞-functor data `F` from `Obj` to `Obj'`, written in Mathlib's order: it acts on objects by
`H.obj ∘ F.obj`, translates degrees along `H.degMap.comp F.degMap`, and its component
(H ∘ F)ₙ is the sum, over all compositions i₁ + ⋯ + iₖ = n, of Hₖ applied to the values of
F_{i₁}, …, F_{iₖ}. It has the same degree `s` as `H`.

For A∞-functor data `H`, this is the composite of A∞-functor data. For the operations of an
A∞-category structure, it is the right-hand side of the A∞-functor equation
(`compMapSum_eq_comp_map_v`). -/
protected def comp : ComposableMultilinearMap β β'' R Obj Obj'' s where
  obj X := H.obj (F.obj X)
  degMap := H.degMap.comp F.degMap
  map X := compMap H F X

omit [NeZero n] in
@[simp]
lemma comp_obj : (H.comp F).obj = H.obj ∘ F.obj :=
  rfl

omit [NeZero n] in
@[simp]
lemma comp_degMap : (H.comp F).degMap = H.degMap.comp F.degMap :=
  rfl

@[simp]
lemma comp_map_v (j : β) (hj : targetDeg s deg = j) :
    ((H.comp F).map X).v deg j hj =
      ∑ c : Composition n, compMapTermMultilinearMap H F X deg c j hj :=
  rfl

/-- The value of the composite component (H ∘ F)ₙ on composable inputs: the sum, over all
compositions c of `n`, of H applied to the values of `F` on the blocks of `c`. -/
lemma comp_map_v_apply (a : ∀ i : Fin n, ComposableHom β R X i (deg i)) (j : β)
    (hj : targetDeg s deg = j) :
    ((H.comp F).map X).v deg j hj a =
      ∑ c : Composition n, homCongr R (congrArg (fun k ↦ H.obj (F.obj (X k))) c.boundary_zero)
        (congrArg (fun k ↦ H.obj (F.obj (X k))) c.boundary_last) rfl
        ((H.map fun k ↦ F.obj (X (c.boundary k))).v _ (F.degMap j)
          (F.targetDeg_degMap_targetDeg_embedding c j hj)
          (F.compositionBlockMap a c)) :=
  sum_apply Finset.univ (fun c ↦ compMapTermMultilinearMap H F X deg c j hj) a

end GradedLinearQuiver

/-! ### The right-hand side of the functor equation as a composite -/

section AInfinityCategoryStruct

variable [AInfinityCategoryStruct β R Obj] [AInfinityCategoryStruct β' R Obj']
  (F : AInfinityFunctorData β β' R Obj Obj') {X : Fin (n + 1) → Obj} {deg : Fin n → β}
  (a : ∀ i : Fin n, ComposableHom β R X i (deg i)) [NeZero n]

/-- The right-hand side of the functor equation of `F` is the value of the composite of the
operations m' of the target, as a composable multilinear map, with `F`. -/
theorem compMapSum_eq_comp_map_v (d : β) (hd : targetDeg 2 deg = d) :
    F.compMapSum a d hd = (((toComposableMultilinearMap β' R Obj').comp F).map X).v deg d hd a :=
  (comp_map_v_apply (toComposableMultilinearMap β' R Obj') F X deg a d hd).symm

end AInfinityCategoryStruct

end ComposableMultilinearMap

end AInfinityTheory
