/-
Copyright (c) 2026 Annie Yao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Annie Yao, Marco David, Zhan Shi
-/
module

public import AInfinity.FunctorComposition.FunctorEquation

/-! # Composition of A∞-functors

The composite `G.comp F` of A∞-functor data `F` from `Obj` to `Obj'` and `G` from `Obj'` to
`Obj''` composes the maps on objects, the homomorphisms of gradings, and the components as
composable multilinear maps. This file proves that the composite of two A∞-functors satisfies the
A∞-functor equations, and that the composition of A∞-functors is associative.

## Main definitions

* `AInfinityTheory.AInfinityFunctorData.comp`: the composite `G.comp F` of A∞-functor data.
* `AInfinityTheory.AInfinityFunctor.comp`: the composite `G.comp F` of A∞-functors.

## Main results

* `AInfinityTheory.AInfinityFunctorData.comp_assoc`: the composition of A∞-functor data is
  associative.
* `AInfinityTheory.AInfinityFunctor.compMarked_id_eq_comp`: the A∞-functor equations of `F`, as
  the equality F ∘ (𝟙 | m) = m' ∘ F of composable multilinear maps.
* `AInfinityTheory.AInfinityFunctor.comp_mapCompSum_eq_compMapSum`: the composite of two
  A∞-functors satisfies the A∞-functor equations.
* `AInfinityTheory.AInfinityFunctor.comp_assoc`: the composition of A∞-functors is associative.

## Implementation notes

With the operations m, m' and m'' of the three A∞-categories, the A∞-functor equations of the
composite follow from those of `F` and of `G` by the rules (R), (L) and (AS) of
`AInfinity.FunctorComposition.Assoc` and the unit laws of `AInfinity.ComposableMultilinearMap`:
$$(G \circ F) \circ (\mathbb 1 \mid m) = G \circ (F \mid F \circ (\mathbb 1 \mid m))
  = G \circ (F \mid m' \circ F) = (G \circ (\mathbb 1 \mid m')) \circ F
  = (m'' \circ G) \circ F = m'' \circ (G \circ F).$$
The first equality is (R) and `comp_id`, the second the functor equations of `F`, the third (L)
and `id_comp`, the fourth the functor equations of `G`, and the last (AS).
-/

@[expose] public section

noncomputable section

namespace AInfinityTheory

open GradedLinearQuiver

variable {n : ℕ} {β β' β'' β''' : Type*} [AddCommGroup β] [Grading β] [AddCommGroup β']
  [Grading β'] [AddCommGroup β''] [Grading β''] [AddCommGroup β'''] [Grading β''']
  {R : Type*} [Semiring R] {Obj Obj' Obj'' Obj''' : Type*}

/-! ### The composite of A∞-functor data -/

namespace AInfinityFunctorData

variable [GradedLinearQuiver β R Obj] [GradedLinearQuiver β' R Obj']
  [GradedLinearQuiver β'' R Obj''] [GradedLinearQuiver β''' R Obj''']

/-- The composite `G.comp F` of A∞-functor data `F` from `Obj` to `Obj'` and `G` from `Obj'` to
`Obj''`, written in Mathlib's order: it acts on objects by `G.obj ∘ F.obj`, translates degrees
along `G.degMap.comp F.degMap`, and its components are those of the composite of the components
of `G` and of `F` as composable multilinear maps. -/
protected def comp (G : AInfinityFunctorData β' β'' R Obj' Obj'')
    (F : AInfinityFunctorData β β' R Obj Obj') : AInfinityFunctorData β β'' R Obj Obj'' where
  obj X := G.obj (F.obj X)
  degMap := G.degMap.comp F.degMap
  toComposableMultilinearMap := G.toComposableMultilinearMap.comp F.toComposableMultilinearMap

@[simp]
lemma comp_obj (G : AInfinityFunctorData β' β'' R Obj' Obj'')
    (F : AInfinityFunctorData β β' R Obj Obj') (X : Obj) : (G.comp F).obj X = G.obj (F.obj X) :=
  rfl

@[simp]
lemma comp_degMap (G : AInfinityFunctorData β' β'' R Obj' Obj'')
    (F : AInfinityFunctorData β β' R Obj Obj') : (G.comp F).degMap = G.degMap.comp F.degMap :=
  rfl

@[simp]
lemma comp_toComposableMultilinearMap (G : AInfinityFunctorData β' β'' R Obj' Obj'')
    (F : AInfinityFunctorData β β' R Obj Obj') :
    (G.comp F).toComposableMultilinearMap =
      G.toComposableMultilinearMap.comp F.toComposableMultilinearMap :=
  rfl

/-- The composition of A∞-functor data is associative. -/
theorem comp_assoc (H : AInfinityFunctorData β'' β''' R Obj'' Obj''')
    (G : AInfinityFunctorData β' β'' R Obj' Obj'') (F : AInfinityFunctorData β β' R Obj Obj') :
    (H.comp G).comp F = H.comp (G.comp F) :=
  congrArg (mk _ _) (ComposableMultilinearMap.comp_assoc _ _ _)

end AInfinityFunctorData

namespace AInfinityFunctor

variable [AInfinityCategory β R Obj] [AInfinityCategory β' R Obj'] [AInfinityCategory β'' R Obj'']
  [AInfinityCategory β''' R Obj''']

/-! ### The functor equations as equalities of composable multilinear maps -/

/-- The A∞-functor equations of `F`, as an equality of composable multilinear maps:
F ∘ (𝟙 | m) = m' ∘ F. -/
theorem compMarked_id_eq_comp (F : AInfinityFunctor β β' R Obj Obj') :
    F.toComposableMultilinearMap.compMarked (ComposableMultilinearMap.id β R Obj)
        (AInfinityCategoryStruct.toComposableMultilinearMap β R Obj) one_add_one_eq_two =
      (AInfinityCategoryStruct.toComposableMultilinearMap β' R Obj').comp
        F.toComposableMultilinearMap := by
  ext n _ X deg a j hj
  exact (F.toAInfinityFunctorData.mapCompSum_eq_compMarked_map_v a j hj).symm.trans
    ((F.mapCompSum_eq_compMapSum a hj).trans
      (F.toAInfinityFunctorData.compMapSum_eq_comp_map_v a j hj))

section Comp

variable (G : AInfinityFunctor β' β'' R Obj' Obj'') (F : AInfinityFunctor β β' R Obj Obj')

/-- The A∞-functor equations of a composite, as an equality of composable multilinear maps:
(G ∘ F) ∘ (𝟙 | m) = m'' ∘ (G ∘ F). -/
theorem comp_compMarked_id_eq_comp :
    (G.toComposableMultilinearMap.comp F.toComposableMultilinearMap).compMarked
        (ComposableMultilinearMap.id β R Obj)
        (AInfinityCategoryStruct.toComposableMultilinearMap β R Obj) one_add_one_eq_two =
      (AInfinityCategoryStruct.toComposableMultilinearMap β'' R Obj'').comp
        (G.toComposableMultilinearMap.comp F.toComposableMultilinearMap) := by
  have h₁ := ComposableMultilinearMap.comp_compMarked G.toComposableMultilinearMap
    F.toComposableMultilinearMap (ComposableMultilinearMap.id β R Obj)
    (AInfinityCategoryStruct.toComposableMultilinearMap β R Obj) one_add_one_eq_two
  rw [ComposableMultilinearMap.comp_id, F.compMarked_id_eq_comp] at h₁
  have h₂ := ComposableMultilinearMap.compMarked_comp G.toComposableMultilinearMap
    (ComposableMultilinearMap.id β' R Obj')
    (AInfinityCategoryStruct.toComposableMultilinearMap β' R Obj') F.toComposableMultilinearMap
    one_add_one_eq_two
  rw [ComposableMultilinearMap.id_comp, G.compMarked_id_eq_comp] at h₂
  exact h₁.trans (h₂.symm.trans (ComposableMultilinearMap.comp_assoc _ _ _))

/-- The composite of two A∞-functors satisfies the A∞-functor equations. -/
theorem comp_mapCompSum_eq_compMapSum {X : Fin (n + 1) → Obj} {deg : Fin n → β}
    (a : ∀ i : Fin n, ComposableHom β R X i (deg i)) [NeZero n] {d : β}
    (hd : targetDeg 2 deg = d) :
    (G.toAInfinityFunctorData.comp F.toAInfinityFunctorData).mapCompSum a d hd =
      (G.toAInfinityFunctorData.comp F.toAInfinityFunctorData).compMapSum a d hd := by
  rw [AInfinityFunctorData.mapCompSum_eq_compMarked_map_v,
    AInfinityFunctorData.compMapSum_eq_comp_map_v]
  exact congrArg (fun Ψ : ComposableMultilinearMap R _ _ 2 ↦ (Ψ.map X).v deg d hd a)
    (comp_compMarked_id_eq_comp G F)

/-! ### The composite of A∞-functors -/

/-- The composite `G.comp F` of A∞-functors `F` from `Obj` to `Obj'` and `G` from `Obj'` to
`Obj''`, written in Mathlib's order: the composite of the underlying A∞-functor data, which
satisfies the A∞-functor equations by `comp_mapCompSum_eq_compMapSum`. -/
protected def comp : AInfinityFunctor β β'' R Obj Obj'' where
  toAInfinityFunctorData := G.toAInfinityFunctorData.comp F.toAInfinityFunctorData
  mapCompSum_eq_compMapSum a _ hd := comp_mapCompSum_eq_compMapSum G F a hd

@[simp]
lemma comp_toAInfinityFunctorData :
    (G.comp F).toAInfinityFunctorData = G.toAInfinityFunctorData.comp F.toAInfinityFunctorData :=
  rfl

end Comp

/-! ### Associativity -/

/-- The composition of A∞-functors is associative. -/
theorem comp_assoc (H : AInfinityFunctor β'' β''' R Obj'' Obj''')
    (G : AInfinityFunctor β' β'' R Obj' Obj'') (F : AInfinityFunctor β β' R Obj Obj') :
    (H.comp G).comp F = H.comp (G.comp F) :=
  toAInfinityFunctorData_injective (AInfinityFunctorData.comp_assoc _ _ _)

end AInfinityFunctor

end AInfinityTheory
