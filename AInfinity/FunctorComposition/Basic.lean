/-
Copyright (c) 2026 Annie Yao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Annie Yao, Marco David, Zhan Shi
-/
module

public import AInfinity.FunctorComposition.StasheffSum

/-! # Composition of A∞-functors

The composite `G.comp F` of A∞-functors `F` from `Obj` to `Obj'` and `G` from `Obj'` to `Obj''` is
the composite of the underlying A∞-functor data. This file proves that it satisfies the
A∞-functor equations, and that the composition of A∞-functors is associative.

## Main definitions

* `AInfinityTheory.AInfinityFunctor.comp`: the composite `G.comp F` of A∞-functors.

## Main results

* `AInfinityTheory.AInfinityFunctor.compMarked_id_eq_comp`: the A∞-functor equations of `F`, as
  the equality F ∘ (𝟙 | m) = m' ∘ F of composable multilinear maps.
* `AInfinityTheory.AInfinityFunctor.comp_mapCompSum_eq_compMapSum`: the composite of two
  A∞-functors satisfies the A∞-functor equations.
* `AInfinityTheory.AInfinityFunctor.comp_assoc`: the composition of A∞-functors is associative.

## Implementation notes

With the operations m, m' and m'' of the three A∞-categories, the A∞-functor equations of the
composite follow from those of `F` and of `G` by the rules (R), (L) and (AS) of
`AInfinity.FunctorComposition.Assoc` and the unit laws of `AInfinity.FunctorComposition.Unit`:
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

variable {n : ℕ}

/-! ### The functor equations as equalities of composable multilinear maps -/

namespace AInfinityFunctor

variable {β β' β'' : Type*} [AddCommGroup β] [Grading β] [AddCommGroup β'] [Grading β']
  [AddCommGroup β''] [Grading β''] {R : Type*} [Semiring R] {Obj Obj' Obj'' : Type*}
  [AInfinityCategory β R Obj] [AInfinityCategory β' R Obj'] [AInfinityCategory β'' R Obj'']

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

variable {X : Fin (n + 1) → Obj} {deg : Fin n → β} (a : ∀ i : Fin n, ComposableHom β R X i (deg i))
  [NeZero n] {d : β} (hd : targetDeg 2 deg = d)

/-- The composite of two A∞-functors satisfies the A∞-functor equations. -/
theorem comp_mapCompSum_eq_compMapSum :
    (G.toAInfinityFunctorData.comp F.toAInfinityFunctorData).mapCompSum a d hd =
      (G.toAInfinityFunctorData.comp F.toAInfinityFunctorData).compMapSum a d hd := by
  rw [AInfinityFunctorData.mapCompSum_eq_compMarked_map_v,
    AInfinityFunctorData.compMapSum_eq_comp_map_v]
  exact congrArg (fun Ψ : ComposableMultilinearMap R _ _ 2 ↦ (Ψ.map X).v deg d hd a)
    (comp_compMarked_id_eq_comp G F)

/-! ### The composite of A∞-functors -/

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

/-! ### Associativity -/

namespace AInfinityFunctor

variable {β β' : Type*} [AddCommGroup β] [Grading β] [AddCommGroup β'] [Grading β']
  {R : Type*} [Semiring R] {Obj Obj' : Type*} [AInfinityCategory β R Obj]
  [AInfinityCategory β' R Obj']

/-- An A∞-functor is determined by its A∞-functor data, since the functor equations are a
proposition. -/
lemma toAInfinityFunctorData_injective :
    Function.Injective (toAInfinityFunctorData : AInfinityFunctor β β' R Obj Obj' → _) := by
  rintro ⟨F, hF⟩ ⟨G, hG⟩ rfl
  rfl

variable {β'' β''' : Type*} [AddCommGroup β''] [Grading β''] [AddCommGroup β'''] [Grading β''']
  {Obj'' Obj''' : Type*} [AInfinityCategory β'' R Obj''] [AInfinityCategory β''' R Obj''']

/-- The composition of A∞-functors is associative. -/
theorem comp_assoc (H : AInfinityFunctor β'' β''' R Obj'' Obj''')
    (G : AInfinityFunctor β' β'' R Obj' Obj'') (F : AInfinityFunctor β β' R Obj Obj') :
    (H.comp G).comp F = H.comp (G.comp F) :=
  toAInfinityFunctorData_injective (AInfinityFunctorData.comp_assoc _ _ _)

end AInfinityFunctor

end AInfinityTheory
