/-
Copyright (c) 2026 Zhan Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhan Shi
-/
module

public import AInfinity.AInfinityFunctor

/-! # Heterogeneous congruence lemmas for the composition of A∞-functors

Morphisms between objects that are equal only propositionally are compared with `HEq`: after
removing all transports `homCongr`, two applications of a component of a functor or of an
operation agree as soon as their arities, object strings, degrees and inputs do. This file
collects such congruence lemmas. They are used in `AInfinity.FunctorComposition.Reindex` to
match the two descriptions of a term of the functor equation for a composite of A∞-functors.

## Main results

* `Fin.hfunext`: function extensionality for dependent functions on `Fin k` and `Fin k'`.
* `AInfinityTheory.AInfinityCategoryStruct.m_v_heq`: congruence for the operations `m`.
* `AInfinityTheory.AInfinityFunctorData.map_v_heq`: congruence for the components of
  A∞-functor data.
* `AInfinityTheory.AInfinityFunctorData.compositionBlockMap_heq`: congruence for the values of
  the components of A∞-functor data on the blocks of compositions.
-/

public section

universe u in
/-- Dependent functions on `Fin k` and `Fin k'`, for `k = k'`, are heterogeneously equal as
soon as they agree at corresponding points. -/
protected lemma Fin.hfunext {k k' : ℕ} (e : k = k') {α : Fin k → Sort u} {α' : Fin k' → Sort u}
    {f : ∀ i, α i} {f' : ∀ i, α' i} (h : ∀ i : Fin k, f i ≍ f' (i.cast e)) : f ≍ f' := by
  refine Function.hfunext (by rw [e]) fun i i' hi ↦ ?_
  obtain rfl : i' = i.cast e := Fin.ext ((Fin.heq_ext_iff e).1 hi).symm
  exact h i
namespace AInfinityTheory

open GradedLinearQuiver

variable {n : ℕ}

/-! ### Transport along equalities of positions -/

namespace GradedLinearQuiver

variable {β R : Type*} [Semiring R] {Obj : Type*} [GradedLinearQuiver β R Obj]

lemma homCongr_heq {X X' Y Y' : Obj} {i i' : β} (hX : X = X') (hY : Y = Y') (hi : i = i')
    (x : (X →ᵍ[R] Y) i) : homCongr R hX hY hi x ≍ x := by
  subst hX hY hi
  rfl

@[simp]
lemma homCongr_homCongr {X X' X'' Y Y' Y'' : Obj} {i i' i'' : β} (hX : X = X') (hY : Y = Y')
    (hi : i = i') (hX' : X' = X'') (hY' : Y' = Y'') (hi' : i' = i'') (x : (X →ᵍ[R] Y) i) :
    homCongr R hX' hY' hi' (homCongr R hX hY hi x) =
      homCongr R (hX.trans hX') (hY.trans hY') (hi.trans hi') x := by
  subst hX hY hi hX' hY' hi'
  rfl

end GradedLinearQuiver

section Degrees

variable {β : Type*} [AddCommGroup β] [Grading β]

lemma functorTargetDeg_congr_heq {k k' : ℕ} (e : k = k') {δ : Fin k → β} {δ' : Fin k' → β}
    (h : δ ≍ δ') : functorTargetDeg δ = functorTargetDeg δ' := by
  subst e
  cases h
  rfl

lemma operationTargetDeg_congr_heq {k k' : ℕ} (e : k = k') {δ : Fin k → β} {δ' : Fin k' → β}
    (h : δ ≍ δ') : operationTargetDeg δ = operationTargetDeg δ' := by
  subst e
  cases h
  rfl
omit [AddCommGroup β] [Grading β] in
/-- If two compositions have a block in the same position and of the same size, the degrees of
the inputs in these blocks agree. -/
lemma embedding_heq_of_sizeUpTo_eq (deg : Fin n → β) {c₁ c₂ : Composition n}
    {l₁ : Fin c₁.length} {l₂ : Fin c₂.length} (hs : c₁.sizeUpTo l₁ = c₂.sizeUpTo l₂)
    (e : c₁.blocksFun l₁ = c₂.blocksFun l₂) :
    (fun i ↦ deg (c₁.embedding l₁ i)) ≍ fun i ↦ deg (c₂.embedding l₂ i) :=
  Fin.hfunext e fun i ↦ heq_of_eq (congrArg deg (Fin.ext (by simp [hs])))

end Degrees
/-- A block of a composition of `n` lying inside the `j`-th block of a composition `c` carries the
same input degrees as the corresponding block of a composition of that block. -/
lemma embedding_heq_embedding_embedding {β : Type*} (deg : Fin n → β) {c₁ c : Composition n}
    {l₁ : Fin c₁.length} {j : Fin c.length} {c₂ : Composition (c.blocksFun j)} {l₂ : Fin c₂.length}
    (hs : c₁.sizeUpTo l₁ = c.sizeUpTo j + c₂.sizeUpTo l₂) (e : c₁.blocksFun l₁ = c₂.blocksFun l₂) :
    (fun i ↦ deg (c₁.embedding l₁ i)) ≍ fun i ↦ deg (c.embedding j (c₂.embedding l₂ i)) :=
  Fin.hfunext e fun i ↦ heq_of_eq (congrArg deg (Fin.ext (by simp [hs, add_assoc])))
section Positions

variable {β : Type*} [AddCommGroup β] [Grading β] (deg : Fin n → β) (p : StasheffIndex n)

lemma stasheffDegOut_of_lt (i : Fin (p.r + 1 + p.t)) (i' : Fin n) (h : (i : ℕ) < p.r)
    (h' : (i' : ℕ) = i) : stasheffDegOut deg p i = deg i' := by
  obtain ⟨j, rfl⟩ : ∃ j : Fin p.r, j.castSucc.castAdd p.t = i := ⟨⟨i, h⟩, Fin.ext rfl⟩
  obtain rfl : i' = p.leftIndex j := Fin.ext h'
  exact stasheffDegOut_left deg p j

lemma stasheffDegOut_of_gt (i : Fin (p.r + 1 + p.t)) (i' : Fin n) (h : p.r < i)
    (h' : (i' : ℕ) = (i : ℕ) + p.s - 1) : stasheffDegOut deg p i = deg i' := by
  have := i.2
  obtain ⟨k, rfl⟩ : ∃ k : Fin p.t, k.natAdd (p.r + 1) = i :=
    ⟨⟨i - (p.r + 1), by omega⟩, Fin.ext (by simp only [Fin.natAdd_mk]; omega)⟩
  obtain rfl : i' = p.rightIndex k :=
    Fin.ext (by simp only [Fin.val_natAdd, StasheffIndex.val_rightIndex] at h' ⊢; omega)
  exact stasheffDegOut_right deg p k

lemma stasheffDegOut_of_eq (i : Fin (p.r + 1 + p.t)) (h : (i : ℕ) = p.r) :
    stasheffDegOut deg p i = stasheffInnerDeg deg p := by
  obtain rfl : i = p.middleIndex := Fin.ext h
  exact stasheffDegOut_middle deg p

variable {R : Type*} [Semiring R] {Obj : Type*} [AInfinityCategoryStruct β R Obj]
  {X : Fin (n + 1) → Obj} {deg} (a : ∀ i : Fin n, ComposableHom β R X i (deg i))

lemma stasheffInputsOut_heq_of_lt (i : Fin (p.r + 1 + p.t)) (i' : Fin n) (h : (i : ℕ) < p.r)
    (h' : (i' : ℕ) = i) : stasheffInputsOut a p i ≍ a i' := by
  obtain ⟨j, rfl⟩ : ∃ j : Fin p.r, j.castSucc.castAdd p.t = i := ⟨⟨i, h⟩, Fin.ext rfl⟩
  obtain rfl : i' = p.leftIndex j := Fin.ext h'
  rw [stasheffInputsOut_left]
  exact homCongr_heq _ _ _ _

lemma stasheffInputsOut_heq_of_gt (i : Fin (p.r + 1 + p.t)) (i' : Fin n) (h : p.r < i)
    (h' : (i' : ℕ) = (i : ℕ) + p.s - 1) : stasheffInputsOut a p i ≍ a i' := by
  have := i.2
  obtain ⟨k, rfl⟩ : ∃ k : Fin p.t, k.natAdd (p.r + 1) = i :=
    ⟨⟨i - (p.r + 1), by omega⟩, Fin.ext (by simp only [Fin.natAdd_mk]; omega)⟩
  obtain rfl : i' = p.rightIndex k :=
    Fin.ext (by simp only [Fin.val_natAdd, StasheffIndex.val_rightIndex] at h' ⊢; omega)
  rw [stasheffInputsOut_right]
  exact homCongr_heq _ _ _ _

/-- Congruence for the operations `m` along an equality of arities, object strings, degrees and
inputs. -/
lemma AInfinityCategoryStruct.m_v_heq {k k' : ℕ} [NeZero k] [NeZero k'] (e : k = k')
    {Y : Fin (k + 1) → Obj} {Y' : Fin (k' + 1) → Obj} (hY : Y ≍ Y') {δ : Fin k → β}
    {δ' : Fin k' → β} (hδ : δ ≍ δ') {j j' : β} (hj : operationTargetDeg δ = j)
    (hj' : operationTargetDeg δ' = j') {b : ∀ i, ComposableHom β R Y i (δ i)}
    {b' : ∀ i, ComposableHom β R Y' i (δ' i)} (hb : b ≍ b') :
    (AInfinityCategoryStruct.m Y).v δ j hj b ≍ (AInfinityCategoryStruct.m Y').v δ' j' hj' b' := by
  subst e hj hj'
  cases hY
  cases hδ
  cases hb
  rfl

/-- Two inner outputs of Stasheff terms agree as soon as their arities, objects, degrees and
inputs do. -/
lemma stasheffInner_heq {n' : ℕ} {X' : Fin (n' + 1) → Obj} {deg' : Fin n' → β}
    (a' : ∀ i, ComposableHom β R X' i (deg' i)) (p' : StasheffIndex n') (e : p.s = p'.s)
    (hX : ∀ u, X (p.innerBoundary u) = X' (p'.innerBoundary (u.cast (by rw [e]))))
    (hdeg : ∀ u, deg (p.innerIndex u) = deg' (p'.innerIndex (u.cast e)))
    (ha : ∀ u, a (p.innerIndex u) ≍ a' (p'.innerIndex (u.cast e))) {d d' : β}
    (hd : stasheffInnerDeg deg p = d) (hd' : stasheffInnerDeg deg' p' = d') :
    stasheffInner a p d hd ≍ stasheffInner a' p' d' hd' :=
  AInfinityCategoryStruct.m_v_heq e (Fin.hfunext (by rw [e]) fun u ↦ heq_of_eq (hX u))
    (Fin.hfunext e fun u ↦ heq_of_eq (hdeg u)) hd hd' (Fin.hfunext e ha)

lemma stasheffInputsOut_heq_of_eq (i : Fin (p.r + 1 + p.t)) (h : (i : ℕ) = p.r) {d : β}
    (hd : stasheffInnerDeg deg p = d) : stasheffInputsOut a p i ≍ stasheffInner a p d hd := by
  obtain rfl : i = p.middleIndex := Fin.ext h
  rw [stasheffInputsOut_middle]
  exact (homCongr_heq _ _ _ _).trans (stasheffInner_heq p a a p rfl (fun _ ↦ rfl) (fun _ ↦ rfl)
    (fun _ ↦ HEq.rfl) _ _)

end Positions

namespace AInfinityFunctorData

variable {β β' β'' : Type*} [AddCommGroup β] [Grading β] [AddCommGroup β'] [Grading β']
  [AddCommGroup β''] [Grading β''] {R : Type*} [Semiring R] {Obj Obj' Obj'' : Type*}

section Congruence

variable [GradedLinearQuiver β R Obj] [GradedLinearQuiver β' R Obj']
  (F : AInfinityFunctorData β β' R Obj Obj')

/-- Congruence for the components of A∞-functor data along an equality of arities, object
strings, degrees and inputs. -/
lemma map_v_heq {k k' : ℕ} [NeZero k] [NeZero k'] (e : k = k') {Y : Fin (k + 1) → Obj}
    {Y' : Fin (k' + 1) → Obj} (hY : Y ≍ Y') {δ : Fin k → β} {δ' : Fin k' → β} (hδ : δ ≍ δ')
    {j j' : β} (hj : functorTargetDeg δ = j) (hj' : functorTargetDeg δ' = j')
    {b : ∀ i, ComposableHom β R Y i (δ i)} {b' : ∀ i, ComposableHom β R Y' i (δ' i)}
    (hb : b ≍ b') : (F.map Y).v δ j hj b ≍ (F.map Y').v δ' j' hj' b' := by
  subst e hj hj'
  cases hY
  cases hδ
  cases hb
  rfl

/-- The values of `F` on two blocks of compositions, possibly of different composable strings,
agree as soon as the blocks have the same size, objects, degrees and inputs. -/
lemma compositionBlockMap_heq {n₁ n₂ : ℕ} {X₁ : Fin (n₁ + 1) → Obj} {X₂ : Fin (n₂ + 1) → Obj}
    {deg₁ : Fin n₁ → β} {deg₂ : Fin n₂ → β} (a₁ : ∀ i, ComposableHom β R X₁ i (deg₁ i))
    (a₂ : ∀ i, ComposableHom β R X₂ i (deg₂ i)) {c₁ : Composition n₁} {l₁ : Fin c₁.length}
    {c₂ : Composition n₂} {l₂ : Fin c₂.length} (e : c₁.blocksFun l₁ = c₂.blocksFun l₂)
    (hX : ∀ i, compositionBlockObj X₁ c₁ l₁ i = compositionBlockObj X₂ c₂ l₂ (i.cast (by rw [e])))
    (hdeg : ∀ i, deg₁ (c₁.embedding l₁ i) = deg₂ (c₂.embedding l₂ (i.cast e)))
    (ha : ∀ i, a₁ (c₁.embedding l₁ i) ≍ a₂ (c₂.embedding l₂ (i.cast e))) :
    F.compositionBlockMap a₁ c₁ l₁ ≍ F.compositionBlockMap a₂ c₂ l₂ :=
  (homCongr_heq _ _ _ _).trans <| HEq.trans (F.map_v_heq e
    (Fin.hfunext (by rw [e]) fun i ↦ heq_of_eq (hX i)) (Fin.hfunext e fun i ↦ heq_of_eq (hdeg i))
    rfl rfl (Fin.hfunext e ha)) (homCongr_heq _ _ _ _).symm

variable {X : Fin (n + 1) → Obj} {deg : Fin n → β} (a : ∀ i : Fin n, ComposableHom β R X i (deg i))

/-- Two blocks of compositions of `n` in the same position and of the same size have the same
value under `F`. -/
lemma compositionBlockMap_heq_of_sizeUpTo_eq {c₁ c₂ : Composition n} {l₁ : Fin c₁.length}
    {l₂ : Fin c₂.length} (hs : c₁.sizeUpTo l₁ = c₂.sizeUpTo l₂)
    (e : c₁.blocksFun l₁ = c₂.blocksFun l₂) :
    F.compositionBlockMap a c₁ l₁ ≍ F.compositionBlockMap a c₂ l₂ :=
  F.compositionBlockMap_heq a a e (fun i ↦ congrArg X (Fin.ext (by simp [hs])))
    (fun i ↦ congrArg deg (Fin.ext (by simp [hs])))
    (fun i ↦ congr_arg_heq a (Fin.ext (by simp [hs])))

/-- A block of a composition of `n` that lies inside the `j`-th block of another composition `c`
has the same value under `F` as the corresponding block of a composition of that block. -/
lemma compositionBlockMap_heq_compositionBlockMap_embedding {c₁ c : Composition n}
    {l₁ : Fin c₁.length} {j : Fin c.length} {c₂ : Composition (c.blocksFun j)}
    {l₂ : Fin c₂.length} (hs : c₁.sizeUpTo l₁ = c.sizeUpTo j + c₂.sizeUpTo l₂)
    (e : c₁.blocksFun l₁ = c₂.blocksFun l₂) :
    F.compositionBlockMap a c₁ l₁ ≍
      F.compositionBlockMap (X := compositionBlockObj X c j) (fun i ↦ a (c.embedding j i)) c₂ l₂ :=
  F.compositionBlockMap_heq _ _ e
    (fun i ↦ congrArg X (Fin.ext (by simp [hs, add_assoc])))
    (fun i ↦ congrArg deg (Fin.ext (by simp [hs, add_assoc])))
    (fun i ↦ congr_arg_heq a (Fin.ext (by simp [hs, add_assoc])))

end Congruence

end AInfinityFunctorData

end AInfinityTheory
