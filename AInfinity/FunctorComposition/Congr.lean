/-
Copyright (c) 2026 Zhan Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhan Shi
-/
module

public import AInfinity.AInfinityFunctor

/-! # Congruence lemmas for the composition of A∞-functors

Two applications of a component of a functor or of an operation may have different arities,
object strings and degrees that are only propositionally equal. They are compared by transporting
one of them with `homCongr` along the equalities of objects and degrees: inputs of arities `k` and
`k'` are matched along `e : k = k'` by `Fin.cast e`, and a statement
`homCongr R hX hY hi x = y` says that `x` is `y` after transport. This file collects such
congruence lemmas. They are used in `AInfinity.FunctorComposition.Reindex` to match the two
descriptions of a term of the functor equation for a composite of A∞-functors.

## Main results

* `AInfinityTheory.GradedLinearQuiver.homCongr_eq_trans`,
  `AInfinityTheory.GradedLinearQuiver.homCongr_eq_symm`: transitivity and symmetry of equality
  after transport.
* `AInfinityTheory.AInfinityCategoryStruct.m_v_congr`: congruence for the operations `m`.
* `AInfinityTheory.AInfinityFunctorData.map_v_congr`: congruence for the components of
  A∞-functor data.
* `AInfinityTheory.AInfinityFunctorData.compositionBlockMap_congr`: congruence for the values of
  the components of A∞-functor data on the blocks of compositions.

## Implementation notes

The transports in the conclusions of these lemmas are given by explicit proofs built from the
hypotheses, so that the lemmas compose with `homCongr_eq_trans` and `homCongr_eq_symm` without
further arguments. By proof irrelevance, they apply to any other proofs of the same equalities.
-/

public section

namespace AInfinityTheory

open GradedLinearQuiver

variable {n : ℕ}

/-! ### Transport along equalities of positions -/

namespace GradedLinearQuiver

variable {β R : Type*} [Semiring R] {Obj : Type*} [GradedLinearQuiver β R Obj]

@[simp]
lemma homCongr_homCongr {X X' X'' Y Y' Y'' : Obj} {i i' i'' : β} (hX : X = X') (hY : Y = Y')
    (hi : i = i') (hX' : X' = X'') (hY' : Y' = Y'') (hi' : i' = i'') (x : (X →ᵍ[R] Y) i) :
    homCongr R hX' hY' hi' (homCongr R hX hY hi x) =
      homCongr R (hX.trans hX') (hY.trans hY') (hi.trans hi') x := by
  subst hX hY hi hX' hY' hi'
  rfl

variable {X X' X'' Y Y' Y'' : Obj} {i i' i'' : β} {hX : X = X'} {hY : Y = Y'} {hi : i = i'}
  {x : (X →ᵍ[R] Y) i} {y : (X' →ᵍ[R] Y') i'}

/-- If `x` is `y` after transport and `y` is `z` after transport, then `x` is `z` after
transport. -/
lemma homCongr_eq_trans {hX' : X' = X''} {hY' : Y' = Y''} {hi' : i' = i''}
    {z : (X'' →ᵍ[R] Y'') i''} (h₁ : homCongr R hX hY hi x = y)
    (h₂ : homCongr R hX' hY' hi' y = z) :
    homCongr R (hX.trans hX') (hY.trans hY') (hi.trans hi') x = z := by
  rw [← h₂, ← h₁, homCongr_homCongr]

/-- If `x` is `y` after transport, then `y` is `x` after the inverse transport. -/
lemma homCongr_eq_symm (h : homCongr R hX hY hi x = y) :
    homCongr R hX.symm hY.symm hi.symm y = x := by
  subst h hX hY hi
  rfl

/-- If `x` is `y` after transport, then `x` and `y` agree after transport to any common hom
space. -/
lemma homCongr_eq_homCongr_of_eq (h : homCongr R hX hY hi x = y) {hX₁ : X = X''}
    {hY₁ : Y = Y''} {hi₁ : i = i''} {hX₂ : X' = X''} {hY₂ : Y' = Y''} {hi₂ : i' = i''} :
    homCongr R hX₁ hY₁ hi₁ x = homCongr R hX₂ hY₂ hi₂ y := by
  rw [← h, homCongr_homCongr]

/-- The value of a family of morphisms at `i` is its value at `i'` after transport along
`i = i'`. -/
lemma homCongr_congrArg {ι : Sort*} {A B : ι → Obj} {δ : ι → β} (f : ∀ i, (A i →ᵍ[R] B i) (δ i))
    {j j' : ι} (h : j = j') :
    homCongr R (congrArg A h) (congrArg B h) (congrArg δ h) (f j) = f j' := by
  subst h
  rfl

end GradedLinearQuiver

section Degrees

variable {β : Type*} [AddCommGroup β] [Grading β]

lemma functorTargetDeg_congr {k k' : ℕ} (e : k = k') {δ : Fin k → β} {δ' : Fin k' → β}
    (h : ∀ i, δ i = δ' (i.cast e)) : functorTargetDeg δ = functorTargetDeg δ' := by
  subst e
  obtain rfl : δ = δ' := funext h
  rfl

lemma operationTargetDeg_congr {k k' : ℕ} (e : k = k') {δ : Fin k → β} {δ' : Fin k' → β}
    (h : ∀ i, δ i = δ' (i.cast e)) : operationTargetDeg δ = operationTargetDeg δ' := by
  subst e
  obtain rfl : δ = δ' := funext h
  rfl

end Degrees

/-- If two compositions have a block in the same position and of the same size, the inputs in
these blocks agree. -/
lemma _root_.Composition.embedding_eq_of_sizeUpTo_eq {c₁ c₂ : Composition n}
    {l₁ : Fin c₁.length} {l₂ : Fin c₂.length} (hs : c₁.sizeUpTo l₁ = c₂.sizeUpTo l₂)
    (e : c₁.blocksFun l₁ = c₂.blocksFun l₂) (i : Fin (c₁.blocksFun l₁)) :
    c₁.embedding l₁ i = c₂.embedding l₂ (i.cast e) :=
  Fin.ext (by simp [hs])

/-- A block of a composition of `n` lying inside the `j`-th block of a composition `c` consists
of the same inputs as the corresponding block of a composition of that block. -/
lemma _root_.Composition.embedding_eq_embedding_embedding {c₁ c : Composition n}
    {l₁ : Fin c₁.length} {j : Fin c.length} {c₂ : Composition (c.blocksFun j)} {l₂ : Fin c₂.length}
    (hs : c₁.sizeUpTo l₁ = c.sizeUpTo j + c₂.sizeUpTo l₂) (e : c₁.blocksFun l₁ = c₂.blocksFun l₂)
    (i : Fin (c₁.blocksFun l₁)) :
    c₁.embedding l₁ i = c.embedding j (c₂.embedding l₂ (i.cast e)) :=
  Fin.ext (by simp [hs, add_assoc])

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

section Objects

variable {Obj : Type*} (X : Fin (n + 1) → Obj)

lemma stasheffObjOut_castSucc_of_le (i : Fin (p.r + 1 + p.t)) (i' : Fin (n + 1))
    (h : (i : ℕ) ≤ p.r) (h' : (i' : ℕ) = i) : stasheffObjOut X p i.castSucc = X i' := by
  rw [show i.castSucc = Fin.castAdd (p.t + 1) ⟨(i : ℕ), by omega⟩ from Fin.ext rfl]
  exact congrArg X (Fin.ext ((p.val_outerBoundary_castAdd _).trans h'.symm))

lemma stasheffObjOut_succ_of_lt (i : Fin (p.r + 1 + p.t)) (i' : Fin (n + 1))
    (h : (i : ℕ) < p.r) (h' : (i' : ℕ) = i + 1) : stasheffObjOut X p i.succ = X i' := by
  rw [show i.succ = Fin.castAdd (p.t + 1) ⟨(i : ℕ) + 1, by omega⟩ from Fin.ext rfl]
  exact congrArg X (Fin.ext ((p.val_outerBoundary_castAdd _).trans h'.symm))

lemma stasheffObjOut_castSucc_of_gt (i : Fin (p.r + 1 + p.t)) (i' : Fin (n + 1))
    (h : p.r < i) (h' : (i' : ℕ) = (i : ℕ) + p.s - 1) : stasheffObjOut X p i.castSucc = X i' := by
  have := i.2; have := p.one_le_s
  rw [show i.castSucc = Fin.natAdd (p.r + 1) (⟨(i : ℕ) - (p.r + 1), by omega⟩ : Fin (p.t + 1)) from
    Fin.ext (by simp only [Fin.val_castSucc, Fin.val_natAdd]; omega)]
  exact congrArg X (Fin.ext ((p.val_outerBoundary_natAdd _).trans (by simp only; omega)))

lemma stasheffObjOut_succ_of_ge (i : Fin (p.r + 1 + p.t)) (i' : Fin (n + 1))
    (h : p.r ≤ i) (h' : (i' : ℕ) = (i : ℕ) + p.s) : stasheffObjOut X p i.succ = X i' := by
  have := i.2
  rw [show i.succ = Fin.natAdd (p.r + 1) (⟨(i : ℕ) - p.r, by omega⟩ : Fin (p.t + 1)) from
    Fin.ext (by simp only [Fin.val_succ, Fin.val_natAdd]; omega)]
  exact congrArg X (Fin.ext ((p.val_outerBoundary_natAdd _).trans (by simp only; omega)))

end Objects

variable {R : Type*} [Semiring R] {Obj : Type*} [AInfinityCategoryStruct β R Obj]
  {X : Fin (n + 1) → Obj} {deg} (a : ∀ i : Fin n, ComposableHom β R X i (deg i))

/-- Before the inner output, an input of the outer operation of a Stasheff term is an original
input. -/
lemma homCongr_stasheffInputsOut_of_lt (i : Fin (p.r + 1 + p.t)) (i' : Fin n) (h : (i : ℕ) < p.r)
    (h' : (i' : ℕ) = i) :
    homCongr R (stasheffObjOut_castSucc_of_le p X i i'.castSucc h.le h')
      (stasheffObjOut_succ_of_lt p X i i'.succ h (by simp [h']))
      (stasheffDegOut_of_lt deg p i i' h h') (stasheffInputsOut a p i) = a i' := by
  obtain ⟨j, rfl⟩ : ∃ j : Fin p.r, j.castSucc.castAdd p.t = i := ⟨⟨i, h⟩, Fin.ext rfl⟩
  obtain rfl : i' = p.leftIndex j := Fin.ext h'
  simp

/-- After the inner output, an input of the outer operation of a Stasheff term is an original
input. -/
lemma homCongr_stasheffInputsOut_of_gt (i : Fin (p.r + 1 + p.t)) (i' : Fin n) (h : p.r < i)
    (h' : (i' : ℕ) = (i : ℕ) + p.s - 1) :
    homCongr R (stasheffObjOut_castSucc_of_gt p X i i'.castSucc h h')
      (stasheffObjOut_succ_of_ge p X i i'.succ h.le (by have := p.one_le_s; simp; omega))
      (stasheffDegOut_of_gt deg p i i' h h') (stasheffInputsOut a p i) = a i' := by
  have := i.2
  obtain ⟨k, rfl⟩ : ∃ k : Fin p.t, k.natAdd (p.r + 1) = i :=
    ⟨⟨i - (p.r + 1), by omega⟩, Fin.ext (by simp only [Fin.natAdd_mk]; omega)⟩
  obtain rfl : i' = p.rightIndex k :=
    Fin.ext (by simp only [Fin.val_natAdd, StasheffIndex.val_rightIndex] at h' ⊢; omega)
  simp

/-- Congruence for the operations `m` along an equality of arities, object strings, degrees and
inputs. -/
lemma AInfinityCategoryStruct.m_v_congr {k k' : ℕ} [NeZero k] [NeZero k'] (e : k = k')
    {Y : Fin (k + 1) → Obj} {Y' : Fin (k' + 1) → Obj} (hY : ∀ i, Y i = Y' (i.cast (by rw [e])))
    {δ : Fin k → β} {δ' : Fin k' → β} (hδ : ∀ i, δ i = δ' (i.cast e)) {j j' : β}
    (hj : operationTargetDeg δ = j) (hj' : operationTargetDeg δ' = j')
    {b : ∀ i, ComposableHom β R Y i (δ i)} {b' : ∀ i, ComposableHom β R Y' i (δ' i)}
    (hb : ∀ i, homCongr R (hY i.castSucc) (hY i.succ) (hδ i) (b i) = b' (i.cast e)) :
    homCongr R ((hY 0).trans (congrArg Y' (Fin.cast_zero _)))
      ((hY _).trans (congrArg Y' Fin.cast_last))
      (hj.symm.trans ((operationTargetDeg_congr e hδ).trans hj'))
      ((AInfinityCategoryStruct.m Y).v δ j hj b) =
        (AInfinityCategoryStruct.m Y').v δ' j' hj' b' := by
  subst e
  obtain rfl : Y = Y' := funext hY
  obtain rfl : δ = δ' := funext hδ
  obtain rfl : b = b' := funext hb
  subst hj hj'
  rfl

/-- Two inner outputs of Stasheff terms agree as soon as their arities, objects, degrees and
inputs do. -/
lemma stasheffInner_congr {n' : ℕ} {X' : Fin (n' + 1) → Obj} {deg' : Fin n' → β}
    (a' : ∀ i, ComposableHom β R X' i (deg' i)) (p' : StasheffIndex n') (e : p.s = p'.s)
    (hX : ∀ u, stasheffObjIn X p u = stasheffObjIn X' p' (u.cast (by rw [e])))
    (hdeg : ∀ u, stasheffDegIn deg p u = stasheffDegIn deg' p' (u.cast e))
    (ha : ∀ u, homCongr R (hX u.castSucc) (hX u.succ) (hdeg u) (a (p.innerIndex u)) =
      a' (p'.innerIndex (u.cast e))) {d d' : β}
    (hd : stasheffInnerDeg deg p = d) (hd' : stasheffInnerDeg deg' p' = d') :
    homCongr R ((hX 0).trans (congrArg (stasheffObjIn X' p') (Fin.cast_zero _)))
      ((hX _).trans (congrArg (stasheffObjIn X' p') Fin.cast_last))
      (hd.symm.trans ((operationTargetDeg_congr e hdeg).trans hd'))
      (stasheffInner a p d hd) = stasheffInner a' p' d' hd' :=
  AInfinityCategoryStruct.m_v_congr e hX hdeg hd hd' ha

lemma homCongr_stasheffInner {d d' : β} (hd : stasheffInnerDeg deg p = d) (h : d = d') :
    homCongr R rfl rfl h (stasheffInner a p d hd) = stasheffInner a p d' (hd.trans h) := by
  subst h
  rfl

/-- The inner output of a Stasheff term is the input of its outer operation at position `r`. -/
lemma homCongr_stasheffInputsOut_of_eq (i : Fin (p.r + 1 + p.t)) (h : (i : ℕ) = p.r) {d : β}
    (hd : stasheffInnerDeg deg p = d) :
    homCongr R (stasheffObjOut_castSucc_of_le p X i (p.innerBoundary 0) h.le (by simp [h]))
      (stasheffObjOut_succ_of_ge p X i (p.innerBoundary (Fin.last p.s)) h.ge (by simp [h]))
      ((stasheffDegOut_of_eq deg p i h).trans hd) (stasheffInputsOut a p i) =
      stasheffInner a p d hd := by
  obtain rfl : i = p.middleIndex := Fin.ext h
  rw [stasheffInputsOut_middle, homCongr_homCongr]
  exact homCongr_stasheffInner p a _ _

end Positions

namespace AInfinityFunctorData

variable {β β' β'' : Type*} [AddCommGroup β] [Grading β] [AddCommGroup β'] [Grading β']
  [AddCommGroup β''] [Grading β''] {R : Type*} [Semiring R] {Obj Obj' Obj'' : Type*}

section Congruence

variable [GradedLinearQuiver β R Obj] [GradedLinearQuiver β' R Obj']
  (F : AInfinityFunctorData β β' R Obj Obj')

/-- Congruence for the components of A∞-functor data along an equality of arities, object
strings, degrees and inputs. -/
lemma map_v_congr {k k' : ℕ} [NeZero k] [NeZero k'] (e : k = k') {Y : Fin (k + 1) → Obj}
    {Y' : Fin (k' + 1) → Obj} (hY : ∀ i, Y i = Y' (i.cast (by rw [e]))) {δ : Fin k → β}
    {δ' : Fin k' → β} (hδ : ∀ i, δ i = δ' (i.cast e)) {j j' : β}
    (hj : functorTargetDeg δ = j) (hj' : functorTargetDeg δ' = j')
    {b : ∀ i, ComposableHom β R Y i (δ i)} {b' : ∀ i, ComposableHom β R Y' i (δ' i)}
    (hb : ∀ i, homCongr R (hY i.castSucc) (hY i.succ) (hδ i) (b i) = b' (i.cast e)) :
    homCongr R (congrArg F.obj ((hY 0).trans (congrArg Y' (Fin.cast_zero _))))
      (congrArg F.obj ((hY _).trans (congrArg Y' Fin.cast_last)))
      (congrArg F.degMap (hj.symm.trans ((functorTargetDeg_congr e hδ).trans hj')))
      ((F.map Y).v δ j hj b) = (F.map Y').v δ' j' hj' b' := by
  subst e
  obtain rfl : Y = Y' := funext hY
  obtain rfl : δ = δ' := funext hδ
  obtain rfl : b = b' := funext hb
  subst hj hj'
  rfl

/-- The values of `F` on two blocks of compositions, possibly of different composable strings,
agree as soon as the blocks have the same size, objects, degrees and inputs. -/
lemma compositionBlockMap_congr {n₁ n₂ : ℕ} {X₁ : Fin (n₁ + 1) → Obj} {X₂ : Fin (n₂ + 1) → Obj}
    {deg₁ : Fin n₁ → β} {deg₂ : Fin n₂ → β} (a₁ : ∀ i, ComposableHom β R X₁ i (deg₁ i))
    (a₂ : ∀ i, ComposableHom β R X₂ i (deg₂ i)) {c₁ : Composition n₁} {l₁ : Fin c₁.length}
    {c₂ : Composition n₂} {l₂ : Fin c₂.length} (e : c₁.blocksFun l₁ = c₂.blocksFun l₂)
    (hX : ∀ i, compositionBlockObj X₁ c₁ l₁ i = compositionBlockObj X₂ c₂ l₂ (i.cast (by rw [e])))
    (hdeg : ∀ i, deg₁ (c₁.embedding l₁ i) = deg₂ (c₂.embedding l₂ (i.cast e)))
    (ha : ∀ i, homCongr R (hX i.castSucc) (hX i.succ) (hdeg i) (a₁ (c₁.embedding l₁ i)) =
      a₂ (c₂.embedding l₂ (i.cast e))) :
    homCongr R (congrArg F.obj (by simpa using hX 0))
      (congrArg F.obj (by simpa using hX (Fin.last _)))
      (congrArg F.degMap (functorTargetDeg_congr e hdeg))
      (F.compositionBlockMap a₁ c₁ l₁) = F.compositionBlockMap a₂ c₂ l₂ := by
  rw [compositionBlockMap, compositionBlockMap, homCongr_homCongr]
  exact homCongr_eq_homCongr_of_eq (F.map_v_congr e hX hdeg rfl rfl ha)

variable {X : Fin (n + 1) → Obj} {deg : Fin n → β} (a : ∀ i : Fin n, ComposableHom β R X i (deg i))

/-- Two blocks of compositions of `n` in the same position and of the same size have the same
value under `F`. -/
lemma compositionBlockMap_congr_of_sizeUpTo_eq {c₁ c₂ : Composition n} {l₁ : Fin c₁.length}
    {l₂ : Fin c₂.length} (hs : c₁.sizeUpTo l₁ = c₂.sizeUpTo l₂)
    (e : c₁.blocksFun l₁ = c₂.blocksFun l₂) :
    homCongr R (congrArg (fun k ↦ F.obj (X k)) (Fin.ext (by simp [Composition.boundary, hs])))
      (congrArg (fun k ↦ F.obj (X k))
        (Fin.ext (by simp [Composition.boundary, Composition.sizeUpTo_succ', hs, e])))
      (congrArg F.degMap (functorTargetDeg_congr e fun i ↦
        congrArg deg (Composition.embedding_eq_of_sizeUpTo_eq hs e i)))
      (F.compositionBlockMap a c₁ l₁) = F.compositionBlockMap a c₂ l₂ :=
  F.compositionBlockMap_congr a a e (fun i ↦ congrArg X (Fin.ext (by simp [hs])))
    (fun i ↦ congrArg deg (Composition.embedding_eq_of_sizeUpTo_eq hs e i))
    (fun i ↦ homCongr_congrArg a (Composition.embedding_eq_of_sizeUpTo_eq hs e i))

/-- A block of a composition of `n` that lies inside the `j`-th block of another composition `c`
has the same value under `F` as the corresponding block of a composition of that block. -/
lemma compositionBlockMap_congr_compositionBlockMap_embedding {c₁ c : Composition n}
    {l₁ : Fin c₁.length} {j : Fin c.length} {c₂ : Composition (c.blocksFun j)}
    {l₂ : Fin c₂.length} (hs : c₁.sizeUpTo l₁ = c.sizeUpTo j + c₂.sizeUpTo l₂)
    (e : c₁.blocksFun l₁ = c₂.blocksFun l₂) :
    homCongr R (congrArg (fun k ↦ F.obj (X k))
        (Fin.ext (by simp [Composition.boundary, hs])))
      (congrArg (fun k ↦ F.obj (X k)) (Fin.ext (by
        simp [Composition.boundary, Composition.sizeUpTo_succ', hs, e, add_assoc])))
      (congrArg F.degMap (functorTargetDeg_congr e fun i ↦
        congrArg deg (Composition.embedding_eq_embedding_embedding hs e i)))
      (F.compositionBlockMap a c₁ l₁) =
      F.compositionBlockMap (X := compositionBlockObj X c j) (fun i ↦ a (c.embedding j i)) c₂ l₂ :=
  F.compositionBlockMap_congr (X₂ := compositionBlockObj X c j) a (fun i ↦ a (c.embedding j i))
    e (fun i ↦ congrArg X (Fin.ext (by simp [hs, add_assoc])))
    (fun i ↦ congrArg deg (Composition.embedding_eq_embedding_embedding hs e i))
    (fun i ↦ homCongr_congrArg a (Composition.embedding_eq_embedding_embedding hs e i))

end Congruence

end AInfinityFunctorData

end AInfinityTheory
