/-
Copyright (c) 2026 Annie Yao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Annie Yao, Marco David, Zhan Shi
-/
module

public import AInfinity.AInfinityCategoryStruct
public import AInfinity.StasheffIndex

/-! # The Stasheff identities

Given a graded `R`-linear quiver with higher compositions
mₙ : Hom(X₀, X₁) ⊗ ⋯ ⊗ Hom(Xₙ₋₁, Xₙ) → Hom(X₀, Xₙ) of degree 2 - n, the arity-n Stasheff
identity states that
$$\sum_{r + s + t = n,\ s \ge 1} (-1)^{\|a_{r+s+1}\| + \dots + \|a_n\|}
  m_{r+1+t}(a_1, \dots, a_r, m_s(a_{r+1}, \dots, a_{r+s}), a_{r+s+1}, \dots, a_n) = 0,$$
where ‖a‖ = |a| - 1 is the reduced degree.

The index triples (r, s, t), the object strings `stasheffObjIn`/`stasheffObjOut` and the input
degrees `stasheffDegIn`/`stasheffDegOut` of the inner and outer operations, and the Koszul signs
are in `AInfinity.StasheffIndex`.

## Main definitions

* `AInfinityTheory.stasheffInputsIn`, `AInfinityTheory.stasheffInputsOut`: the inputs of the
  inner and of the outer operation of the (r, s, t) summand.
* `AInfinityTheory.stasheffInner`, `AInfinityTheory.stasheffOuter`: the inner output and the
  outer value of the (r, s, t) summand.
* `AInfinityTheory.stasheffTerm`: the (r, s, t) summand of the Stasheff sum.
* `AInfinityTheory.stasheffSum`: the signed Stasheff sum in arity n.

## Main results

* `AInfinityTheory.stasheffTerm_eq_zero_of_arity_notMem`: if `m` vanishes in every arity
  outside `S`, a Stasheff term vanishes unless both its inner and its outer arity lie in `S`.
* `AInfinityTheory.stasheffSum_eq_zero_of_arity_notMem`: the corresponding vanishing of the
  Stasheff sum, when every index triple has an arity outside `S`.
* `AInfinityTheory.stasheffSum_arity_one`, `AInfinityTheory.stasheffSum_arity_two`,
  `AInfinityTheory.stasheffSum_arity_three`: the Stasheff sums in arities 1, 2 and 3,
  written out term by term.
-/

@[expose] public section

namespace AInfinityTheory

universe u v w

open GradedLinearQuiver
open AInfinityCategoryStruct (m)

variable {β : Type v} [AddCommGroup β] [Grading β]
variable {R : Type u} [CommRing R] {Obj : Type w} [AInfinityCategoryStruct β R Obj]
variable {n : ℕ} {X : Fin (n + 1) → Obj} {deg : Fin n → β}
variable (a : ∀ i : Fin n, ComposableHom β R X i (deg i)) (p : StasheffIndex n)

/-- The inputs of the inner operation mₛ of the (r, s, t) summand: the s inputs after the
first r, as morphisms between the objects of the inner operation. -/
def stasheffInputsIn :
    ∀ j : Fin p.s, ComposableHom β R (stasheffObjIn X p) j (stasheffDegIn deg p j) :=
  fun j ↦ a (p.innerEmb j)

@[simp]
lemma stasheffInputsIn_apply (j : Fin p.s) : stasheffInputsIn a p j = a (p.innerEmb j) :=
  rfl

/-- The inner output of the (r, s, t) summand, mₛ applied to the s inputs after the first r,
in any degree `d` equal to its degree `stasheffInnerDeg deg p`. -/
def stasheffInner (d : β) (hd : stasheffInnerDeg deg p = d) :
    (stasheffObjIn X p 0 →ᵍ[R] stasheffObjIn X p (Fin.last p.s)) d :=
  (m (stasheffObjIn X p)).v (stasheffDegIn deg p) d hd (stasheffInputsIn a p)

/-- The inputs of the outer operation of the (r, s, t) summand: the first r inputs, then the
inner output, then the last t inputs, each transported to the hom space between the
corresponding objects of the outer operation. -/
def stasheffInputsOut :
    ∀ i : Fin (p.r + 1 + p.t), ComposableHom β R (stasheffObjOut X p) i (stasheffDegOut deg p i) :=
  Fin.addCases
    (Fin.snoc
      (fun j ↦ homCongr R (stasheffObjOut_left_castSucc X p j).symm
        (stasheffObjOut_left_succ X p j).symm (stasheffDegOut_left deg p j).symm (a (p.leftEmb j)))
      (homCongr R (stasheffObjOut_middle_castSucc X p).symm (stasheffObjOut_middle_succ X p).symm
        rfl (stasheffInner a p _ (stasheffDegOut_middle deg p).symm)))
    fun k ↦ homCongr R (stasheffObjOut_right_castSucc X p k).symm
      (stasheffObjOut_right_succ X p k).symm (stasheffDegOut_right deg p k).symm (a (p.rightEmb k))

@[simp]
lemma stasheffInputsOut_left (j : Fin p.r) :
    stasheffInputsOut a p (j.castSucc.castAdd p.t) =
      homCongr R (stasheffObjOut_left_castSucc X p j).symm (stasheffObjOut_left_succ X p j).symm
        (stasheffDegOut_left deg p j).symm (a (p.leftEmb j)) := by
  simp [stasheffInputsOut]

@[simp]
lemma stasheffInputsOut_right (k : Fin p.t) :
    stasheffInputsOut a p (k.natAdd (p.r + 1)) =
      homCongr R (stasheffObjOut_right_castSucc X p k).symm (stasheffObjOut_right_succ X p k).symm
        (stasheffDegOut_right deg p k).symm (a (p.rightEmb k)) := by
  simp [stasheffInputsOut]

@[simp]
lemma stasheffInputsOut_middle :
    stasheffInputsOut a p p.middleIndex =
      homCongr R (stasheffObjOut_middle_castSucc X p).symm (stasheffObjOut_middle_succ X p).symm
        rfl (stasheffInner a p _ (stasheffDegOut_middle deg p).symm) := by
  simp [stasheffInputsOut]

lemma stasheffInputsOut_middle_eq_zero_of_inner_eq_zero
    (hinner : ∀ d hd, stasheffInner a p d hd = 0) :
    stasheffInputsOut a p p.middleIndex = 0 := by
  rw [stasheffInputsOut_middle, hinner, map_zero]

/-- The outer value of the (r, s, t) summand: the operation of arity r + 1 + t applied to
`stasheffInputsOut a p`, in any degree `d` equal to its degree. -/
def stasheffOuter (d : β) (hd : operationTargetDeg (stasheffDegOut deg p) = d) :
    (stasheffObjOut X p 0 →ᵍ[R] stasheffObjOut X p (Fin.last (p.r + 1 + p.t))) d :=
  (m (stasheffObjOut X p)).v (stasheffDegOut deg p) d hd (stasheffInputsOut a p)

/-- The (r, s, t) summand of the Stasheff sum, without its Koszul sign: the outer value
`stasheffOuter`, transported to the hom space from `X 0` to `X (Fin.last n)`, in any degree `d`
equal to the Stasheff target degree. -/
def stasheffTerm (d : β) (hd : stasheffTargetDeg deg = d) : (X 0 →ᵍ[R] X (Fin.last n)) d :=
  homCongr R (stasheffObjOut_zero X p) (stasheffObjOut_last X p) rfl
    (stasheffOuter a p d ((stasheffDegOut_sum deg p).trans hd))

lemma stasheffInner_eq_zero_of_map_eq_zero
    (hm : ∀ d hd, (m (R := R) (stasheffObjIn X p)).v (stasheffDegIn deg p) d hd = 0)
    (d : β) (hd : stasheffInnerDeg deg p = d) :
    stasheffInner a p d hd = 0 := by
  simp [stasheffInner, hm d hd]

lemma stasheffOuter_eq_zero_of_map_eq_zero
    (hm : ∀ d hd, (m (R := R) (stasheffObjOut X p)).v (stasheffDegOut deg p) d hd = 0)
    (d : β) (hd : operationTargetDeg (stasheffDegOut deg p) = d) :
    stasheffOuter a p d hd = 0 := by
  rw [stasheffOuter, hm, zero_apply]

lemma stasheffOuter_eq_zero_of_inner_eq_zero
    (hinner : ∀ d hd, stasheffInner a p d hd = 0)
    (d : β) (hd : operationTargetDeg (stasheffDegOut deg p) = d) :
    stasheffOuter a p d hd = 0 :=
  MultilinearMap.map_coord_zero ((m (stasheffObjOut X p)).v (stasheffDegOut deg p) d hd)
    p.middleIndex (stasheffInputsOut_middle_eq_zero_of_inner_eq_zero a p hinner)

lemma stasheffTerm_eq_zero_iff_outer_eq_zero (d : β) (hd : stasheffTargetDeg deg = d) :
    stasheffTerm a p d hd = 0 ↔
      stasheffOuter a p d ((stasheffDegOut_sum deg p).trans hd) = 0 :=
  (homCongr R (stasheffObjOut_zero X p) (stasheffObjOut_last X p) rfl).map_eq_zero_iff

lemma stasheffTerm_eq_zero_of_outer_map_eq_zero
    (hm : ∀ d hd, (m (R := R) (stasheffObjOut X p)).v (stasheffDegOut deg p) d hd = 0)
    (d : β) (hd : stasheffTargetDeg deg = d) :
    stasheffTerm a p d hd = 0 :=
  (stasheffTerm_eq_zero_iff_outer_eq_zero a p d hd).2
    (stasheffOuter_eq_zero_of_map_eq_zero a p hm _ _)

lemma stasheffTerm_eq_zero_of_inner_map_eq_zero
    (hm : ∀ d hd, (m (R := R) (stasheffObjIn X p)).v (stasheffDegIn deg p) d hd = 0)
    (d : β) (hd : stasheffTargetDeg deg = d) :
    stasheffTerm a p d hd = 0 :=
  (stasheffTerm_eq_zero_iff_outer_eq_zero a p d hd).2
    (stasheffOuter_eq_zero_of_inner_eq_zero a p
      (stasheffInner_eq_zero_of_map_eq_zero a p hm) _ _)

/-- The full Stasheff sum in arity n, with Koszul signs, in any degree `d` equal to the
Stasheff target degree. -/
def stasheffSum (d : β) (hd : stasheffTargetDeg deg = d) : (X 0 →ᵍ[R] X (Fin.last n)) d :=
  signedStasheffSum deg fun q => stasheffTerm a q d hd

/-- If `m` vanishes in every arity outside `S`, a Stasheff term vanishes unless both its
inner and its outer arity lie in `S`. -/
lemma stasheffTerm_eq_zero_of_arity_notMem (S : Set ℕ)
    (hm : ∀ (k : ℕ) [NeZero k], k ∉ S → ∀ X : Fin (k + 1) → Obj, m (β := β) (R := R) X = 0)
    {n : ℕ} {X : Fin (n + 1) → Obj} {deg : Fin n → β}
    (a : ∀ i : Fin n, ComposableHom β R X i (deg i)) (p : StasheffIndex n)
    (hS : p.s ∉ S ∨ p.r + 1 + p.t ∉ S) (d : β) (hd : stasheffTargetDeg deg = d) :
    stasheffTerm a p d hd = 0 := by
  rcases hS with hS | hS
  · exact stasheffTerm_eq_zero_of_inner_map_eq_zero a p
      (fun d hd => by simp only [hm p.s hS]; rfl) d hd
  · exact stasheffTerm_eq_zero_of_outer_map_eq_zero a p
      (fun d hd => by simp only [hm _ hS]; rfl) d hd

/-- If `m` vanishes in every arity outside `S`, the arity-n Stasheff sum vanishes as soon as
every index triple has its inner or its outer arity outside `S`. -/
lemma stasheffSum_eq_zero_of_arity_notMem (S : Set ℕ)
    (hm : ∀ (k : ℕ) [NeZero k], k ∉ S → ∀ X : Fin (k + 1) → Obj, m (β := β) (R := R) X = 0)
    {n : ℕ} {X : Fin (n + 1) → Obj} {deg : Fin n → β}
    (hS : ∀ p : StasheffIndex n, p.s ∉ S ∨ p.r + 1 + p.t ∉ S)
    (a : ∀ i : Fin n, ComposableHom β R X i (deg i)) (d : β) (hd : stasheffTargetDeg deg = d) :
    stasheffSum a d hd = 0 :=
  signedStasheffSum_eq_zero fun p => stasheffTerm_eq_zero_of_arity_notMem S hm a p (hS p) d hd

/-- In arity 1, the Stasheff sum is the single term m₁(m₁(a₁)). -/
lemma stasheffSum_arity_one {X : Fin (1 + 1) → Obj} {deg : Fin 1 → β}
    (a : ∀ i : Fin 1, ComposableHom β R X i (deg i)) (d : β) (hd : stasheffTargetDeg deg = d) :
    stasheffSum a d hd = stasheffTerm a ⟨0, 1, 0, rfl, le_rfl⟩ d hd := by
  rw [stasheffSum, signedStasheffSum, StasheffIndex.univ_one, Finset.sum_singleton]
  exact one_smul _ _

/-- In arity 2, the Stasheff sum has the three terms m₂(m₁(a₁), a₂),
m₂(a₁, m₁(a₂)) and m₁(m₂(a₁, a₂)), with the Koszul sign (-1)^‖a₂‖ on the
first. -/
lemma stasheffSum_arity_two {X : Fin (2 + 1) → Obj} {deg : Fin 2 → β}
    (a : ∀ i : Fin 2, ComposableHom β R X i (deg i)) (d : β) (hd : stasheffTargetDeg deg = d) :
    stasheffSum a d hd =
      (sign (deg 1 - degOne)).toMul • stasheffTerm a ⟨0, 1, 1, rfl, le_rfl⟩ d hd +
        stasheffTerm a ⟨1, 1, 0, rfl, le_rfl⟩ d hd +
        stasheffTerm a ⟨0, 2, 0, rfl, one_le_two⟩ d hd := by
  rw [stasheffSum, signedStasheffSum, StasheffIndex.univ_two, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [stasheffSign, Fin.prod_univ_one, Fin.prod_univ_zero, one_smul, add_assoc]
  rfl

/-- In arity 3, the Stasheff sum has six terms, one for each index triple (r, s, t), with
the Koszul signs given by `stasheffSign`. -/
lemma stasheffSum_arity_three {X : Fin (3 + 1) → Obj} {deg : Fin 3 → β}
    (a : ∀ i : Fin 3, ComposableHom β R X i (deg i)) (d : β) (hd : stasheffTargetDeg deg = d) :
    stasheffSum a d hd =
      ((sign (deg 1 - degOne)).toMul * (sign (deg 2 - degOne)).toMul) •
          stasheffTerm a ⟨0, 1, 2, rfl, le_rfl⟩ d hd +
        (sign (deg 2 - degOne)).toMul • stasheffTerm a ⟨1, 1, 1, rfl, le_rfl⟩ d hd +
        stasheffTerm a ⟨2, 1, 0, rfl, le_rfl⟩ d hd +
        (sign (deg 2 - degOne)).toMul • stasheffTerm a ⟨0, 2, 1, rfl, one_le_two⟩ d hd +
        stasheffTerm a ⟨1, 2, 0, rfl, one_le_two⟩ d hd +
        stasheffTerm a ⟨0, 3, 0, rfl, by decide⟩ d hd := by
  rw [stasheffSum, signedStasheffSum, StasheffIndex.univ_three]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp only [stasheffSign, Fin.prod_univ_two, Fin.prod_univ_one, Fin.prod_univ_zero,
    one_smul, add_assoc]
  rfl

end AInfinityTheory
