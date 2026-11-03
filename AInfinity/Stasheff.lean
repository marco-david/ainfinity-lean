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
`mₙ : Hom(X₀, X₁) ⊗ ⋯ ⊗ Hom(Xₙ₋₁, Xₙ) → Hom(X₀, Xₙ)` of degree `2 - n`, the arity-`n` Stasheff
identity states that
`∑_{r + s + t = n, s ≥ 1} (-1)^(‖a_{r+s+1}‖ + ⋯ + ‖aₙ‖) m_{r+1+t}(a₁, …, aᵣ,
mₛ(a_{r+1}, …, a_{r+s}), a_{r+s+1}, …, aₙ) = 0`.

The index triples `(r, s, t)`, the degree and object bookkeeping attached to them and the Koszul
signs are in `AInfinity.StasheffIndex`.

## Main definitions

* `AInfinityTheory.stasheffTerm`: the `(r, s, t)` summand of the Stasheff sum.
* `AInfinityTheory.stasheffSum`: the signed Stasheff sum in arity `n`.

## Main results

* `AInfinityTheory.stasheffTerm_eq_zero_of_arity_notMem`: if `m` vanishes in every arity
  outside `S`, a Stasheff term vanishes unless both its inner and its outer arity lie in `S`.
* `AInfinityTheory.stasheffSum_eq_zero_of_arity_notMem`: the corresponding vanishing of the
  Stasheff sum, when every index triple has an arity outside `S`.
* `AInfinityTheory.stasheffSum_arity_one`, `AInfinityTheory.stasheffSum_arity_two`,
  `AInfinityTheory.stasheffSum_arity_three`: the Stasheff sums in arities `1`, `2` and `3`,
  written out term by term.
-/

@[expose] public section

namespace AInfinityTheory

universe u v w

variable {β : Type v} [AddCommGroup β] [Grading β]
variable {n : ℕ}

open GradedLinearQuiver

variable {R : Type u} [CommRing R] {Obj : Type w}
variable (X : Fin (n + 1) → Obj) (deg : Fin n → β)

section GradedLinearQuiver

variable [GradedLinearQuiver β R Obj]
variable (x : ∀ i : Fin n, ComposableHom β R X i (deg i))
variable (p : StasheffIndex n)

/-! From here on, `X` and `deg` are inferred from the inputs `x`; declarations that do not take
`x` bind them explicitly. -/

variable {X deg}

/-- Helper: the input tuple for the inner operation in a Stasheff term. -/
def stasheffInputsIn :
    ∀ j : Fin p.s, ComposableHom β R (stasheffObjIn X p) j (stasheffDegIn deg p j) :=
  fun j => x (((j.natAdd p.r).castAdd p.t).cast p.sum_eq)

omit [AddCommGroup β] [Grading β] in
/-- Evaluating the inner input tuple just picks out the corresponding original input. -/
@[simp]
lemma stasheffInputsIn_apply
    (j : Fin p.s) :
    stasheffInputsIn x p j = x (((j.natAdd p.r).castAdd p.t).cast p.sum_eq) :=
  rfl

/-- Helper: the middle index in the outer tuple of a Stasheff term. -/
abbrev stasheffMiddleIndex : Fin (p.r + 1 + p.t) :=
  (Fin.last p.r).castAdd p.t

variable (R X deg) in
/-- Before the inserted block, the space of an original input is identified with the
corresponding outer input space. -/
def stasheffInputsOutEquivLeft
    (j : Fin p.r) :
    ComposableHom β R X (((j.castAdd p.s).castAdd p.t).cast p.sum_eq)
        (deg (((j.castAdd p.s).castAdd p.t).cast p.sum_eq)) ≃ₗ[R]
      ComposableHom β R (stasheffObjOut X p) (j.castSucc.castAdd p.t)
        (stasheffDegOut deg p (j.castSucc.castAdd p.t)) :=
  homCongr R (stasheffObjOut_left X p j.castSucc).symm
    (stasheffObjOut_left X p j.succ).symm (stasheffDegOut_left deg p j).symm

variable (R X) in
/-- At the inserted block, the space of the inner output is identified with the outer middle
input space, in any degree `d`. -/
def stasheffInputsOutEquivMiddle
    (d : β) :
    (stasheffObjIn X p 0 →ᵍ[R] stasheffObjIn X p (Fin.last p.s)) d ≃ₗ[R]
      ComposableHom β R (stasheffObjOut X p) (stasheffMiddleIndex p) d :=
  homCongr R (stasheffObjOut_left X p (Fin.last p.r)).symm
    (stasheffObjOut_right X p 0).symm rfl

variable (R X deg) in
/-- After the inserted block, the space of an original input is identified with the
corresponding outer input space. -/
def stasheffInputsOutEquivRight
    (k : Fin p.t) :
    ComposableHom β R X ((k.natAdd (p.r + p.s)).cast p.sum_eq)
        (deg ((k.natAdd (p.r + p.s)).cast p.sum_eq)) ≃ₗ[R]
      ComposableHom β R (stasheffObjOut X p) (k.natAdd (p.r + 1))
        (stasheffDegOut deg p (k.natAdd (p.r + 1))) :=
  homCongr R (stasheffObjOut_right X p k.castSucc).symm
    (stasheffObjOut_right X p k.succ).symm (stasheffDegOut_right deg p k).symm

variable (R X) in
/-- Helper: the identification of the outer target space with the final Stasheff target space,
in any degree `d`. -/
def stasheffTargetEquiv
    (d : β) :
    (stasheffObjOut X p 0 →ᵍ[R] stasheffObjOut X p (Fin.last (p.r + 1 + p.t))) d
      ≃ₗ[R] (X 0 →ᵍ[R] X (Fin.last n)) d :=
  homCongr R (stasheffObjOut_zero X p) (stasheffObjOut_last X p) rfl

end GradedLinearQuiver

section AInfinityCategoryStruct

open AInfinityCategoryStruct (m)

variable [AInfinityCategoryStruct β R Obj]
variable (x : ∀ i : Fin n, ComposableHom β R X i (deg i))
variable (p : StasheffIndex n)
variable {X deg}

/-- Rewriting the degree function and transporting each input does not change the value of `m`. -/
lemma m_homCongr_deg
    [NeZero n]
    {deg deg' : Fin n → β}
    (hdeg : deg = deg')
    (x : ∀ i : Fin n, ComposableHom β R X i (deg i))
    {d : β}
    (hd : operationTargetDeg deg = d)
    (hd' : operationTargetDeg deg' = d) :
    (m X).v deg' d hd' (fun i => homCongr R rfl rfl (congrFun hdeg i) (x i)) =
      (m X).v deg d hd x := by
  subst hdeg
  rfl

/-- Helper: the inner value appearing in a Stasheff term, in any degree `d` equal to the
inner degree. -/
def stasheffInner
    (d : β)
    (hd : stasheffInnerDeg deg p = d) :
    (stasheffObjIn X p 0 →ᵍ[R] stasheffObjIn X p (Fin.last p.s)) d :=
  (m (stasheffObjIn X p)).v (stasheffDegIn deg p) d hd (stasheffInputsIn x p)

/-- Helper: the input tuple for the outer operation in a Stasheff term: the first `r` inputs,
then the inner output, then the last `t` inputs. -/
def stasheffInputsOut :
    ∀ a : Fin (p.r + 1 + p.t),
      ComposableHom β R (stasheffObjOut X p) a (stasheffDegOut deg p a) :=
  Fin.addCases
    (Fin.snoc
      (fun j => stasheffInputsOutEquivLeft R X deg p j
        (x (((j.castAdd p.s).castAdd p.t).cast p.sum_eq)))
      (stasheffInputsOutEquivMiddle R X p _
        (stasheffInner x p _ (stasheffDegOut_middle deg p).symm)))
    (fun k => stasheffInputsOutEquivRight R X deg p k
      (x ((k.natAdd (p.r + p.s)).cast p.sum_eq)))

/-- Before the inserted block, the outer input tuple agrees with the original inputs. -/
@[simp]
lemma stasheffInputsOut_left
    (j : Fin p.r) :
    stasheffInputsOut x p (j.castSucc.castAdd p.t) =
      stasheffInputsOutEquivLeft R X deg p j
        (x (((j.castAdd p.s).castAdd p.t).cast p.sum_eq)) := by
  simp [stasheffInputsOut]

/-- After the inserted block, the outer input tuple agrees with the original inputs. -/
@[simp]
lemma stasheffInputsOut_right
    (k : Fin p.t) :
    stasheffInputsOut x p (k.natAdd (p.r + 1)) =
      stasheffInputsOutEquivRight R X deg p k (x ((k.natAdd (p.r + p.s)).cast p.sum_eq)) := by
  simp [stasheffInputsOut]

/-- The middle outer input is the transported inner output. -/
@[simp]
lemma stasheffInputsOut_middle :
    stasheffInputsOut x p (stasheffMiddleIndex p) =
      stasheffInputsOutEquivMiddle R X p _
        (stasheffInner x p _ (stasheffDegOut_middle deg p).symm) := by
  simp [stasheffInputsOut]

/-- The middle outer input vanishes whenever the inner output vanishes. -/
lemma stasheffInputsOut_middle_eq_zero_of_inner_eq_zero
    (hinner : ∀ d hd, stasheffInner x p d hd = 0) :
    stasheffInputsOut x p (stasheffMiddleIndex p) = 0 := by
  rw [stasheffInputsOut_middle, hinner, map_zero]

/-- Helper: the outer value appearing in a Stasheff term, in any degree `d` equal to the
degree of the outer operation. -/
def stasheffOuter
    (d : β)
    (hd : operationTargetDeg (stasheffDegOut deg p) = d) :
    (stasheffObjOut X p 0 →ᵍ[R] stasheffObjOut X p (Fin.last (p.r + 1 + p.t))) d :=
  (m (stasheffObjOut X p)).v (stasheffDegOut deg p) d hd (stasheffInputsOut x p)

/-- A generic Stasheff term builder for object-indexed A∞ operations, in any degree `d` equal
to the Stasheff target degree. -/
def stasheffTerm
    (d : β)
    (hd : stasheffTargetDeg deg = d) :
    (X 0 →ᵍ[R] X (Fin.last n)) d :=
  stasheffTargetEquiv R X p d
    (stasheffOuter x p d ((stasheffDegOut_sum deg p).trans hd))

/-- The inner value vanishes if the inner multilinear map itself vanishes. -/
lemma stasheffInner_eq_zero_of_map_eq_zero
    (hm : ∀ d hd, (m (R := R) (stasheffObjIn X p)).v (stasheffDegIn deg p) d hd = 0)
    (d : β)
    (hd : stasheffInnerDeg deg p = d) :
    stasheffInner x p d hd = 0 := by
  simp [stasheffInner, hm]

/-- The outer value vanishes if the outer multilinear map itself vanishes. -/
lemma stasheffOuter_eq_zero_of_map_eq_zero
    (hm : ∀ d hd, (m (R := R) (stasheffObjOut X p)).v (stasheffDegOut deg p) d hd = 0)
    (d : β)
    (hd : operationTargetDeg (stasheffDegOut deg p) = d) :
    stasheffOuter x p d hd = 0 := by
  rw [stasheffOuter, hm, MultilinearMap.zero_apply]

/-- The outer value vanishes whenever the inserted inner output vanishes. -/
lemma stasheffOuter_eq_zero_of_inner_eq_zero
    (hinner : ∀ d hd, stasheffInner x p d hd = 0)
    (d : β)
    (hd : operationTargetDeg (stasheffDegOut deg p) = d) :
    stasheffOuter x p d hd = 0 :=
  MultilinearMap.map_coord_zero ((m (stasheffObjOut X p)).v (stasheffDegOut deg p) d hd)
    (stasheffMiddleIndex p)
    (stasheffInputsOut_middle_eq_zero_of_inner_eq_zero x p hinner)

/-- The final transported Stasheff term vanishes exactly when the outer value vanishes. -/
lemma stasheffTerm_eq_zero_iff_outer_eq_zero
    (d : β)
    (hd : stasheffTargetDeg deg = d) :
    stasheffTerm x p d hd = 0 ↔
      stasheffOuter x p d ((stasheffDegOut_sum deg p).trans hd) = 0 :=
  (stasheffTargetEquiv R X p d).map_eq_zero_iff

/-- The final Stasheff term vanishes if the outer multilinear map vanishes. -/
lemma stasheffTerm_eq_zero_of_outer_map_eq_zero
    (hm : ∀ d hd, (m (R := R) (stasheffObjOut X p)).v (stasheffDegOut deg p) d hd = 0)
    (d : β)
    (hd : stasheffTargetDeg deg = d) :
    stasheffTerm x p d hd = 0 :=
  (stasheffTerm_eq_zero_iff_outer_eq_zero x p d hd).2
    (stasheffOuter_eq_zero_of_map_eq_zero x p hm _ _)

/-- The final Stasheff term vanishes if the inner multilinear map vanishes. -/
lemma stasheffTerm_eq_zero_of_inner_map_eq_zero
    (hm : ∀ d hd, (m (R := R) (stasheffObjIn X p)).v (stasheffDegIn deg p) d hd = 0)
    (d : β)
    (hd : stasheffTargetDeg deg = d) :
    stasheffTerm x p d hd = 0 :=
  (stasheffTerm_eq_zero_iff_outer_eq_zero x p d hd).2
    (stasheffOuter_eq_zero_of_inner_eq_zero x p
      (stasheffInner_eq_zero_of_map_eq_zero x p hm) _ _)

/-- The full Stasheff sum in arity `n`, with Koszul signs, in any degree `d` equal to the
Stasheff target degree. -/
def stasheffSum
    (d : β)
    (hd : stasheffTargetDeg deg = d) :
    (X 0 →ᵍ[R] X (Fin.last n)) d :=
  signedStasheffSum deg fun q => stasheffTerm x q d hd

/-- If `m` vanishes in every arity outside `S`, a Stasheff term vanishes unless both its
inner and its outer arity lie in `S`. -/
lemma stasheffTerm_eq_zero_of_arity_notMem (S : Set ℕ)
    (hm : ∀ (k : ℕ) [NeZero k], k ∉ S → ∀ X : Fin (k + 1) → Obj, m (β := β) (R := R) X = 0)
    {n : ℕ} {X : Fin (n + 1) → Obj} {deg : Fin n → β}
    (x : ∀ i : Fin n, ComposableHom β R X i (deg i)) (p : StasheffIndex n)
    (hS : p.s ∉ S ∨ p.r + 1 + p.t ∉ S) (d : β) (hd : stasheffTargetDeg deg = d) :
    stasheffTerm x p d hd = 0 := by
  rcases hS with hS | hS
  · exact stasheffTerm_eq_zero_of_inner_map_eq_zero x p
      (fun d hd => by simp only [hm p.s hS]; rfl) d hd
  · exact stasheffTerm_eq_zero_of_outer_map_eq_zero x p
      (fun d hd => by simp only [hm _ hS]; rfl) d hd

/-- If `m` vanishes in every arity outside `S`, the arity-`n` Stasheff sum vanishes as soon as
every index triple has its inner or its outer arity outside `S`. -/
lemma stasheffSum_eq_zero_of_arity_notMem (S : Set ℕ)
    (hm : ∀ (k : ℕ) [NeZero k], k ∉ S → ∀ X : Fin (k + 1) → Obj, m (β := β) (R := R) X = 0)
    {n : ℕ} {X : Fin (n + 1) → Obj} {deg : Fin n → β}
    (hS : ∀ p : StasheffIndex n, p.s ∉ S ∨ p.r + 1 + p.t ∉ S)
    (x : ∀ i : Fin n, ComposableHom β R X i (deg i)) (d : β) (hd : stasheffTargetDeg deg = d) :
    stasheffSum x d hd = 0 :=
  signedStasheffSum_eq_zero fun p => stasheffTerm_eq_zero_of_arity_notMem S hm x p (hS p) d hd

/-- In arity `1`, the Stasheff sum is the single term `m₁(m₁(a₁))`. -/
lemma stasheffSum_arity_one {X : Fin (1 + 1) → Obj} {deg : Fin 1 → β}
    (x : ∀ i : Fin 1, ComposableHom β R X i (deg i)) (d : β) (hd : stasheffTargetDeg deg = d) :
    stasheffSum x d hd = stasheffTerm x ⟨0, 1, 0, rfl, le_rfl⟩ d hd := by
  rw [stasheffSum, signedStasheffSum, StasheffIndex.univ_one, Finset.sum_singleton]
  exact one_smul _ _

/-- In arity `2`, the Stasheff sum has the three terms `m₂(m₁(a₁), a₂)`, `m₂(a₁, m₁(a₂))` and
`m₁(m₂(a₁, a₂))`, with the Koszul sign `(-1)^‖a₂‖` on the first. -/
lemma stasheffSum_arity_two {X : Fin (2 + 1) → Obj} {deg : Fin 2 → β}
    (x : ∀ i : Fin 2, ComposableHom β R X i (deg i)) (d : β) (hd : stasheffTargetDeg deg = d) :
    stasheffSum x d hd =
      (sign (deg 1 - shift 1)).toMul • stasheffTerm x ⟨0, 1, 1, rfl, le_rfl⟩ d hd +
        stasheffTerm x ⟨1, 1, 0, rfl, le_rfl⟩ d hd +
        stasheffTerm x ⟨0, 2, 0, rfl, one_le_two⟩ d hd := by
  rw [stasheffSum, signedStasheffSum, StasheffIndex.univ_two, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [stasheffSign, Fin.prod_univ_one, Fin.prod_univ_zero, one_smul, add_assoc]
  rfl

/-- In arity `3`, the Stasheff sum has six terms, one for each index triple `(r, s, t)`, with
the Koszul signs `(-1)^(‖a_{r+s+1}‖ + ⋯ + ‖a₃‖)`. -/
lemma stasheffSum_arity_three {X : Fin (3 + 1) → Obj} {deg : Fin 3 → β}
    (x : ∀ i : Fin 3, ComposableHom β R X i (deg i)) (d : β) (hd : stasheffTargetDeg deg = d) :
    stasheffSum x d hd =
      ((sign (deg 1 - shift 1)).toMul * (sign (deg 2 - shift 1)).toMul) •
          stasheffTerm x ⟨0, 1, 2, rfl, le_rfl⟩ d hd +
        (sign (deg 2 - shift 1)).toMul • stasheffTerm x ⟨1, 1, 1, rfl, le_rfl⟩ d hd +
        stasheffTerm x ⟨2, 1, 0, rfl, le_rfl⟩ d hd +
        (sign (deg 2 - shift 1)).toMul • stasheffTerm x ⟨0, 2, 1, rfl, one_le_two⟩ d hd +
        stasheffTerm x ⟨1, 2, 0, rfl, one_le_two⟩ d hd +
        stasheffTerm x ⟨0, 3, 0, rfl, by decide⟩ d hd := by
  rw [stasheffSum, signedStasheffSum, StasheffIndex.univ_three]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp only [stasheffSign, Fin.prod_univ_two, Fin.prod_univ_one, Fin.prod_univ_zero,
    one_smul, add_assoc]
  rfl

end AInfinityCategoryStruct

end AInfinityTheory
