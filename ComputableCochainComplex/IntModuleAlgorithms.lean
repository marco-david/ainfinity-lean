/-
Copyright (c) 2026 Zhan Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhan Shi
-/
module

public import ComputableCochainComplex.ModuleAlgorithms
public import ComputableCochainComplex.SmithNormalForm

/-! # Effective module algorithms over the integers

This file provides `EffectiveModuleAlgorithms ℤ`, computing kernels and lifts of integer
matrices through their Smith normal forms.

Let `U * A * V = S` with `S` in Smith normal form of rank `r` (`Matrix.smithRank`).
* **Kernels.** `A x = 0` exactly when `⅟V x` vanishes in its first `r` coordinates, so the last
  columns of `V`, from index `r` on, form a basis of the kernel of `A`
  (`Matrix.SmithNormalForm.kernelGenerators`).
* **Lifts.** If `x` lies in the image of `A`, then the first `r` coordinates of `U x` are
  divisible by the invariant factors and the others vanish. Dividing gives `z` with `S z = U x`,
  and `V z` is a preimage of `x` (`Matrix.SmithNormalForm.liftVec`).
-/

@[expose] public section

open scoped Matrix

namespace Matrix

variable {m n : ℕ}

namespace TwoSidedTransform

variable {R : Type*} [CommRing R] {A : Matrix (Fin m) (Fin n) R} (t : TwoSidedTransform A)

theorem invOf_U_mulVec_mulVec (x : Fin m → R) : ⅟t.U *ᵥ (t.U *ᵥ x) = x := by
  rw [mulVec_mulVec, invOf_mul_self, one_mulVec]

theorem invOf_V_mulVec_mulVec (y : Fin n → R) : ⅟t.V *ᵥ (t.V *ᵥ y) = y := by
  rw [mulVec_mulVec, invOf_mul_self, one_mulVec]

theorem V_mulVec_invOf_mulVec (y : Fin n → R) : t.V *ᵥ (⅟t.V *ᵥ y) = y := by
  rw [mulVec_mulVec, mul_invOf_self, one_mulVec]

/-- In the new coordinates, `B` acts as `A` followed by `U`. -/
theorem B_mulVec_invOf_V (y : Fin n → R) : t.B *ᵥ (⅟t.V *ᵥ y) = t.U *ᵥ (A *ᵥ y) := by
  rw [mulVec_mulVec, mulVec_mulVec, ← t.mul_mul_eq, Matrix.mul_invOf_cancel_right]

/-- The kernel of `A` corresponds to the kernel of `B` under `⅟V`. -/
theorem mulVec_eq_zero_iff (y : Fin n → R) : A *ᵥ y = 0 ↔ t.B *ᵥ (⅟t.V *ᵥ y) = 0 := by
  rw [t.B_mulVec_invOf_V]
  refine ⟨fun h => by rw [h, mulVec_zero], fun h => ?_⟩
  rw [← t.invOf_U_mulVec_mulVec (A *ᵥ y), h, mulVec_zero]

/-- The image of `A` corresponds to the image of `B` under `U`. -/
theorem U_mulVec_mem_range {x : Fin m → R} (hx : x ∈ LinearMap.range A.mulVecLin) :
    t.U *ᵥ x ∈ LinearMap.range t.B.mulVecLin := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨⅟t.V *ᵥ y, t.B_mulVec_invOf_V y⟩

end TwoSidedTransform

/-- Divide the first `smithRank S` coordinates of `w` by the diagonal entries of `S`, and set
the remaining coordinates to zero. This solves `S z = w` when `S` is a Smith normal form and `w`
lies in its image. -/
def diagDiv {c b : ℕ} (S : Matrix (Fin c) (Fin b) ℤ) (w : Fin c → ℤ) : Fin b → ℤ := fun j =>
  if hj : j.val < smithRank S then
    w ⟨j, hj.trans_le (smithRank_le_left S)⟩ / S ⟨j, hj.trans_le (smithRank_le_left S)⟩ j
  else 0

/-- Dividing by the diagonal solves `S z = w` for `w` in the image of a Smith normal form. -/
theorem IsSmithNormalForm.mulVec_diagDiv {S : Matrix (Fin m) (Fin n) ℤ}
    (h : S.IsSmithNormalForm) {w : Fin m → ℤ} (hw : w ∈ LinearMap.range S.mulVecLin) :
    S *ᵥ diagDiv S w = w := by
  obtain ⟨v, rfl⟩ := hw
  ext i
  by_cases hi : i.val < smithRank S
  · have hin : i.val < n := hi.trans_le (smithRank_le_right S)
    have hne := h.apply_ne_zero_of_lt_smithRank (j := ⟨i, hin⟩) rfl hi
    simp only [mulVecLin_apply, h.mulVec_apply_of_lt _ i hin, diagDiv, hi, dite_true]
    rw [Int.mul_ediv_cancel_left _ hne]
  · simp only [mulVecLin_apply, h.mulVec_apply_of_smithRank_le _ (not_lt.mp hi)]

namespace SmithNormalForm

variable {A : Matrix (Fin m) (Fin n) ℤ} (s : A.SmithNormalForm)

/-- The coordinates from `smithRank s.B` on, where `s.B` vanishes. -/
def tailIndex (k : Fin (n - smithRank s.B)) : Fin n :=
  ⟨smithRank s.B + k, by have := smithRank_le_right s.B; omega⟩

/-- Place a vector into the coordinates from `smithRank s.B` on. -/
def tailExtend (z : Fin (n - smithRank s.B) → ℤ) : Fin n → ℤ :=
  (1 : Matrix (Fin n) (Fin n) ℤ).submatrix id s.tailIndex *ᵥ z

theorem submatrix_tailIndex_mulVec (z : Fin (n - smithRank s.B) → ℤ) :
    s.V.submatrix id s.tailIndex *ᵥ z = s.V *ᵥ s.tailExtend z := by
  rw [tailExtend, mulVec_mulVec, ← Equiv.coe_refl, mul_submatrix_one]
  rfl

theorem tailExtend_apply_of_lt (z : Fin (n - smithRank s.B) → ℤ) {j : Fin n}
    (hj : j.val < smithRank s.B) : s.tailExtend z j = 0 := by
  rw [tailExtend, mulVec, dotProduct]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [submatrix_apply, id_eq, one_apply_ne (fun e => by simp [tailIndex, Fin.ext_iff] at e; omega),
    zero_mul]

/-- A vector vanishing before `smithRank s.B` is the extension of its tail. -/
theorem tailExtend_comp_tailIndex {y : Fin n → ℤ}
    (hy : ∀ j : Fin n, j.val < smithRank s.B → y j = 0) : s.tailExtend (y ∘ s.tailIndex) = y := by
  ext j
  by_cases hj : j.val < smithRank s.B
  · rw [s.tailExtend_apply_of_lt _ hj, hy j hj]
  · have hk : j.val - smithRank s.B < n - smithRank s.B := by omega
    have hjk : s.tailIndex ⟨_, hk⟩ = j := Fin.ext (by simp [tailIndex]; omega)
    rw [tailExtend, mulVec, dotProduct, Finset.sum_eq_single ⟨_, hk⟩]
    · rw [submatrix_apply, id_eq, Function.comp_apply, hjk, one_apply_eq, one_mul]
    · intro k _ hk'
      rw [submatrix_apply, id_eq, one_apply_ne (fun e => hk' (Fin.ext (by
        simp [tailIndex, Fin.ext_iff] at e; simp; omega))), zero_mul]
    · simp

/-- The last columns of `V`, from index `smithRank B` on, form a basis of the kernel of `A`. -/
def kernelGenerators : KernelGenerators A where
  size := n - smithRank s.B
  generators := s.V.submatrix id s.tailIndex
  range_eq_ker := by
    ext x
    simp only [LinearMap.mem_range, LinearMap.mem_ker, mulVecLin_apply,
      s.toTwoSidedTransform.mulVec_eq_zero_iff, s.isSmithNormalForm.mulVec_eq_zero_iff]
    constructor
    · rintro ⟨z, rfl⟩ j hj
      rw [submatrix_tailIndex_mulVec, s.invOf_V_mulVec_mulVec]
      exact s.tailExtend_apply_of_lt z hj
    · intro hy
      refine ⟨(⅟s.V *ᵥ x) ∘ s.tailIndex, ?_⟩
      rw [submatrix_tailIndex_mulVec, tailExtend_comp_tailIndex _ hy, s.V_mulVec_invOf_mulVec]

/-- A preimage under `A` of a vector in its image: `V` applied to `U x` divided by the
invariant factors. -/
def liftVec (x : Fin m → ℤ) : Fin n → ℤ :=
  s.V *ᵥ diagDiv s.B (s.U *ᵥ x)

theorem mulVec_liftVec {x : Fin m → ℤ} (hx : x ∈ LinearMap.range A.mulVecLin) :
    A *ᵥ s.liftVec x = x := by
  rw [liftVec, mulVec_mulVec, s.mul_eq_invOf_mul, ← mulVec_mulVec,
    s.isSmithNormalForm.mulVec_diagDiv (s.U_mulVec_mem_range hx), s.invOf_U_mulVec_mulVec]

end SmithNormalForm

end Matrix

/-- Kernels and lifts of integer matrices, computed from Smith normal forms. The kernel
generators are the last columns of `V` and form a basis; lifting divides by the invariant
factors. -/
instance Int.instEffectiveModuleAlgorithms : EffectiveModuleAlgorithms ℤ where
  syzygies B := B.smithNormalForm.kernelGenerators
  lift A x hx := ⟨A.smithNormalForm.liftVec x, A.smithNormalForm.mulVec_liftVec hx⟩
