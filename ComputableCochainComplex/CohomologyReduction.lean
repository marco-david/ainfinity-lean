/-
Copyright (c) 2026 Annie Yao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Annie Yao
-/
module

public import ComputableCochainComplex.CohomologyKernel
public import Mathlib.Data.Matrix.Diagonal

/-!
# Finite checks for kernel and quotient coordinates

Reduction algorithms supply candidate matrices. The finite equations in `KernelData.Valid`
certify the entire kernel, including over integral domains where nonzero pivots need not be
units. `SplitPresentationData.Valid` certifies a free cokernel and an explicit boundary
preimage operator. Checking these equations uses only exact arithmetic and decidable equality.
Neither checker assumes the output of a reduction algorithm is correct.
-/

@[expose] public section

namespace ComputableCohomology

open scoped Matrix

variable {R : Type*} [CommRing R] {a b c : ℕ}

/-- Candidate kernel coordinates together with a complementary coordinate system.
Nonzero diagonal multiples of the complementary coordinates factor through the differential. -/
structure KernelData (R : Type*) (b c : ℕ) where
  /-- Number of kernel coordinates. -/
  size : ℕ
  /-- Number of complementary coordinates. -/
  complementSize : ℕ
  /-- Candidate kernel basis columns. -/
  inclusion : Matrix (Fin b) (Fin size) R
  /-- Candidate kernel coordinate rows. -/
  retraction : Matrix (Fin size) (Fin b) R
  /-- Complementary basis columns. -/
  complement : Matrix (Fin b) (Fin complementSize) R
  /-- Complementary coordinate rows. -/
  complementCoordinates : Matrix (Fin complementSize) (Fin b) R
  /-- Nonzero pivot multipliers; they need not be invertible. -/
  pivots : Fin complementSize → R
  /-- Rows expressing the pivot multiples through the outgoing differential. -/
  rows : Matrix (Fin complementSize) (Fin c) R

namespace KernelData

variable (data : KernelData R b c) (B : Matrix (Fin c) (Fin b) R)

/-- Finite algebraic checks proving that the candidate describes the entire kernel. -/
def Valid : Prop :=
  B * data.inclusion = 0 ∧
  data.retraction * data.inclusion = 1 ∧
  data.inclusion * data.retraction + data.complement * data.complementCoordinates = 1 ∧
  Matrix.diagonal data.pivots * data.complementCoordinates = data.rows * B ∧
  ∀ i, data.pivots i ≠ 0

instance [DecidableEq R] : Decidable (data.Valid B) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

variable [NoZeroDivisors R] (h : data.Valid B)

include h

lemma complementCoordinates_mulVec_eq_zero (x : Fin b → R) (hx : B *ᵥ x = 0) :
    data.complementCoordinates *ᵥ x = 0 := by
  have hp : Matrix.diagonal data.pivots *ᵥ (data.complementCoordinates *ᵥ x) = 0 := by
    rw [Matrix.mulVec_mulVec, h.2.2.2.1, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]
  ext i
  exact (mul_eq_zero.mp (by
    simpa only [Matrix.mulVec_diagonal, Pi.zero_apply] using congrFun hp i)).resolve_left
      (h.2.2.2.2 i)

/-- The finite checks imply completeness for every cocycle, not just tested vectors. -/
lemma inclusion_retraction (x : Fin b → R) (hx : B *ᵥ x = 0) :
    data.inclusion *ᵥ (data.retraction *ᵥ x) = x := by
  have hp := congrArg (fun M => M *ᵥ x) h.2.2.1
  simpa only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec,
    data.complementCoordinates_mulVec_eq_zero B h x hx, Matrix.mulVec_zero, add_zero,
    Matrix.one_mulVec] using hp

/-- Turn a successful finite check into the shared kernel certificate. -/
def certificate : KernelCertificate B where
  size := data.size
  inclusion := data.inclusion
  retraction := data.retraction
  mul_inclusion := h.1
  retraction_mul_inclusion := h.2.1
  inclusion_retraction := data.inclusion_retraction B h

/-- Check a candidate using exact arithmetic. Failure returns no mathematical claim. -/
def check [DecidableEq R] : Option (KernelCertificate B) :=
  if h : data.Valid B then some (data.certificate B h) else none

end KernelData

/-- Candidate free quotient coordinates for the cokernel of an incoming matrix. -/
structure SplitPresentationData (R : Type*) (a b : ℕ) where
  /-- Number of quotient coordinates. -/
  size : ℕ
  /-- Chosen representatives of the quotient basis. -/
  representatives : Matrix (Fin b) (Fin size) R
  /-- Class coordinates of a vector. -/
  normalize : Matrix (Fin size) (Fin b) R
  /-- Preimages of the boundary parts of vectors. -/
  preimage : Matrix (Fin a) (Fin b) R

namespace SplitPresentationData

variable (data : SplitPresentationData R a b) (W : Matrix (Fin b) (Fin a) R)

/-- Finite checks expressing a splitting of the quotient, including complete boundary witnesses. -/
def Valid : Prop :=
  data.normalize * W = 0 ∧
  data.normalize * data.representatives = 1 ∧
  W * data.preimage + data.representatives * data.normalize = 1

instance [DecidableEq R] : Decidable (data.Valid W) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

variable (h : data.Valid W)

include h

lemma normalize_boundary (x : Fin a → R) : data.normalize *ᵥ (W *ᵥ x) = 0 := by
  rw [Matrix.mulVec_mulVec, h.1, Matrix.zero_mulVec]

lemma normalize_representative (x : Fin data.size → R) :
    data.normalize *ᵥ (data.representatives *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, h.2.1, Matrix.one_mulVec]

/-- Every vector is its chosen representative plus an explicitly witnessed boundary. -/
lemma decompose (x : Fin b → R) :
    W *ᵥ (data.preimage *ᵥ x) + data.representatives *ᵥ (data.normalize *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, h.2.2,
    Matrix.one_mulVec]

/-- Vanishing coordinates are equivalent to being a boundary, with the supplied preimage. -/
lemma normalize_eq_zero_iff (x : Fin b → R) :
    data.normalize *ᵥ x = 0 ↔ W *ᵥ (data.preimage *ᵥ x) = x := by
  constructor
  · intro hx
    simpa [hx] using data.decompose W h x
  · intro hx
    rw [← hx]
    exact data.normalize_boundary W h _

/-- Class normalization is well-defined on the quotient by boundaries. -/
def quotientNormalize : ((Fin b → R) ⧸ LinearMap.range W.mulVecLin) →ₗ[R]
    (Fin data.size → R) :=
  (LinearMap.range W.mulVecLin).liftQ data.normalize.mulVecLin (by
    rintro _ ⟨x, rfl⟩
    exact data.normalize_boundary W h x)

@[simp] lemma quotientNormalize_mk (x : Fin b → R) :
    data.quotientNormalize W h (Submodule.Quotient.mk x) = data.normalize *ᵥ x := rfl

/-- The checked quotient coordinates give an executable linear equivalence. -/
def quotientEquiv : ((Fin b → R) ⧸ LinearMap.range W.mulVecLin) ≃ₗ[R]
    (Fin data.size → R) where
  toLinearMap := data.quotientNormalize W h
  invFun x := Submodule.Quotient.mk (data.representatives *ᵥ x)
  left_inv x := by
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      apply (Submodule.Quotient.eq _).mpr
      refine ⟨-(data.preimage *ᵥ x), ?_⟩
      change W *ᵥ (-(data.preimage *ᵥ x)) =
        data.representatives *ᵥ (data.normalize *ᵥ x) - x
      rw [Matrix.mulVec_neg, eq_sub_iff_add_eq]
      simpa using (congrArg (fun z => -(W *ᵥ (data.preimage *ᵥ x)) + z)
        (data.decompose W h x)).symm
  right_inv := data.normalize_representative W h

end SplitPresentationData

/-- Working matrices for exact row and column reduction. They are untrusted candidate data;
the kernel and quotient checkers validate every result used by a public calculator. -/
structure MatrixReductionData (R : Type*) (m n : ℕ) where
  /-- Number of pivots found so far. -/
  rank : ℕ
  /-- The matrix after the current row and column operations. -/
  reduced : Matrix (Fin m) (Fin n) R
  /-- Accumulated row operations. -/
  left : Matrix (Fin m) (Fin m) R
  /-- Inverse row operations. -/
  leftInverse : Matrix (Fin m) (Fin m) R
  /-- Accumulated column operations. -/
  right : Matrix (Fin n) (Fin n) R
  /-- Inverse column operations. -/
  rightInverse : Matrix (Fin n) (Fin n) R

namespace MatrixReductionData

variable {m n : ℕ}

/-- Start reduction in the original coordinates. -/
def initial (M : Matrix (Fin m) (Fin n) R) : MatrixReductionData R m n :=
  ⟨0, M, 1, 1, 1, 1⟩

/-- Swap two rows, updating the row transformation and its inverse. -/
def swapRows (s : MatrixReductionData R m n) (i j : Fin m) : MatrixReductionData R m n :=
  { s with
    reduced := s.reduced.submatrix (Equiv.swap i j) id
    left := s.left.submatrix (Equiv.swap i j) id
    leftInverse := s.leftInverse.submatrix id (Equiv.swap i j) }

/-- Swap two columns, updating the column transformation and its inverse. -/
def swapCols (s : MatrixReductionData R m n) (i j : Fin n) : MatrixReductionData R m n :=
  { s with
    reduced := s.reduced.submatrix id (Equiv.swap i j)
    right := s.right.submatrix id (Equiv.swap i j)
    rightInverse := s.rightInverse.submatrix (Equiv.swap i j) id }

/-- Scale a row, supplying the inverse scalar explicitly for the inverse transformation. -/
def scaleRow (s : MatrixReductionData R m n) (i : Fin m) (r rInv : R) :
    MatrixReductionData R m n :=
  { s with
    reduced := fun k j => if k = i then r * s.reduced k j else s.reduced k j
    left := fun k j => if k = i then r * s.left k j else s.left k j
    leftInverse := fun k j => if j = i then s.leftInverse k j * rInv else s.leftInverse k j }

/-- Add a multiple of one row to a distinct row and update the inverse transformation. -/
def addRow (s : MatrixReductionData R m n) (target source : Fin m) (r : R) :
    MatrixReductionData R m n :=
  { s with
    reduced := fun i j =>
      if i = target then s.reduced i j + r * s.reduced source j else s.reduced i j
    left := fun i j => if i = target then s.left i j + r * s.left source j else s.left i j
    leftInverse := fun i j =>
      if j = source then s.leftInverse i j - r * s.leftInverse i target else s.leftInverse i j }

/-- Add a multiple of one column to a distinct column and update the inverse transformation. -/
def addCol (s : MatrixReductionData R m n) (target source : Fin n) (r : R) :
    MatrixReductionData R m n :=
  { s with
    reduced := fun i j =>
      if j = target then s.reduced i j + r * s.reduced i source else s.reduced i j
    right := fun i j => if j = target then s.right i j + r * s.right i source else s.right i j
    rightInverse := fun i j =>
      if i = source then s.rightInverse i j - r * s.rightInverse target j else s.rightInverse i j }

/-- Extract candidate kernel coordinates from a diagonal reduction.
Out-of-range entries are zero; an invalid pivot count will be rejected by the checker. -/
def kernelData (s : MatrixReductionData R m n) : KernelData R n m where
  size := n - s.rank
  complementSize := s.rank
  inclusion i j := if h : s.rank + j.val < n then s.right i ⟨s.rank + j.val, h⟩ else 0
  retraction i j := if h : s.rank + i.val < n then s.rightInverse ⟨s.rank + i.val, h⟩ j else 0
  complement i j := if h : j.val < n then s.right i ⟨j.val, h⟩ else 0
  complementCoordinates i j := if h : i.val < n then s.rightInverse ⟨i.val, h⟩ j else 0
  pivots i := if hm : i.val < m then
    if hn : i.val < n then s.reduced ⟨i.val, hm⟩ ⟨i.val, hn⟩ else 0
    else 0
  rows i j := if h : i.val < m then s.left ⟨i.val, h⟩ j else 0

/-- Extract candidate free quotient coordinates when the nonzero pivots are all one. -/
def splitPresentationData (s : MatrixReductionData R m n) : SplitPresentationData R n m where
  size := m - s.rank
  representatives i j :=
    if h : s.rank + j.val < m then s.leftInverse i ⟨s.rank + j.val, h⟩ else 0
  normalize i j := if h : s.rank + i.val < m then s.left ⟨s.rank + i.val, h⟩ j else 0
  preimage := s.right *
    (Matrix.of fun (i : Fin n) (j : Fin m) =>
      if i.val = j.val ∧ i.val < s.rank then (1 : R) else 0) * s.left

end MatrixReductionData

end ComputableCohomology
