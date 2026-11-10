/-
Copyright (c) 2026 Annie Yao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Annie Yao
-/
module

public import ComputableCochainComplex.CohomologySmith

/-!
# Exact integral row and column reduction

Euclidean pivot reduction retains all integer coordinate transformations and their inverses.
Recursive calls check a strictly decreasing absolute pivot, so no user-supplied fuel is needed.
The returned matrices remain candidate data: the kernel and Smith presentation checkers are
required before any cohomology result is used. A failure of the descent guard is explicit;
a universal theorem that this generator always passes every check is not asserted here.
-/

@[expose] public section

namespace ComputableCohomology

open scoped Matrix

namespace MatrixReductionData

variable {m n : ℕ}

/-- Clear a pivot column and row by Euclidean division. Return a smaller pivot on the left,
or a completed pivot dividing the whole remaining block on the right. -/
def smithPivotStep (row : Fin m) (col : Fin n) (s : MatrixReductionData ℤ m n) :
    MatrixReductionData ℤ m n ⊕ MatrixReductionData ℤ m n := Id.run do
  let mut t := s
  for i in List.finRange m do
    if row.val < i.val then
      t := t.addRow i row (-(t.reduced i col / t.reduced row col))
  match (List.finRange m).find? (fun i => row.val < i.val && t.reduced i col != 0) with
  | some i => return .inl (t.swapRows row i)
  | none => pure ()
  for j in List.finRange n do
    if col.val < j.val then
      t := t.addCol j col (-(t.reduced row j / t.reduced row col))
  match (List.finRange n).find? (fun j => col.val < j.val && t.reduced row j != 0) with
  | some j => return .inl (t.swapCols col j)
  | none => pure ()
  match ((List.finRange m).product (List.finRange n)).find? (fun ij =>
      decide (row.val < ij.1.val ∧ col.val < ij.2.val ∧
        ¬ t.reduced row col ∣ t.reduced ij.1 ij.2)) with
  | none => return .inr t
  | some (i, j) =>
    t := t.addRow row i 1
    t := t.addCol j col (-(t.reduced row j / t.reduced row col))
    return .inl (t.swapCols col j)

/-- Repeated Euclidean reduction, with a checked strictly decreasing absolute pivot.
The guard makes termination independent of unproved invariants of the candidate generator. -/
def smithPivot (row : Fin m) (col : Fin n) (s : MatrixReductionData ℤ m n) :
    Except String (MatrixReductionData ℤ m n) :=
  match s.smithPivotStep row col with
  | .inr t => .ok t
  | .inl t =>
    if _h : (t.reduced row col).natAbs < (s.reduced row col).natAbs then
      smithPivot row col t
    else .error "integer reduction: pivot descent check failed"
termination_by (s.reduced row col).natAbs

/-- Extract diagonal relation-module witnesses from two-sided integral reduction. -/
def smithPresentationData (s : MatrixReductionData ℤ m n) : SmithPresentationData n m where
  diagonal i := if h : i.val < n then (s.reduced i ⟨i.val, h⟩).natAbs else 0
  coordinates := s.left
  representatives := s.leftInverse
  relations i j := if h : i.val < n then s.rightInverse ⟨i.val, h⟩ j else 0
  preimages i j := if h : j.val < n then s.right i ⟨j.val, h⟩ else 0

end MatrixReductionData

/-- Total exact integer reduction with Euclidean pivot descent and nonnegative pivots.
Every output must still pass the kernel or normalized presentation checker. -/
def integerReduce {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℤ) :
    Except String (MatrixReductionData ℤ m n) := do
  let mut s := MatrixReductionData.initial M
  for k in List.finRange (min m n) do
    let pivot := ((List.finRange m).product (List.finRange n)).find? fun ij =>
      decide (k.val ≤ ij.1.val ∧ k.val ≤ ij.2.val ∧ s.reduced ij.1 ij.2 ≠ 0)
    match pivot with
    | none => return s
    | some (i, j) =>
      let row : Fin m := ⟨k.val, lt_of_lt_of_le k.isLt (Nat.min_le_left m n)⟩
      let col : Fin n := ⟨k.val, lt_of_lt_of_le k.isLt (Nat.min_le_right m n)⟩
      s := (s.swapRows row i).swapCols col j
      s ← s.smithPivot row col
      if s.reduced row col < 0 then s := s.scaleRow row (-1) (-1)
      s := { s with rank := k.val + 1 }
  return s

end ComputableCohomology
