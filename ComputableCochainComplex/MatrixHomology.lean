/-
Copyright (c) 2026 Annie Yao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Annie Yao
-/
module

public import Mathlib.LinearAlgebra.Matrix.Transvection
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!+# Certified finite matrix cohomology dimensions

Exact elimination uses executable finite pivot searches and mathlib's transvections.
The algorithm returns finite transformation data; independent certificate theorems relate
these data to matrix rank and the existing kernel/range quotient. This module is independent
of `CMat_`, bounded categorical complexes, and KLRW.
-/

@[expose] public section

namespace MatrixHomology

open Matrix Matrix.TransvectionStruct Sum

variable {k : Type*} [Field k] [DecidableEq k]

/-- Finite data witnessing a diagonalization by invertible row and column operations. -/
structure Diagonalization (ι : Type*) (k : Type*) where
  /-- Row operations, applied by multiplying their matrices on the left. -/
  left : List (TransvectionStruct ι k)
  /-- Column operations, applied by multiplying their matrices on the right. -/
  right : List (TransvectionStruct ι k)
  /-- The resulting diagonal entries. -/
  diagonal : ι → k

namespace Diagonalization

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The certificate equation, separated from the procedure producing its finite data. -/
def Valid (a : Diagonalization ι k) (M : Matrix ι ι k) : Prop :=
  (a.left.map toMatrix).prod * M * (a.right.map toMatrix).prod = Matrix.diagonal a.diagonal

/-- Counting nonzero diagonal entries computes rank whenever the certificate equation holds. -/
theorem rank_eq (a : Diagonalization ι k) {M : Matrix ι ι k} (h : a.Valid M) :
    M.rank = Fintype.card {i // a.diagonal i ≠ 0} := by
  have hl : IsUnit (a.left.map toMatrix).prod.det := by simp
  have hr : IsUnit (a.right.map toMatrix).prod.det := by simp
  rw [← Matrix.rank_diagonal, ← h,
    Matrix.rank_mul_eq_left_of_isUnit_det _ _ hr,
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ hl]

end Diagonalization

section Pivot

variable {r : ℕ}

/-- Clear the last column and row using their common nonzero diagonal entry. -/
def clearPivot (M : Matrix (Fin r ⊕ Unit) (Fin r ⊕ Unit) k) :
    List (TransvectionStruct (Fin r ⊕ Unit) k) ×
      List (TransvectionStruct (Fin r ⊕ Unit) k) :=
  (List.ofFn fun i : Fin r =>
    ⟨inl i, inr (), by simp, -M (inl i) (inr ()) / M (inr ()) (inr ())⟩,
   List.ofFn fun i : Fin r =>
    ⟨inr (), inl i, by simp, -M (inr ()) (inl i) / M (inr ()) (inr ())⟩)

omit [DecidableEq k] in
/-- Mathlib's pivot proof certifies the explicit clearing operations. -/
theorem clearPivot_valid (M : Matrix (Fin r ⊕ Unit) (Fin r ⊕ Unit) k)
    (h : M (inr ()) (inr ()) ≠ 0) :
    IsTwoBlockDiagonal (((clearPivot M).1.map toMatrix).prod * M *
      ((clearPivot M).2.map toMatrix).prod) := by
  simpa [clearPivot, Matrix.Pivot.listTransvecCol, Matrix.Pivot.listTransvecRow] using
    Matrix.Pivot.isTwoBlockDiagonal_listTransvecCol_mul_mul_listTransvecRow M h

/-- Select a pivot by ascending finite search, preferring the last column to the last row. -/
def pivotStep (M : Matrix (Fin r ⊕ Unit) (Fin r ⊕ Unit) k) :
    List (TransvectionStruct (Fin r ⊕ Unit) k) ×
      List (TransvectionStruct (Fin r ⊕ Unit) k) :=
  if M (inr ()) (inr ()) ≠ 0 then clearPivot M
  else
    match (List.finRange r).find? (fun i => M (inl i) (inr ()) ≠ 0) with
    | some i =>
      let t : TransvectionStruct (Fin r ⊕ Unit) k := ⟨inr (), inl i, by simp, 1⟩
      let q := clearPivot (t.toMatrix * M)
      (q.1 ++ [t], q.2)
    | none =>
      match (List.finRange r).find? (fun i => M (inr ()) (inl i) ≠ 0) with
      | some i =>
        let t : TransvectionStruct (Fin r ⊕ Unit) k := ⟨inl i, inr (), by simp, 1⟩
        let q := clearPivot (M * t.toMatrix)
        (q.1, t :: q.2)
      | none => ([], [])

omit [DecidableEq k] in
private theorem pivotStep_column (M : Matrix (Fin r ⊕ Unit) (Fin r ⊕ Unit) k)
    (h : M (inr ()) (inr ()) = 0) (i : Fin r) (hi : M (inl i) (inr ()) ≠ 0) :
    let t : TransvectionStruct (Fin r ⊕ Unit) k := ⟨inr (), inl i, by simp, 1⟩
    let q := clearPivot (t.toMatrix * M)
    IsTwoBlockDiagonal (((q.1 ++ [t]).map toMatrix).prod * M *
      (q.2.map toMatrix).prod) := by
  let t : TransvectionStruct (Fin r ⊕ Unit) k := ⟨inr (), inl i, by simp, 1⟩
  let q := clearPivot (t.toMatrix * M)
  change IsTwoBlockDiagonal (((q.1 ++ [t]).map toMatrix).prod * M *
    (q.2.map toMatrix).prod)
  have hp : (t.toMatrix * M) (inr ()) (inr ()) ≠ 0 := by simpa [t, h] using hi
  have hq := clearPivot_valid (t.toMatrix * M) hp
  change IsTwoBlockDiagonal ((q.1.map toMatrix).prod * (t.toMatrix * M) *
    (q.2.map toMatrix).prod) at hq
  simpa only [List.map_append, List.prod_append, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, Matrix.mul_one, Matrix.mul_assoc] using hq

omit [DecidableEq k] in
private theorem pivotStep_row (M : Matrix (Fin r ⊕ Unit) (Fin r ⊕ Unit) k)
    (h : M (inr ()) (inr ()) = 0) (i : Fin r) (hi : M (inr ()) (inl i) ≠ 0) :
    let t : TransvectionStruct (Fin r ⊕ Unit) k := ⟨inl i, inr (), by simp, 1⟩
    let q := clearPivot (M * t.toMatrix)
    IsTwoBlockDiagonal ((q.1.map toMatrix).prod * M *
      ((t :: q.2).map toMatrix).prod) := by
  let t : TransvectionStruct (Fin r ⊕ Unit) k := ⟨inl i, inr (), by simp, 1⟩
  let q := clearPivot (M * t.toMatrix)
  change IsTwoBlockDiagonal ((q.1.map toMatrix).prod * M *
    ((t :: q.2).map toMatrix).prod)
  have hp : (M * t.toMatrix) (inr ()) (inr ()) ≠ 0 := by simpa [t, h] using hi
  have hq := clearPivot_valid (M * t.toMatrix) hp
  change IsTwoBlockDiagonal ((q.1.map toMatrix).prod * (M * t.toMatrix) *
    (q.2.map toMatrix).prod) at hq
  simpa only [List.map_cons, List.prod_cons, Matrix.mul_assoc] using hq

/-- Each pivot step isolates the last row and column, including when both searches fail. -/
theorem pivotStep_valid (M : Matrix (Fin r ⊕ Unit) (Fin r ⊕ Unit) k) :
    IsTwoBlockDiagonal (((pivotStep M).1.map toMatrix).prod * M *
      ((pivotStep M).2.map toMatrix).prod) := by
  unfold pivotStep
  split_ifs with h
  · exact clearPivot_valid M h
  · have hz : M (inr ()) (inr ()) = 0 := not_not.mp h
    split <;> rename_i hc
    · rename_i i
      exact pivotStep_column M hz i (by simpa using List.find?_some hc)
    · split <;> rename_i hr
      · rename_i i
        exact pivotStep_row M hz i (by simpa using List.find?_some hr)
      · simp only [List.map_nil, List.prod_nil, Matrix.one_mul, Matrix.mul_one]
        constructor
        · ext i j
          cases j
          simpa using (List.find?_eq_none.mp hc i (by simp))
        · ext i j
          cases i
          simpa using (List.find?_eq_none.mp hr j (by simp))

end Pivot

namespace Diagonalization

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]

/-- Transport the finite transformation data along an explicit indexing equivalence. -/
def reindex (a : Diagonalization ι k) (e : ι ≃ κ) : Diagonalization κ k where
  left := a.left.map (reindexEquiv e)
  right := a.right.map (reindexEquiv e)
  diagonal := a.diagonal ∘ e.symm

omit [DecidableEq k] in
/-- Reindexing preserves the diagonalization certificate. -/
theorem reindex_valid [Fintype ι] [Fintype κ] (a : Diagonalization ι k)
    (e : ι ≃ κ) {M : Matrix ι ι k} (h : a.Valid M) :
    (a.reindex e).Valid (M.reindex e e) := by
  dsimp only [Valid, reindex]
  simp only [List.map_map, toMatrix_reindexEquiv_prod]
  change reindexAlgEquiv k _ e _ * reindexAlgEquiv k _ e M *
    reindexAlgEquiv k _ e _ = _
  rw [← reindexAlgEquiv_mul, ← reindexAlgEquiv_mul, h]
  simp only [reindexAlgEquiv_apply, reindex_apply, submatrix_diagonal_equiv]

end Diagonalization

/-- Split off the last finite index using only explicit finite equivalences. -/
def lastIndexEquiv (r : ℕ) : Fin (r + 1) ≃ Fin r ⊕ Unit :=
  finSumFinEquiv.symm.trans (Equiv.sumCongr (Equiv.refl _) (Equiv.ofUnique _ _))

/-- The matrix remaining after one certified pivot step. -/
def pivotMatrix {r : ℕ} (M : Matrix (Fin r ⊕ Unit) (Fin r ⊕ Unit) k) :
    Matrix (Fin r ⊕ Unit) (Fin r ⊕ Unit) k :=
  ((pivotStep M).1.map toMatrix).prod * M * ((pivotStep M).2.map toMatrix).prod

/-- Combine a diagonalization of the smaller block with the last pivot step. -/
def finishStep {r : ℕ} (M : Matrix (Fin r ⊕ Unit) (Fin r ⊕ Unit) k)
    (a : Diagonalization (Fin r) k) : Diagonalization (Fin r ⊕ Unit) k where
  left := a.left.map (sumInl Unit) ++ (pivotStep M).1
  right := (pivotStep M).2 ++ a.right.map (sumInl Unit)
  diagonal := Sum.elim a.diagonal (fun _ => pivotMatrix M (inr ()) (inr ()))

/-- The block induction step for the certificate proof. -/
theorem finishStep_valid {r : ℕ} (M : Matrix (Fin r ⊕ Unit) (Fin r ⊕ Unit) k)
    (a : Diagonalization (Fin r) k) (h : a.Valid (pivotMatrix M).toBlocks₁₁) :
    (finishStep M a).Valid M := by
  have hb := pivotStep_valid M
  change IsTwoBlockDiagonal (pivotMatrix M) at hb
  have he : pivotMatrix M = fromBlocks (pivotMatrix M).toBlocks₁₁ 0 0
      (Matrix.diagonal fun _ : Unit => pivotMatrix M (inr ()) (inr ())) := by
    rw [← fromBlocks_toBlocks (pivotMatrix M), hb.1, hb.2]
    rfl
  suffices (a.left.map (toMatrix ∘ sumInl Unit)).prod * pivotMatrix M *
      (a.right.map (toMatrix ∘ sumInl Unit)).prod =
      Matrix.diagonal (Sum.elim a.diagonal (fun _ => pivotMatrix M (inr ()) (inr ()))) by
    simpa only [Diagonalization.Valid, finishStep, pivotMatrix, List.map_append,
      List.prod_append, List.map_map, Matrix.mul_assoc] using this
  conv_lhs => rw [he]
  simpa only [sumInl_toMatrix_prod_mul, mul_sumInl_toMatrix_prod, h,
    fromBlocks_diagonal] using congrArg
      (fun N => fromBlocks N 0 0
        (Matrix.diagonal fun _ : Unit => pivotMatrix M (inr ()) (inr ()))) h

/-- Exact diagonalization, terminating by recursion on the square matrix size. -/
def diagonalize : (n : ℕ) → Matrix (Fin n) (Fin n) k → Diagonalization (Fin n) k
  | 0, _ => ⟨[], [], Fin.elim0⟩
  | r + 1, M =>
    let e := lastIndexEquiv r
    let N := M.reindex e e
    (finishStep N (diagonalize r (pivotMatrix N).toBlocks₁₁)).reindex e.symm

/-- Every matrix produced by the recursive procedure satisfies its certificate equation. -/
theorem diagonalize_valid (n : ℕ) (M : Matrix (Fin n) (Fin n) k) :
    (diagonalize n M).Valid M := by
  induction n with
  | zero => ext i; exact Fin.elim0 i
  | succ r ih =>
    let e := lastIndexEquiv r
    let N := M.reindex e e
    have h := (finishStep N (diagonalize r (pivotMatrix N).toBlocks₁₁)).reindex_valid
      e.symm (finishStep_valid N _ (ih _))
    change (diagonalize (r + 1) M).Valid ((M.reindex e e).reindex e.symm e.symm) at h
    simpa only [reindex_apply, submatrix_submatrix, Equiv.symm_comp_self,
      Equiv.symm_symm, submatrix_id_id] using h

section Rectangular

variable {m n : ℕ}

/-- Pad a rectangular matrix with zero rows and columns to size `max m n`.
The two identity submatrices are the coordinate inclusion and projection. -/
def pad (M : Matrix (Fin m) (Fin n) k) : Matrix (Fin (max m n)) (Fin (max m n)) k :=
  (1 : Matrix (Fin (max m n)) (Fin (max m n)) k).submatrix id
      (Fin.castLE (Nat.le_max_left m n)) * M *
    (1 : Matrix (Fin (max m n)) (Fin (max m n)) k).submatrix
      (Fin.castLE (Nat.le_max_right m n)) id

omit [DecidableEq k] in
/-- Extracting the original rows and columns of the padded matrix recovers the input. -/
theorem pad_submatrix (M : Matrix (Fin m) (Fin n) k) :
    (pad M).submatrix (Fin.castLE (Nat.le_max_left m n))
      (Fin.castLE (Nat.le_max_right m n)) = M := by
  unfold pad
  rw [submatrix_mul _ _ _ id _ Function.bijective_id,
    submatrix_mul _ _ _ id _ Function.bijective_id]
  simp only [submatrix_submatrix, Function.comp_id, Function.id_comp, submatrix_id_id,
    submatrix_one _ (Fin.castLE_injective _), Matrix.one_mul, Matrix.mul_one]

omit [DecidableEq k] in
/-- Padding preserves rank: it factors through the input, and the input is a submatrix. -/
theorem rank_pad (M : Matrix (Fin m) (Fin n) k) : (pad M).rank = M.rank := by
  apply le_antisymm
  · exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  · have h := Matrix.rank_submatrix_le (pad M) (Fin.castLE (Nat.le_max_left m n))
      (Fin.castLE (Nat.le_max_right m n))
    rwa [pad_submatrix] at h

/-- Executable rank, obtained by exact elimination rather than a chosen abstract basis. -/
def computeRank (M : Matrix (Fin m) (Fin n) k) : ℕ :=
  Fintype.card {i // (diagonalize (max m n) (pad M)).diagonal i ≠ 0}

/-- The automatically computed rank agrees with mathlib's rank. -/
theorem computeRank_eq_rank (M : Matrix (Fin m) (Fin n) k) : computeRank M = M.rank := by
  rw [computeRank, ← Diagonalization.rank_eq _ (diagonalize_valid _ _), rank_pad]

end Rectangular

section Cohomology

open CategoryTheory Module

omit [DecidableEq k] in
/-- The existing module homology quotient has the usual dimension, with no new quotient type. -/
theorem finrank_homology (S : ShortComplex (ModuleCat k)) [FiniteDimensional k S.X₂] :
    finrank k S.homology = finrank k S.X₂ -
      finrank k (LinearMap.range S.f.hom) - finrank k (LinearMap.range S.g.hom) := by
  have hr := Submodule.finrank_map_subtype_eq (LinearMap.ker S.g.hom)
    (LinearMap.range S.moduleCatToCycles)
  rw [← LinearMap.range_comp] at hr
  have hf : (LinearMap.ker S.g.hom).subtype.comp S.moduleCatToCycles = S.f.hom := rfl
  rw [hf] at hr
  have hn := S.g.hom.finrank_range_add_finrank_ker
  rw [S.moduleCatHomologyIso.toLinearEquiv.finrank_eq]
  change finrank k (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) = _
  rw [Submodule.finrank_quotient, ← hr]
  omega

variable {a m c : ℕ}

/-- The short complex of coordinate modules attached to two square-zero matrices. -/
def shortComplex (F : Matrix (Fin m) (Fin a) k) (G : Matrix (Fin c) (Fin m) k)
    (h : G * F = 0) : ShortComplex (ModuleCat k) :=
  ShortComplex.moduleCatMk F.mulVecLin G.mulVecLin (by
    rw [← Matrix.mulVecLin_mul, h, Matrix.mulVecLin_zero])

/-- Executable cohomology dimension of a three-term matrix complex. -/
def cohomologyDimension (F : Matrix (Fin m) (Fin a) k)
    (G : Matrix (Fin c) (Fin m) k) : ℕ := m - computeRank F - computeRank G

/-- The rank-sum bound ensures the dimension formula does not hide an invalid subtraction. -/
theorem computeRank_add_le (F : Matrix (Fin m) (Fin a) k)
    (G : Matrix (Fin c) (Fin m) k) (h : G * F = 0) :
    computeRank F + computeRank G ≤ m := by
  simpa [computeRank_eq_rank, Nat.add_comm] using Matrix.rank_add_rank_le_card_of_mul_eq_zero h

/-- The computed number is the dimension of the existing abstract module homology. -/
theorem cohomologyDimension_eq_finrank (F : Matrix (Fin m) (Fin a) k)
    (G : Matrix (Fin c) (Fin m) k) (h : G * F = 0) :
    cohomologyDimension F G = finrank k (shortComplex F G h).homology := by
  haveI : FiniteDimensional k (shortComplex F G h).X₂ :=
    inferInstanceAs (FiniteDimensional k (Fin m → k))
  rw [finrank_homology]
  change cohomologyDimension F G = finrank k (Fin m → k) - F.rank - G.rank
  simp [cohomologyDimension, computeRank_eq_rank]

end Cohomology

end MatrixHomology
