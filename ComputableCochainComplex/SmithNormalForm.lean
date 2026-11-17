/-
Copyright (c) 2026 Zhan Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhan Shi
-/
module

public import Mathlib.Algebra.GCDMonoid.Nat
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.LinearAlgebra.Matrix.Swap
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.LinearAlgebra.Matrix.Transvection
public import Mathlib.LinearAlgebra.StdBasis

/-! # Smith normal form of integer matrices

For an integer matrix `A : Matrix (Fin m) (Fin n) ℤ`, `Matrix.smithNormalForm A` computes
invertible matrices `U` and `V`, together with their inverses, and a matrix `B` in Smith
normal form such that `U * A * V = B`.

Equivalently, it computes bases of the source and the target on which `A` acts diagonally:
the columns `vⱼ = V.col j` form a basis of `Fin n → ℤ`, the columns `uᵢ = (⅟U).col i` form a
basis of `Fin m → ℤ`, and `A *ᵥ vₖ = B k k • uₖ`, where `B 0 0 ∣ B 1 1 ∣ ⋯` are the invariant
factors (`SmithNormalForm.mulVec_col_of_val_eq`). All matrices are computable; Mathlib's
`Module.Basis` packaging (`TwoSidedTransform.sourceBasis`, `TwoSidedTransform.targetBasis`) is
not, since `Module.Basis` is built on `Finsupp`.

## Main definitions

* `Matrix.IsSmithNormalForm`: the recursive Smith normal form predicate.
* `Matrix.TwoSidedTransform A`: a two-sided change of bases `U * A * V = B` with explicit
  inverses of `U` and `V`.
* `Matrix.SmithNormalForm A`: a two-sided change of bases whose result is in Smith normal form.
* `Matrix.smithNormalForm`: the algorithm for integer matrices.

## Implementation notes

The design is adapted from the verified Smith normal form in
[lean-normal-forms](https://github.com/JJYYY-JJY/lean-normal-forms) by Junye Ji
(Apache 2.0): the recursive predicate `IsSmithNormalFormFin`, the composable two-sided
transforms with inverse certificates, pivot stabilization by a strictly decreasing measure,
and the recursion on the lower-right block. Here the Bézout reductions over a general
Euclidean domain are replaced by Euclidean remainder steps over `ℤ`, decreasing the absolute
value of the pivot.

Matrices are functions, so iterated products would recompute their entries exponentially
often; `TwoSidedTransform.trans` therefore stores its results as `ofTable (memoTable M)`.
The table is a `Vector`, not a function, so the compiler evaluates it once, before the
matrix closure is built; a function returning a matrix would instead be eta-expanded and
rebuild its table for every entry.
-/

@[expose] public section

open scoped Matrix

namespace Matrix

variable {m n k : ℕ}

section Memoize

variable {α : Type*}

/-- The entries of a matrix, evaluated once and stored row by row. -/
def memoTable (M : Matrix (Fin m) (Fin n) α) : Vector (Vector α n) m :=
  Vector.ofFn fun i => Vector.ofFn (M i)

/-- The matrix whose entries are read off a stored table. -/
def ofTable (rows : Vector (Vector α n) m) : Matrix (Fin m) (Fin n) α :=
  of fun i j => rows[i][j]

/-- Storing the entries of a matrix and reading them back gives the same matrix. -/
@[simp]
theorem ofTable_memoTable (M : Matrix (Fin m) (Fin n) α) : ofTable (memoTable M) = M := by
  ext i j
  simp [ofTable, memoTable]

end Memoize

section DiagCons

variable {α : Type*}

/-- The block-diagonal matrix with corner entry `a` and lower-right block `M`. -/
def diagCons [Zero α] (a : α) (M : Matrix (Fin m) (Fin n) α) :
    Matrix (Fin (m + 1)) (Fin (n + 1)) α :=
  of fun i j => Fin.cases (Fin.cases a (fun _ => 0) j) (fun i => Fin.cases 0 (M i) j) i

variable [Zero α] (a : α) (M : Matrix (Fin m) (Fin n) α)

@[simp] theorem diagCons_zero_zero : diagCons a M 0 0 = a := rfl

@[simp] theorem diagCons_zero_succ (j : Fin n) : diagCons a M 0 j.succ = 0 := rfl

@[simp] theorem diagCons_succ_zero (i : Fin m) : diagCons a M i.succ 0 = 0 := rfl

@[simp] theorem diagCons_succ_succ (i : Fin m) (j : Fin n) :
    diagCons a M i.succ j.succ = M i j := rfl

@[simp] theorem submatrix_succ_succ_diagCons :
    (diagCons a M).submatrix Fin.succ Fin.succ = M := rfl

/-- A matrix with zero first row and column is block diagonal. -/
theorem eq_diagCons {B : Matrix (Fin (m + 1)) (Fin (n + 1)) α}
    (row : ∀ j : Fin n, B 0 j.succ = 0) (col : ∀ i : Fin m, B i.succ 0 = 0) :
    B = diagCons (B 0 0) (B.submatrix Fin.succ Fin.succ) := by
  ext i j
  cases i using Fin.cases <;> cases j using Fin.cases <;> simp [row, col]

end DiagCons

section DiagConsMul

variable {α : Type*} [Semiring α]

theorem diagCons_mul_diagCons (a b : α) (M : Matrix (Fin m) (Fin k) α)
    (N : Matrix (Fin k) (Fin n) α) : diagCons a M * diagCons b N = diagCons (a * b) (M * N) := by
  ext i j
  cases i using Fin.cases <;> cases j using Fin.cases <;> simp [mul_apply, Fin.sum_univ_succ]

@[simp]
theorem diagCons_one_one : diagCons (1 : α) (1 : Matrix (Fin m) (Fin m) α) = 1 := by
  ext i j
  cases i using Fin.cases <;> cases j using Fin.cases <;>
    simp [one_apply, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm]

/-- `diagCons 1 M` is invertible when `M` is, with inverse `diagCons 1 ⅟M`. -/
instance invertibleDiagCons (M : Matrix (Fin m) (Fin m) α) [Invertible M] :
    Invertible (diagCons 1 M) where
  invOf := diagCons 1 (⅟M)
  invOf_mul_self := by rw [diagCons_mul_diagCons, one_mul, invOf_mul_self, diagCons_one_one]
  mul_invOf_self := by rw [diagCons_mul_diagCons, one_mul, mul_invOf_self, diagCons_one_one]

theorem diagCons_one_mul_mul_diagCons_one {B : Matrix (Fin (m + 1)) (Fin (n + 1)) α}
    (row : ∀ j : Fin n, B 0 j.succ = 0) (col : ∀ i : Fin m, B i.succ 0 = 0)
    (U : Matrix (Fin m) (Fin m) α) (V : Matrix (Fin n) (Fin n) α) :
    diagCons 1 U * B * diagCons 1 V = diagCons (B 0 0) (U * B.submatrix Fin.succ Fin.succ * V) := by
  rw [eq_diagCons row col, diagCons_mul_diagCons, diagCons_mul_diagCons, one_mul, mul_one]
  rfl

end DiagConsMul

/-- A common divisor of all entries of `L` divides all entries of `X * L * Y`. -/
theorem dvd_mul_mul_apply {α : Type*} [CommSemiring α] {d : α} {L : Matrix (Fin m) (Fin n) α}
    (h : ∀ i j, d ∣ L i j) (X : Matrix (Fin k) (Fin m) α) (Y : Matrix (Fin n) (Fin n) α)
    (i : Fin k) (j : Fin n) : d ∣ (X * L * Y) i j := by
  simp only [mul_apply]
  exact Finset.dvd_sum fun _ _ => (Finset.dvd_sum fun _ _ => (h _ _).mul_left _).mul_right _

section SmithRank

variable {R : Type*} [Zero R] [DecidableEq R]

/-- The number of leading nonzero diagonal entries, read recursively from the corner. For a
matrix in Smith normal form this is its rank: all later rows and columns vanish. -/
def smithRank : {m n : ℕ} → Matrix (Fin m) (Fin n) R → ℕ
  | 0, _, _ => 0
  | _ + 1, 0, _ => 0
  | _ + 1, _ + 1, A => if A 0 0 = 0 then 0 else smithRank (A.submatrix Fin.succ Fin.succ) + 1

theorem smithRank_le_left : ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) R), smithRank A ≤ m
  | 0, _, _ => le_rfl
  | _ + 1, 0, _ => Nat.zero_le _
  | _ + 1, _ + 1, A => by
    have := smithRank_le_left (A.submatrix Fin.succ Fin.succ)
    rw [smithRank]
    split_ifs <;> omega

theorem smithRank_le_right : ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) R), smithRank A ≤ n
  | 0, _, _ => Nat.zero_le _
  | _ + 1, 0, _ => le_rfl
  | _ + 1, _ + 1, A => by
    have := smithRank_le_right (A.submatrix Fin.succ Fin.succ)
    rw [smithRank]
    split_ifs <;> omega

@[simp]
theorem smithRank_zero : smithRank (0 : Matrix (Fin m) (Fin n) R) = 0 := by
  rcases m with _ | m <;> rcases n with _ | n <;> simp [smithRank]

theorem smithRank_of_ne_zero {A : Matrix (Fin (m + 1)) (Fin (n + 1)) R} (h : A 0 0 ≠ 0) :
    smithRank A = smithRank (A.submatrix Fin.succ Fin.succ) + 1 := by
  simp [smithRank, h]

end SmithRank

section Spec

variable {R : Type*} [CommMonoidWithZero R] [NormalizationMonoid R]

/-- A matrix is in *Smith normal form* if it is diagonal, with normalized diagonal entries
each dividing the next. Recursively: the matrix is empty or zero, or its corner entry is a
nonzero normalized pivot dividing every entry of the lower-right block, the rest of its
first row and column vanishes, and the lower-right block is in Smith normal form. -/
inductive IsSmithNormalForm : {m n : ℕ} → Matrix (Fin m) (Fin n) R → Prop
  /-- A matrix without rows. -/
  | empty_rows {n : ℕ} (A : Matrix (Fin 0) (Fin n) R) : IsSmithNormalForm A
  /-- A matrix without columns. -/
  | empty_cols {m : ℕ} (A : Matrix (Fin m) (Fin 0) R) : IsSmithNormalForm A
  /-- The zero matrix. -/
  | zero {m n : ℕ} : IsSmithNormalForm (0 : Matrix (Fin m) (Fin n) R)
  /-- A normalized nonzero pivot, followed by a Smith normal form it divides. -/
  | pivot {m n : ℕ} (A : Matrix (Fin (m + 1)) (Fin (n + 1)) R) (ne_zero : A 0 0 ≠ 0)
      (normalize_eq : normalize (A 0 0) = A 0 0) (row : ∀ j : Fin n, A 0 j.succ = 0)
      (col : ∀ i : Fin m, A i.succ 0 = 0)
      (lower : IsSmithNormalForm (A.submatrix Fin.succ Fin.succ))
      (dvd : ∀ (i : Fin m) (j : Fin n), A 0 0 ∣ A i.succ j.succ) : IsSmithNormalForm A

namespace IsSmithNormalForm

variable {A : Matrix (Fin m) (Fin n) R}

/-- A Smith normal form is diagonal. -/
theorem apply_eq_zero_of_val_ne (h : A.IsSmithNormalForm) {i : Fin m} {j : Fin n}
    (hij : i.val ≠ j.val) : A i j = 0 := by
  induction h with
  | empty_rows => exact i.elim0
  | empty_cols => exact j.elim0
  | zero => rfl
  | pivot A _ _ row col _ _ ih =>
    cases i using Fin.cases <;> cases j using Fin.cases
    · simp at hij
    · exact row _
    · exact col _
    · exact ih (by simpa using hij)

/-- The entries of a Smith normal form are normalized. -/
theorem normalize_apply (h : A.IsSmithNormalForm) (i : Fin m) (j : Fin n) :
    normalize (A i j) = A i j := by
  induction h with
  | empty_rows => exact i.elim0
  | empty_cols => exact j.elim0
  | zero => simp
  | pivot A _ hnorm row col _ _ ih =>
    cases i using Fin.cases <;> cases j using Fin.cases
    · exact hnorm
    · simp [row]
    · simp [col]
    · exact ih _ _

/-- Each diagonal entry of a Smith normal form divides the next one. -/
theorem diag_dvd_diag_succ (h : A.IsSmithNormalForm) (k : ℕ) (hm : k + 1 < m) (hn : k + 1 < n) :
    A ⟨k, by omega⟩ ⟨k, by omega⟩ ∣ A ⟨k + 1, hm⟩ ⟨k + 1, hn⟩ := by
  induction h generalizing k with
  | empty_rows => omega
  | empty_cols => omega
  | zero => simp
  | pivot A _ _ _ _ _ dvd ih =>
    cases k with
    | zero => exact dvd ⟨0, by omega⟩ ⟨0, by omega⟩
    | succ k => exact ih k (by omega) (by omega)

end IsSmithNormalForm

section SmithRank

variable [DecidableEq R]

namespace IsSmithNormalForm

variable {A : Matrix (Fin m) (Fin n) R}

/-- The rows of a Smith normal form beyond its rank vanish. -/
theorem apply_eq_zero_of_smithRank_le_left (h : A.IsSmithNormalForm) {i : Fin m}
    (hi : smithRank A ≤ i.val) (j : Fin n) : A i j = 0 := by
  induction h with
  | empty_rows => exact i.elim0
  | empty_cols => exact j.elim0
  | zero => rfl
  | pivot A hne _ _ col _ _ ih =>
    rw [smithRank_of_ne_zero hne] at hi
    cases i using Fin.cases with
    | zero => simp at hi
    | succ i =>
      cases j using Fin.cases
      · exact col i
      · exact ih (by simpa using hi) _

/-- The columns of a Smith normal form beyond its rank vanish. -/
theorem apply_eq_zero_of_smithRank_le_right (h : A.IsSmithNormalForm) (i : Fin m) {j : Fin n}
    (hj : smithRank A ≤ j.val) : A i j = 0 := by
  induction h with
  | empty_rows => exact i.elim0
  | empty_cols => exact j.elim0
  | zero => rfl
  | pivot A hne _ row _ _ _ ih =>
    rw [smithRank_of_ne_zero hne] at hj
    cases j using Fin.cases with
    | zero => simp at hj
    | succ j =>
      cases i using Fin.cases
      · exact row j
      · exact ih _ (by simpa using hj)

/-- The diagonal entries of a Smith normal form before its rank are nonzero. -/
theorem apply_ne_zero_of_lt_smithRank (h : A.IsSmithNormalForm) {i : Fin m} {j : Fin n}
    (hij : i.val = j.val) (hi : i.val < smithRank A) : A i j ≠ 0 := by
  induction h with
  | empty_rows => exact i.elim0
  | empty_cols => exact j.elim0
  | zero => simp at hi
  | pivot A hne _ _ _ _ _ ih =>
    rw [smithRank_of_ne_zero hne] at hi
    cases i using Fin.cases <;> cases j using Fin.cases
    · exact hne
    · simp at hij
    · simp at hij
    · exact ih (by simpa using hij) (by simpa using hi)

end IsSmithNormalForm

end SmithRank

end Spec

namespace IsSmithNormalForm

variable {R : Type*} [CommRing R] [NormalizationMonoid R] [DecidableEq R]
  {A : Matrix (Fin m) (Fin n) R}

omit [DecidableEq R] in
/-- A Smith normal form acts on each coordinate by its diagonal entry. -/
theorem mulVec_apply_of_lt (h : A.IsSmithNormalForm) (y : Fin n → R) (i : Fin m)
    (hi : i.val < n) : (A *ᵥ y) i = A i ⟨i, hi⟩ * y ⟨i, hi⟩ := by
  rw [mulVec, dotProduct, Finset.sum_eq_single ⟨i, hi⟩]
  · intro j _ hj
    rw [h.apply_eq_zero_of_val_ne fun e => hj (Fin.ext e.symm), zero_mul]
  · simp

/-- A Smith normal form vanishes on the coordinates beyond its rank. -/
theorem mulVec_apply_of_smithRank_le (h : A.IsSmithNormalForm) (y : Fin n → R) {i : Fin m}
    (hi : smithRank A ≤ i.val) : (A *ᵥ y) i = 0 := by
  simp [mulVec, dotProduct, h.apply_eq_zero_of_smithRank_le_left hi]

/-- Over a domain, the kernel of a Smith normal form consists of the vectors vanishing in the
first `smithRank A` coordinates. -/
theorem mulVec_eq_zero_iff [IsDomain R] (h : A.IsSmithNormalForm) (y : Fin n → R) :
    A *ᵥ y = 0 ↔ ∀ j : Fin n, j.val < smithRank A → y j = 0 := by
  refine ⟨fun hy j hj => ?_, fun hy => funext fun i => ?_⟩
  · have hjm : j.val < m := hj.trans_le (smithRank_le_left A)
    have := congrFun hy ⟨j, hjm⟩
    rw [h.mulVec_apply_of_lt y _ j.isLt, Pi.zero_apply] at this
    exact (mul_eq_zero.mp this).resolve_left (h.apply_ne_zero_of_lt_smithRank rfl hj)
  · refine (Finset.sum_eq_zero fun j _ => ?_ : ∑ j, A i j * y j = 0)
    by_cases hj : j.val < smithRank A
    · rw [hy j hj, mul_zero]
    · rw [h.apply_eq_zero_of_smithRank_le_right _ (not_lt.mp hj), zero_mul]

end IsSmithNormalForm

section Transform

variable {R : Type*} [CommRing R]

/-- A two-sided change of bases `U * A * V = B` with explicit inverses of `U` and `V`.
The columns of `V` and of `⅟U` are bases of the source and the target in which the linear
map `A` has matrix `B`. -/
structure TwoSidedTransform (A : Matrix (Fin m) (Fin n) R) where
  /-- The row operations, acting on the target. -/
  U : Matrix (Fin m) (Fin m) R
  /-- The explicit inverse of `U`. -/
  invertibleU : Invertible U
  /-- The column operations, acting on the source. -/
  V : Matrix (Fin n) (Fin n) R
  /-- The explicit inverse of `V`. -/
  invertibleV : Invertible V
  /-- The transformed matrix. -/
  B : Matrix (Fin m) (Fin n) R
  mul_mul_eq : U * A * V = B

namespace TwoSidedTransform

attribute [instance] invertibleU invertibleV

variable {A : Matrix (Fin m) (Fin n) R}

/-- The identity change of bases. -/
def refl (A : Matrix (Fin m) (Fin n) R) : TwoSidedTransform A :=
  ⟨1, invertibleOne, 1, invertibleOne, A, by rw [Matrix.one_mul, Matrix.mul_one]⟩

/-- Row operations by an invertible matrix `P`. -/
def ofLeft (P : Matrix (Fin m) (Fin m) R) [Invertible P] (A : Matrix (Fin m) (Fin n) R) :
    TwoSidedTransform A :=
  ⟨P, ‹_›, 1, invertibleOne, P * A, Matrix.mul_one _⟩

/-- A change of bases for `Aᵀ` transposes to one for `A`, exchanging rows and columns. -/
def ofTranspose (t : TwoSidedTransform Aᵀ) : TwoSidedTransform A :=
  ⟨t.Vᵀ, invertibleTranspose _, t.Uᵀ, invertibleTranspose _, t.Bᵀ, by
    rw [← t.mul_mul_eq, transpose_mul, transpose_mul, transpose_transpose, Matrix.mul_assoc]⟩

/-- The memoized copy of an invertible matrix, with the memoized inverse. -/
@[instance_reducible]
def invertibleMemoize (M : Matrix (Fin m) (Fin m) R) (h : Invertible M) :
    Invertible (ofTable (memoTable M)) :=
  h.copy' _ (ofTable (memoTable (⅟M))) (ofTable_memoTable M) (ofTable_memoTable _)

/-- First change bases by `t`, then by `s`. The resulting matrices are memoized. -/
def trans (t : TwoSidedTransform A) (s : TwoSidedTransform t.B) : TwoSidedTransform A where
  U := ofTable (memoTable (s.U * t.U))
  invertibleU := invertibleMemoize _ (invertibleMul _ _)
  V := ofTable (memoTable (t.V * s.V))
  invertibleV := invertibleMemoize _ (invertibleMul _ _)
  B := ofTable (memoTable s.B)
  mul_mul_eq := by
    simp only [ofTable_memoTable, ← s.mul_mul_eq, ← t.mul_mul_eq, Matrix.mul_assoc]

@[simp] theorem refl_B : (refl A).B = A := rfl

@[simp] theorem ofLeft_B (P : Matrix (Fin m) (Fin m) R) [Invertible P] :
    (ofLeft P A).B = P * A := rfl

@[simp] theorem ofTranspose_B (t : TwoSidedTransform Aᵀ) : (ofTranspose t).B = t.Bᵀ := rfl

@[simp] theorem trans_B (t : TwoSidedTransform A) (s : TwoSidedTransform t.B) :
    (t.trans s).B = s.B :=
  ofTable_memoTable _

/-- Extend a change of bases of the lower-right block of a matrix whose first row and column
vanish away from the corner. -/
def diagCons {B : Matrix (Fin (m + 1)) (Fin (n + 1)) R} (row : ∀ j : Fin n, B 0 j.succ = 0)
    (col : ∀ i : Fin m, B i.succ 0 = 0) (s : TwoSidedTransform (B.submatrix Fin.succ Fin.succ)) :
    TwoSidedTransform B :=
  ⟨Matrix.diagCons 1 s.U, inferInstance, Matrix.diagCons 1 s.V, inferInstance,
    Matrix.diagCons (B 0 0) s.B, by rw [diagCons_one_mul_mul_diagCons_one row col, s.mul_mul_eq]⟩

@[simp] theorem diagCons_B {B : Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (row : ∀ j : Fin n, B 0 j.succ = 0) (col : ∀ i : Fin m, B i.succ 0 = 0)
    (s : TwoSidedTransform (B.submatrix Fin.succ Fin.succ)) :
    (diagCons row col s).B = Matrix.diagCons (B 0 0) s.B := rfl

/-- Since `U * A * V = B`, the matrix `A` sends the columns of `V` to combinations of the
columns of `⅟U` with coefficients the columns of `B`. -/
theorem mul_eq_invOf_mul (t : TwoSidedTransform A) : A * t.V = ⅟t.U * t.B := by
  rw [← t.mul_mul_eq, Matrix.mul_assoc, Matrix.invOf_mul_cancel_left]

/-- The image of the `j`-th source basis vector, expanded in the target basis. -/
theorem mulVec_col (t : TwoSidedTransform A) (j : Fin n) :
    A *ᵥ t.V.col j = ∑ i, t.B i j • (⅟t.U).col i := by
  rw [← mulVec_single_one, mulVec_mulVec, mul_eq_invOf_mul, ← mulVec_mulVec, mulVec_single_one]
  ext r
  simp [mulVec, dotProduct, mul_comm]

/-- The source basis: the columns of `V`. -/
noncomputable def sourceBasis (t : TwoSidedTransform A) : Module.Basis (Fin n) R (Fin n → R) :=
  (Pi.basisFun R (Fin n)).map (toLinearEquiv' t.V t.invertibleV)

/-- The target basis: the columns of `⅟U`. -/
noncomputable def targetBasis (t : TwoSidedTransform A) : Module.Basis (Fin m) R (Fin m → R) :=
  (Pi.basisFun R (Fin m)).map (toLinearEquiv' (⅟t.U) (invertibleInvOf))

@[simp] theorem sourceBasis_apply (t : TwoSidedTransform A) (j : Fin n) :
    t.sourceBasis j = t.V.col j := by
  simp [sourceBasis, toLinearEquiv']

@[simp] theorem targetBasis_apply (t : TwoSidedTransform A) (i : Fin m) :
    t.targetBasis i = (⅟t.U).col i := by
  simp [targetBasis, toLinearEquiv']

end TwoSidedTransform

/-- A Smith normal form of `A`: a two-sided change of bases `U * A * V = B` with `B` in Smith
normal form. -/
structure SmithNormalForm [NormalizationMonoid R] (A : Matrix (Fin m) (Fin n) R)
    extends TwoSidedTransform A where
  isSmithNormalForm : B.IsSmithNormalForm

namespace SmithNormalForm

variable [NormalizationMonoid R] {A : Matrix (Fin m) (Fin n) R}
  (s : SmithNormalForm A)

/-- `A` sends the `k`-th source basis vector to the `k`-th invariant factor times the `k`-th
target basis vector. -/
theorem mulVec_col_of_val_eq {i : Fin m} {j : Fin n} (h : i.val = j.val) :
    A *ᵥ s.V.col j = s.B i j • (⅟s.U).col i := by
  rw [s.mulVec_col, Finset.sum_eq_single i]
  · intro i' _ hi'
    rw [s.isSmithNormalForm.apply_eq_zero_of_val_ne (by omega), zero_smul]
  · simp

/-- `A` kills the source basis vectors beyond the number of rows. -/
theorem mulVec_col_eq_zero {j : Fin n} (h : m ≤ j.val) : A *ᵥ s.V.col j = 0 := by
  rw [s.mulVec_col]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [s.isSmithNormalForm.apply_eq_zero_of_val_ne (by omega), zero_smul]

end SmithNormalForm

end Transform

/-! ### Elementary row operations -/

section Elementary

variable {R : Type*} [CommRing R]

/-- The elementary matrix adding `c i` times row `0` to row `i.succ`, for every `i`. -/
def addRowZero (c : Fin m → R) : Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
  1 + vecMulVec (Fin.cons 0 c) (Pi.single 0 1)

@[simp] theorem addRowZero_mul_apply_zero (c : Fin m → R) (M : Matrix (Fin (m + 1)) (Fin n) R)
    (j : Fin n) : (addRowZero c * M) 0 j = M 0 j := by
  rw [addRowZero, Matrix.add_mul, Matrix.one_mul]
  simp [mul_apply, vecMulVec_apply, Pi.single_apply]

@[simp] theorem addRowZero_mul_apply_succ (c : Fin m → R) (M : Matrix (Fin (m + 1)) (Fin n) R)
    (i : Fin m) (j : Fin n) : (addRowZero c * M) i.succ j = M i.succ j + c i * M 0 j := by
  rw [addRowZero, Matrix.add_mul, Matrix.one_mul]
  simp [mul_apply, vecMulVec_apply, Pi.single_apply]

theorem addRowZero_mul_addRowZero (c d : Fin m → R) :
    addRowZero c * addRowZero d = addRowZero (c + d) := by
  ext i j
  cases i using Fin.cases
  · rw [addRowZero_mul_apply_zero]
    simp [addRowZero, vecMulVec_apply]
  · rw [addRowZero_mul_apply_succ]
    cases j using Fin.cases <;>
      simp [addRowZero, vecMulVec_apply, one_apply, add_comm, (Fin.succ_ne_zero _).symm]

@[simp] theorem addRowZero_zero : addRowZero (0 : Fin m → R) = 1 := by
  ext i j
  cases i using Fin.cases <;> simp [addRowZero, vecMulVec_apply]

/-- `addRowZero c` is invertible with inverse `addRowZero (-c)`. -/
instance invertibleAddRowZero (c : Fin m → R) : Invertible (addRowZero c) where
  invOf := addRowZero (-c)
  invOf_mul_self := by rw [addRowZero_mul_addRowZero, neg_add_cancel, addRowZero_zero]
  mul_invOf_self := by rw [addRowZero_mul_addRowZero, add_neg_cancel, addRowZero_zero]

/-- A permutation matrix swapping two rows is its own inverse. -/
instance invertibleSwap {ι : Type*} [Fintype ι] [DecidableEq ι] (i j : ι) :
    Invertible (swap R i j) :=
  ⟨swap R i j, swap_mul_self i j, swap_mul_self i j⟩

/-- A transvection `1 + c • E i j` with `i ≠ j` has inverse `1 - c • E i j`. -/
@[instance_reducible]
def invertibleTransvection {ι : Type*} [Fintype ι] [DecidableEq ι] {i j : ι} (h : i ≠ j)
    (c : R) : Invertible (transvection i j c) where
  invOf := transvection i j (-c)
  invOf_mul_self := by simp [transvection_mul_transvection_same i j h]
  mul_invOf_self := by simp [transvection_mul_transvection_same i j h]

end Elementary

/-! ### The algorithm over `ℤ` -/

namespace SmithNormalForm

open TwoSidedTransform

theorem natAbs_emod_lt (a : ℤ) {b : ℤ} (hb : b ≠ 0) : (a % b).natAbs < b.natAbs := by
  have := Int.emod_nonneg a hb
  have := Int.emod_lt a hb
  omega

section Steps

variable (B : Matrix (Fin (m + 1)) (Fin (n + 1)) ℤ)

/-- Replace each entry of column `0` below the pivot by its remainder modulo the pivot. -/
def reduceCol : TwoSidedTransform B :=
  ofLeft (addRowZero fun i => -(B i.succ 0 / B 0 0)) B

@[simp] theorem reduceCol_B_zero (j : Fin (n + 1)) : (reduceCol B).B 0 j = B 0 j := by
  simp [reduceCol]

theorem reduceCol_B_succ_zero (i : Fin m) : (reduceCol B).B i.succ 0 = B i.succ 0 % B 0 0 := by
  simp [reduceCol, Int.emod_def]
  ring

/-- Reduce column `0` modulo the pivot, then swap row `i.succ` to the top. -/
def rowStep (i : Fin m) : TwoSidedTransform B :=
  (reduceCol B).trans (ofLeft (swap ℤ 0 i.succ) _)

theorem rowStep_B_zero_zero (i : Fin m) : (rowStep B i).B 0 0 = B i.succ 0 % B 0 0 := by
  simp [rowStep, swap_mul_apply_left, reduceCol_B_succ_zero]

/-- Reduce row `0` modulo the pivot, then swap column `j.succ` to the left. -/
def colStep (j : Fin n) : TwoSidedTransform B :=
  ofTranspose (rowStep Bᵀ j)

theorem colStep_B_zero_zero (j : Fin n) : (colStep B j).B 0 0 = B 0 j.succ % B 0 0 :=
  rowStep_B_zero_zero Bᵀ j

/-- Reduce column `0`, then row `0`, modulo the pivot. -/
def clearStep : TwoSidedTransform B :=
  (reduceCol B).trans (ofTranspose (reduceCol (reduceCol B).Bᵀ))

@[simp] theorem clearStep_B_zero_zero : (clearStep B).B 0 0 = B 0 0 := by
  simp [clearStep]

theorem clearStep_B_succ_zero (hcol : ∀ i : Fin m, B 0 0 ∣ B i.succ 0) (i : Fin m) :
    (clearStep B).B i.succ 0 = 0 := by
  simp [clearStep, reduceCol_B_succ_zero, Int.emod_eq_zero_of_dvd (hcol i)]

theorem clearStep_B_zero_succ (hrow : ∀ j : Fin n, B 0 0 ∣ B 0 j.succ) (j : Fin n) :
    (clearStep B).B 0 j.succ = 0 := by
  simp [clearStep, reduceCol_B_succ_zero, Int.emod_eq_zero_of_dvd (hrow j)]

/-- Add row `i.succ` to row `0`. -/
def addRowStep (i : Fin m) : TwoSidedTransform B :=
  @ofLeft _ _ _ _ (transvection 0 i.succ 1) (invertibleTransvection (Fin.succ_ne_zero i).symm 1) B

theorem addRowStep_B_zero (i : Fin m) (j : Fin (n + 1)) :
    (addRowStep B i).B 0 j = B 0 j + B i.succ j := by
  simp [addRowStep, transvection_mul_apply_same]

/-- Clear the first row and column, add row `i.succ` to row `0`, and reduce row `0` modulo the
pivot, swapping column `j.succ` to the left. The new pivot is a remainder of entry
`(i.succ, j.succ)` of the cleared matrix. -/
def lowerStep (i : Fin m) (j : Fin n) : TwoSidedTransform B :=
  (clearStep B).trans ((addRowStep _ i).trans (colStep _ j))

theorem lowerStep_B_zero_zero (hcol : ∀ i : Fin m, B 0 0 ∣ B i.succ 0)
    (hrow : ∀ j : Fin n, B 0 0 ∣ B 0 j.succ) (i : Fin m) (j : Fin n) :
    (lowerStep B i j).B 0 0 = (clearStep B).B i.succ j.succ % B 0 0 := by
  simp [lowerStep, colStep_B_zero_zero, addRowStep_B_zero, clearStep_B_zero_succ _ hrow,
    clearStep_B_succ_zero _ hcol]

/-- Negate all entries. -/
def negStep : TwoSidedTransform B :=
  @ofLeft _ _ _ _ (-1) ⟨-1, by simp, by simp⟩ B

@[simp] theorem negStep_B : (negStep B).B = -B := by
  simp [negStep]

/-- Swap row `i` and column `j` into row and column `0`. -/
def toCorner (i : Fin (m + 1)) (j : Fin (n + 1)) : TwoSidedTransform B :=
  (ofLeft (swap ℤ 0 i) B).trans (ofTranspose (ofLeft (swap ℤ 0 j) _))

@[simp] theorem toCorner_B_zero_zero (i : Fin (m + 1)) (j : Fin (n + 1)) :
    (toCorner B i j).B 0 0 = B i j := by
  rw [toCorner, trans_B]
  simp [swap_mul_apply_left]

end Steps

/-- A transform whose result has a positive pivot dividing the lower-right block, and whose
first row and column vanish away from the pivot. -/
structure PivotState (A : Matrix (Fin (m + 1)) (Fin (n + 1)) ℤ) extends TwoSidedTransform A where
  pivot_pos : 0 < B 0 0
  row_eq_zero (j : Fin n) : B 0 j.succ = 0
  col_eq_zero (i : Fin m) : B i.succ 0 = 0
  dvd (i : Fin m) (j : Fin n) : B 0 0 ∣ B i.succ j.succ

variable {A : Matrix (Fin (m + 1)) (Fin (n + 1)) ℤ}

/-- Make a nonzero pivot positive, given that the first row and column vanish and the pivot
divides the lower-right block. -/
def PivotState.ofNeZero (t : TwoSidedTransform A) (hp : t.B 0 0 ≠ 0)
    (row : ∀ j : Fin n, t.B 0 j.succ = 0) (col : ∀ i : Fin m, t.B i.succ 0 = 0)
    (dvd : ∀ (i : Fin m) (j : Fin n), t.B 0 0 ∣ t.B i.succ j.succ) : PivotState A :=
  if hpos : 0 < t.B 0 0 then ⟨t, hpos, row, col, dvd⟩
  else ⟨t.trans (negStep t.B), by simp; omega, by simp [row], by simp [col], by simp [dvd]⟩

/-- Transforms of `A` whose pivot is nonzero and smaller in absolute value than `p`. -/
abbrev SmallerPivot (A : Matrix (Fin (m + 1)) (Fin (n + 1)) ℤ) (p : ℤ) :=
  {t : TwoSidedTransform A // t.B 0 0 ≠ 0 ∧ (t.B 0 0).natAbs < p.natAbs}

/-- Follow `t` by a step `s` whose new pivot is a nonzero remainder modulo the old pivot. -/
def descend (t : TwoSidedTransform A) (hp : t.B 0 0 ≠ 0) (s : TwoSidedTransform t.B) {a : ℤ}
    (hs : s.B 0 0 = a % t.B 0 0) (ha : ¬t.B 0 0 ∣ a) : SmallerPivot A (t.B 0 0) :=
  ⟨t.trans s, by
    rw [trans_B, hs]
    exact ⟨mt Int.dvd_of_emod_eq_zero ha, natAbs_emod_lt a hp⟩⟩

/-- One round of pivot improvement: either the pivot already divides its row, its column and
the lower-right block, or some remainder modulo the pivot gives a smaller pivot. -/
def step (t : TwoSidedTransform A) (hp : t.B 0 0 ≠ 0) : PivotState A ⊕ SmallerPivot A (t.B 0 0) :=
  if hcol : ∃ i, ¬t.B 0 0 ∣ t.B i.succ 0 then
    .inr (descend t hp _ (rowStep_B_zero_zero _ _) (Fin.find_spec hcol))
  else if hrow : ∃ j, ¬t.B 0 0 ∣ t.B 0 j.succ then
    .inr (descend t hp _ (colStep_B_zero_zero _ _) (Fin.find_spec hrow))
  else if hlow : ∃ i j, ¬t.B 0 0 ∣ (clearStep t.B).B i.succ j.succ then
    .inr (descend t hp _ (lowerStep_B_zero_zero _ (by simpa using hcol) (by simpa using hrow)
      _ (Fin.find _ (Fin.find_spec hlow))) (Fin.find_spec (Fin.find_spec hlow)))
  else
    .inl (.ofNeZero (t.trans (clearStep t.B)) (by simpa using hp)
      (by simpa using clearStep_B_zero_succ _ (by simpa using hrow))
      (by simpa using clearStep_B_succ_zero _ (by simpa using hcol)) (by simpa using hlow))

/-- Pivot stabilization, by well-founded recursion on the absolute value of the pivot. -/
def stabilize (t : TwoSidedTransform A) (hp : t.B 0 0 ≠ 0) : PivotState A :=
  match step t hp with
  | .inl s => s
  | .inr t' => stabilize t'.1 t'.2.1
termination_by (t.B 0 0).natAbs
decreasing_by exact t'.2.2

/-- The pivot divides every entry of the transformed lower-right block, so the block-diagonal
combination of a pivot state with a Smith normal form of its lower-right block is in Smith
normal form. -/
theorem isSmithNormalForm_diagCons (p : PivotState A)
    (s : (p.B.submatrix Fin.succ Fin.succ).SmithNormalForm) :
    (p.trans (TwoSidedTransform.diagCons p.row_eq_zero p.col_eq_zero
      s.toTwoSidedTransform)).B.IsSmithNormalForm := by
  rw [trans_B, TwoSidedTransform.diagCons_B]
  refine .pivot _ p.pivot_pos.ne' (Int.normalize_of_nonneg p.pivot_pos.le) (fun _ => rfl)
    (fun _ => rfl) s.isSmithNormalForm fun i j => ?_
  rw [diagCons_zero_zero, diagCons_succ_succ, ← s.mul_mul_eq]
  exact dvd_mul_mul_apply p.dvd _ _ i j

end SmithNormalForm

open SmithNormalForm TwoSidedTransform in
/-- The Smith normal form of an integer matrix `A`, together with the change of bases:
invertible `U` and `V`, with their inverses, such that `U * A * V` is in Smith normal form. -/
def smithNormalForm : {m n : ℕ} → (A : Matrix (Fin m) (Fin n) ℤ) → A.SmithNormalForm
  | 0, _, A => ⟨.refl A, .empty_rows A⟩
  | _ + 1, 0, A => ⟨.refl A, .empty_cols A⟩
  | _ + 1, _ + 1, A =>
    haveI : DecidablePred fun i => ∃ j, A i j ≠ 0 := fun _ => inferInstance
    if h : ∃ i j, A i j ≠ 0 then
      let p := stabilize (toCorner A (Fin.find _ h) (Fin.find _ (Fin.find_spec h)))
        (by simpa using Fin.find_spec (Fin.find_spec h))
      let s := smithNormalForm (p.B.submatrix Fin.succ Fin.succ)
      ⟨p.trans (TwoSidedTransform.diagCons p.row_eq_zero p.col_eq_zero s.toTwoSidedTransform),
        isSmithNormalForm_diagCons p s⟩
    else
      ⟨.refl A, by
        obtain rfl : A = 0 := by
          push Not at h
          exact ext h
        exact .zero⟩

end Matrix
