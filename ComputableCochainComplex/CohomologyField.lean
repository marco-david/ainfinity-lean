/-
Copyright (c) 2026 Annie Yao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Annie Yao
-/
module

public import ComputableCochainComplex.CohomologyReduction
public import ComputableCochainComplex.Cohomology
public import Mathlib.LinearAlgebra.Matrix.Rank
public meta import Lean.Elab.Tactic.Basic

/-!
# Certified cohomology over computable fields

Exact Gaussian reduction retains both coordinate transformations and their inverses.
Its loops are bounded by the matrix dimensions. Candidate kernel and quotient coordinates
are checked by the generic finite verifier before a result is returned. Every successful
result contains complete cohomology coordinates, representatives, and boundary preimages,
with an isomorphism to Mathlib homology. Verification failure is explicit.
-/

@[expose] public section

namespace ComputableCohomology

open CategoryTheory
open scoped Matrix

variable {R : Type*} {a b c : ℕ}

/-- Exact two-sided Gaussian elimination. At most `min m n` pivots are processed.
The result is candidate data; public solvers check it before using it as a certificate. -/
def fieldReduce [Field R] [DecidableEq R] {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) R) : MatrixReductionData R m n := Id.run do
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
      let p := s.reduced row col
      s := s.scaleRow row p⁻¹ p
      for i in List.finRange m do
        if i ≠ row then s := s.addRow i row (-s.reduced i col)
      for j in List.finRange n do
        if j ≠ col then s := s.addCol j col (-s.reduced row j)
      s := { s with rank := k.val + 1 }
  return s

variable [CommRing R]

/-- A certified free cohomology model for two consecutive differential matrices. -/
structure FreeCohomologyCertificate (A : Matrix (Fin b) (Fin a) R)
    (B : Matrix (Fin c) (Fin b) R) where
  /-- The matrices are consecutive differentials. -/
  square_zero : B * A = 0
  /-- Coordinates for all cocycles. -/
  kernel : KernelCertificate B
  /-- Representatives, normalization, and boundary preimages in kernel coordinates. -/
  quotient : SplitPresentationData R a kernel.size
  /-- The quotient data satisfy the exact splitting equations. -/
  valid : quotient.Valid (kernel.retraction * A)

namespace FreeCohomologyCertificate

variable {A : Matrix (Fin b) (Fin a) R} {B : Matrix (Fin c) (Fin b) R}
  (result : FreeCohomologyCertificate A B)

/-- The number of cohomology coordinates. -/
abbrev size : ℕ := result.quotient.size

/-- Normalize a cocycle to its unique class coordinates. -/
def normalize (x : Fin b → R) : Fin result.size → R :=
  result.quotient.normalize *ᵥ (result.kernel.retraction *ᵥ x)

/-- The chosen original-coordinate cocycle representing a class. -/
def representative (x : Fin result.size → R) : Fin b → R :=
  result.kernel.inclusion *ᵥ (result.quotient.representatives *ᵥ x)

/-- A preimage of the boundary part of a cocycle, in the original source coordinates. -/
def preimage (x : Fin b → R) : Fin a → R :=
  result.quotient.preimage *ᵥ (result.kernel.retraction *ᵥ x)

lemma representative_is_cocycle (x : Fin result.size → R) :
    B *ᵥ result.representative x = 0 := result.kernel.inclusion_mem_ker _

@[simp] lemma normalize_representative (x : Fin result.size → R) :
    result.normalize (result.representative x) = x := by
  unfold normalize representative
  rw [result.kernel.retraction_inclusion]
  exact result.quotient.normalize_representative _ result.valid x

lemma normalize_boundary (x : Fin a → R) : result.normalize (A *ᵥ x) = 0 := by
  unfold normalize
  rw [Matrix.mulVec_mulVec x result.kernel.retraction A]
  exact result.quotient.normalize_boundary _ result.valid x

/-- Vanishing class coordinates give a verified, executable boundary preimage. -/
lemma normalize_eq_zero_iff (x : Fin b → R) (hx : B *ᵥ x = 0) :
    result.normalize x = 0 ↔ A *ᵥ result.preimage x = x :=
  (result.quotient.normalize_eq_zero_iff _ result.valid _).trans
    (result.kernel.boundary_preimage_iff A result.square_zero x hx _)

/-- The boundary test is complete for every cocycle. -/
lemma boundary_iff (x : Fin b → R) (hx : B *ᵥ x = 0) :
    (∃ y, A *ᵥ y = x) ↔ result.normalize x = 0 := by
  constructor
  · rintro ⟨y, rfl⟩
    exact result.normalize_boundary y
  · intro h
    exact ⟨result.preimage x, (result.normalize_eq_zero_iff x hx).mp h⟩

/-- Return a certified preimage precisely when the given cocycle is a boundary. -/
def boundaryPreimage [DecidableEq R] (x : Fin b → R) (hx : B *ᵥ x = 0) :
    Option {y : Fin a → R // A *ᵥ y = x} :=
  if h : result.normalize x = 0 then
    some ⟨result.preimage x, (result.normalize_eq_zero_iff x hx).mp h⟩
  else none

/-- The checked coordinates compute the homology of the local matrix complex. -/
noncomputable def homologyIso :
    (KernelCertificate.shortComplex A result.square_zero).homology ≅
      ModuleCat.of R (Fin result.size → R) :=
  result.kernel.homologyIso A result.square_zero ≪≫
    (result.quotient.quotientEquiv _ result.valid).toModuleIso

end FreeCohomologyCertificate

end ComputableCohomology

namespace ComputableCohomology

variable {R : Type*} [Field R] {a b c : ℕ}

/-- The certified kernel dimension satisfies rank-nullity. -/
lemma KernelCertificate.size_add_rank {B : Matrix (Fin c) (Fin b) R}
    (k : KernelCertificate B) : k.size + B.rank = b := by
  have h := B.mulVecLin.finrank_range_add_finrank_ker
  rw [← k.cyclesEquiv.finrank_eq] at h
  simpa [Matrix.rank, add_comm] using h

/-- Passing to certified kernel coordinates preserves the rank of the incoming differential. -/
lemma KernelCertificate.boundary_rank {B : Matrix (Fin c) (Fin b) R}
    (k : KernelCertificate B) (A : Matrix (Fin b) (Fin a) R) (hBA : B * A = 0) :
    (k.retraction * A).rank = A.rank := by
  apply le_antisymm (Matrix.rank_mul_le_right _ _)
  calc
    A.rank = (k.inclusion * (k.retraction * A)).rank := by
      rw [k.inclusion_mul_retraction_mul A hBA]
    _ ≤ (k.retraction * A).rank := Matrix.rank_mul_le_right _ _

/-- Certified quotient coordinates account for the full boundary rank. -/
lemma SplitPresentationData.size_add_rank (q : SplitPresentationData R a b)
    (W : Matrix (Fin b) (Fin a) R) (h : q.Valid W) : q.size + W.rank = b := by
  have hd := (LinearMap.range W.mulVecLin).finrank_quotient_add_finrank
  rw [(q.quotientEquiv W h).finrank_eq] at hd
  simpa [Matrix.rank] using hd

/-- The computed number of classes is the usual Betti-number formula. -/
lemma FreeCohomologyCertificate.size_eq {A : Matrix (Fin b) (Fin a) R}
    {B : Matrix (Fin c) (Fin b) R} (result : FreeCohomologyCertificate A B) :
    result.size = b - A.rank - B.rank := by
  have hk := result.kernel.size_add_rank
  have hq := result.quotient.size_add_rank _ result.valid
  rw [result.kernel.boundary_rank A result.square_zero] at hq
  change result.size + A.rank = result.kernel.size at hq
  omega

/-- Compute exact free cohomology coordinates, checking every certificate before returning it.
Errors report invalid differential data or failed certificate verification. -/
def computeField [DecidableEq R] (A : Matrix (Fin b) (Fin a) R)
    (B : Matrix (Fin c) (Fin b) R) :
    Except String (FreeCohomologyCertificate A B) :=
  if hBA : B * A = 0 then
    let kd := (fieldReduce B).kernelData
    if hk : kd.Valid B then
      let k := kd.certificate B hk
      let q := (fieldReduce (k.retraction * A)).splitPresentationData
      if hq : q.Valid (k.retraction * A) then
        .ok { square_zero := hBA, kernel := k, quotient := q, valid := hq }
      else .error "field cohomology: quotient certificate verification failed"
    else .error "field cohomology: kernel certificate verification failed"
  else .error "field cohomology: the differential matrices do not compose to zero"

end ComputableCohomology

namespace FiniteFreeCochainComplex

open CategoryTheory

variable {R : Type*} [Field R] [DecidableEq R] (C : FiniteFreeCochainComplex R) (n : ℤ)

/-- Compute cohomology at one requested degree, without enumerating the support. -/
def computeFieldCohomology :
    Except String (ComputableCohomology.FreeCohomologyCertificate (C.incoming n) (C.d n)) :=
  ComputableCohomology.computeField (C.incoming n) (C.d n)

/-- The computed free model is Mathlib's cohomology of the supplied finite-free complex. -/
noncomputable def fieldCohomologyIso
    (result : ComputableCohomology.FreeCohomologyCertificate (C.incoming n) (C.d n)) :
    C.toCochainComplex.homology n ≅ ModuleCat.of R (Fin result.size → R) :=
  C.localHomologyIso n ≪≫ result.homologyIso

end FiniteFreeCochainComplex

open Lean Elab Tactic Meta in
/-- Check the coefficient ring before elaborating the certificate's dependent model type. -/
private meta def checkFieldInput (input : TSyntax `term) (complex : Bool) : TacticM Unit :=
  withMainContext do
    let value ← Term.elabTerm input none
    Term.synthesizeSyntheticMVarsNoPostponing
    let type ← instantiateMVars (← inferType value)
    let ring ← if complex then do
        let type ← whnf type
        unless type.isAppOfArity ``FiniteFreeCochainComplex 2 do
          throwError "certify_cohomology: expected a finite-free cochain complex"
        pure type.getAppArgs[0]!
      else forallBoundedTelescope type (some 2) fun indices ring => do
        unless indices.size = 2 do
          throwError "certify_cohomology: expected a matrix with two finite indices"
        pure ring
    try
      let _ ← synthInstance (← mkAppM ``Field #[ring])
    catch _ =>
      throwError "certify_cohomology: coefficient ring {ring} is not a supported field; \
        use computeInteger for integral cohomology"
    try
      let _ ← synthInstance (← mkAppM ``DecidableEq #[ring])
    catch _ =>
      throwError "certify_cohomology: exact decidable equality is required on {ring}"

/-- Prove an explicit local cohomology isomorphism using a kernel-checked field certificate. -/
syntax "certify_cohomology " term ", " term : tactic

/-- Prove an explicit cohomology isomorphism at one requested integer degree. -/
syntax "certify_cohomology " term " at " term : tactic

open Lean Elab Tactic in
elab_rules : tactic
  | `(tactic| certify_cohomology $A, $B) => do
    checkFieldInput A false
    evalTactic (← `(tactic| (
      refine ⟨((ComputableCohomology.computeField $A $B).toOption.get
        (by decide +kernel)).homologyIso ≪≫ ?_⟩
      exact (LinearEquiv.funCongrLeft _ _ (finCongr (by decide +kernel))).toModuleIso)))
  | `(tactic| certify_cohomology $C at $n) => do
    checkFieldInput C true
    evalTactic (← `(tactic| (
      refine ⟨FiniteFreeCochainComplex.fieldCohomologyIso $C $n
        ((FiniteFreeCochainComplex.computeFieldCohomology $C $n).toOption.get
          (by decide +kernel)) ≪≫ ?_⟩
      exact (LinearEquiv.funCongrLeft _ _ (finCongr (by decide +kernel))).toModuleIso)))
