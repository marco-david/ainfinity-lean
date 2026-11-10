/-
Copyright (c) 2026 Annie Yao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Annie Yao
-/
module

public import ComputableCochainComplex.CohomologyReduction
public import Mathlib.Data.ZMod.Basic

/-!
# Checked integral presentations

An integral presentation is certified by two inverse coordinate changes and two equations
identifying its relation module with a nonnegative diagonal relation module. Divisibility
of successive diagonal entries is checked separately. Zero entries describe free summands;
entries equal to one describe trivial summands.
-/

@[expose] public section

namespace ComputableCohomology

open scoped Matrix

/-- Candidate Smith coordinates, with witnesses for both inclusions of relation modules. -/
structure SmithPresentationData (a b : ℕ) where
  /-- Nonnegative diagonal relations, with zero denoting a free coordinate. -/
  diagonal : Fin b → ℕ
  /-- Coordinates in the diagonal presentation. -/
  coordinates : Matrix (Fin b) (Fin b) ℤ
  /-- Original-coordinate representatives of diagonal generators. -/
  representatives : Matrix (Fin b) (Fin b) ℤ
  /-- Express original relations as diagonal relations. -/
  relations : Matrix (Fin b) (Fin a) ℤ
  /-- Original preimages of diagonal relations. -/
  preimages : Matrix (Fin a) (Fin b) ℤ

namespace SmithPresentationData

variable {a b : ℕ} (data : SmithPresentationData a b) (W : Matrix (Fin b) (Fin a) ℤ)

/-- Exact finite conditions certifying a normalized Smith presentation. -/
def Valid : Prop :=
  data.coordinates * data.representatives = 1 ∧
  data.representatives * data.coordinates = 1 ∧
  data.coordinates * W = Matrix.diagonal (fun i => (data.diagonal i : ℤ)) * data.relations ∧
  W * data.preimages = data.representatives * Matrix.diagonal (fun i => (data.diagonal i : ℤ)) ∧
  ∀ i j, i < j → data.diagonal i ∣ data.diagonal j

instance : Decidable (data.Valid W) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/-- All cyclic coordinates, including `ZMod 0 = ℤ` and trivial unit coordinates. -/
abbrev Coordinates := ∀ i, ZMod (data.diagonal i)

/-- Normalize an integer vector in the diagonal presentation. -/
def normalize : (Fin b → ℤ) →ₗ[ℤ] data.Coordinates :=
  (LinearMap.pi fun i => (Int.castAddHom (ZMod (data.diagonal i))).toIntLinearMap.comp
    (LinearMap.proj i)).comp data.coordinates.mulVecLin

@[simp] lemma normalize_apply (x : Fin b → ℤ) (i : Fin b) :
    data.normalize x i = ((data.coordinates *ᵥ x) i : ZMod (data.diagonal i)) := rfl

/-- Lift cyclic coordinates using canonical residues and unrestricted free coordinates. -/
def representative (x : data.Coordinates) : Fin b → ℤ :=
  data.representatives *ᵥ (fun i => ZMod.cast (x i))

@[simp] lemma representative_zero : data.representative 0 = 0 := by
  simp only [representative, Pi.zero_apply, ZMod.cast_zero]
  exact Matrix.mulVec_zero _

/-- The original preimage of the part removed by canonical residue normalization. -/
def preimage (x : Fin b → ℤ) : Fin a → ℤ :=
  data.preimages *ᵥ (fun i =>
    ((data.coordinates *ᵥ x) i - ZMod.cast (data.normalize x i)) / data.diagonal i)

lemma residue_sub_dvd (d : ℕ) (z : ℤ) :
    (d : ℤ) ∣ z - ZMod.cast (z : ZMod d) := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ d).mp
  simp

/-- The explicit free part and nontrivial torsion part, omitting every unit factor. -/
abbrev Model :=
  ({i : Fin b // data.diagonal i = 0} → ℤ) ×
    (∀ i : {i : Fin b // 1 < data.diagonal i}, ZMod (data.diagonal i.val))

/-- Number of unrestricted integer coordinates. -/
def freeRank : ℕ := Fintype.card {i : Fin b // data.diagonal i = 0}

/-- Nontrivial invariant factors in their original diagonal order. -/
def torsionFactors : List ℕ :=
  ((List.finRange b).map data.diagonal).filter (fun d => 1 < d)

/-- Discard trivial cyclic factors and distinguish free coordinates from torsion coordinates. -/
def splitEquiv : data.Coordinates ≃ₗ[ℤ] data.Model := AddEquiv.toIntLinearEquiv
  { toFun := fun x => (fun i => ZMod.cast (x i.val), fun i => x i.val)
    invFun := fun x i => if h0 : data.diagonal i = 0 then
      (x.1 ⟨i, h0⟩ : ZMod (data.diagonal i)) else
      if h1 : 1 < data.diagonal i then x.2 ⟨i, h1⟩ else 0
    left_inv := by
      intro x
      funext i
      dsimp only
      split_ifs with h0 h1
      · exact ZMod.intCast_zmod_cast _
      · rfl
      · have hi : data.diagonal i = 1 := by omega
        haveI : Subsingleton (ZMod (data.diagonal i)) := hi ▸ inferInstance
        exact Subsingleton.elim _ _
    right_inv := by
      intro x
      apply Prod.ext
      · funext i
        simp [i.property]
      · funext i
        have hi : data.diagonal i.val ≠ 0 := by have := i.property; omega
        simp [hi, i.property]
    map_add' := by
      intro x y
      apply Prod.ext
      · funext i
        simp [i.property]
      · rfl }

variable (h : data.Valid W)

include h

@[simp] lemma normalize_representative (x : data.Coordinates) :
    data.normalize (data.representative x) = x := by
  ext i
  simp [normalize_apply, representative, Matrix.mulVec_mulVec, h.1]

lemma normalize_boundary (x : Fin a → ℤ) : data.normalize (W *ᵥ x) = 0 := by
  ext i
  rw [normalize_apply, Matrix.mulVec_mulVec, h.2.2.1, ← Matrix.mulVec_mulVec]
  simp [Matrix.mulVec_diagonal]

/-- Every vector differs from its canonical representative by a witnessed original relation. -/
lemma decompose (x : Fin b → ℤ) :
    W *ᵥ data.preimage x + data.representative (data.normalize x) = x := by
  have hd : ∀ i, (data.diagonal i : ℤ) *
      (((data.coordinates *ᵥ x) i - ZMod.cast (data.normalize x i)) / data.diagonal i) =
      (data.coordinates *ᵥ x) i - ZMod.cast (data.normalize x i) :=
    fun i => Int.mul_ediv_cancel' (residue_sub_dvd (data.diagonal i) _)
  simp only [preimage, representative, Matrix.mulVec_mulVec, h.2.2.2.1]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_add]
  calc _ = data.representatives *ᵥ (data.coordinates *ᵥ x) := by
         congr 1
         ext i
         simp only [Pi.add_apply, Matrix.mulVec_diagonal, hd, sub_add_cancel]
       _ = x := by rw [Matrix.mulVec_mulVec, h.2.1, Matrix.one_mulVec]

/-- Vanishing cyclic coordinates are equivalent to the computed preimage equation. -/
lemma normalize_eq_zero_iff (x : Fin b → ℤ) :
    data.normalize x = 0 ↔ W *ᵥ data.preimage x = x := by
  constructor
  · intro hx
    have hd := data.decompose W h x
    rw [hx, data.representative_zero, add_zero] at hd
    exact hd
  · intro hx
    rw [← hx]
    exact data.normalize_boundary W h _

/-- Canonical normalization descends to the quotient by the original relations. -/
def quotientNormalize : ((Fin b → ℤ) ⧸ LinearMap.range W.mulVecLin) →ₗ[ℤ]
    data.Coordinates :=
  (LinearMap.range W.mulVecLin).liftQ data.normalize (by
    rintro _ ⟨x, rfl⟩
    exact data.normalize_boundary W h x)

@[simp] lemma quotientNormalize_mk (x : Fin b → ℤ) :
    data.quotientNormalize W h (Submodule.Quotient.mk x) = data.normalize x := rfl

/-- The verified integral presentation is equivalent to its cyclic coordinate model. -/
def quotientEquiv : ((Fin b → ℤ) ⧸ LinearMap.range W.mulVecLin) ≃ₗ[ℤ]
    data.Coordinates where
  toLinearMap := data.quotientNormalize W h
  invFun x := Submodule.Quotient.mk (data.representative x)
  left_inv x := by
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      apply (Submodule.Quotient.eq _).mpr
      refine ⟨-(data.preimage x), ?_⟩
      change W *ᵥ (-data.preimage x) = data.representative (data.normalize x) - x
      rw [Matrix.mulVec_neg, eq_sub_iff_add_eq]
      simpa using (congrArg (fun z => -(W *ᵥ data.preimage x) + z)
        (data.decompose W h x)).symm
  right_inv := data.normalize_representative W h

end SmithPresentationData

end ComputableCohomology
