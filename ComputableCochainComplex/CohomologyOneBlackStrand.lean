/-
Copyright (c) 2026 Annie Yao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Annie Yao
-/
module

public import ComputableCochainComplex.CohomologyGraded
public import KLRW.OneBlackStrand

/-!
# Homogeneous coordinates for the one-black-strand test category

A minimal strand from position `X` to position `Y` has degree `|X-Y|`; each dot has degree
two. The existing composition shift is checked against this convention. Every homogeneous
piece is given executable zero- or one-coordinate bases over `R`. This is a test adapter;
it makes no claim about normal forms in the general quotient-defined KLRW category.
-/

@[expose] public section

namespace ComputableCohomology.OneBlackStrand

open CategoryTheory AInfinityTheory

variable {R : Type*} [CommRing R] {n : ℕ}
  (X Y Z : KLRWCategory n R)

/-- Number of crossings in the minimal strand between two positions. -/
def crossingDegree : ℕ :=
  max X.positioning.val Y.positioning.val - min X.positioning.val Y.positioning.val

/-- Internal degree of a minimal strand with `k` dots. -/
def degree (k : ℕ) : ℤ := (crossingDegree X Y : ℤ) + 2 * (k : ℤ)

omit [CommRing R] in
/-- The existing composition shift makes internal degrees additive. -/
lemma degree_comp (i j : ℕ) :
    degree X Z (i + j + compShift X Y Z) = degree X Y i + degree Y Z j := by
  unfold degree crossingDegree compShift
  omega

/-- The existing strand coefficients give the Hom groups their pointwise scalar action. -/
instance homModule [DecidableEq R] : Module R (X ⟶ Y) := inferInstanceAs (Module R (StrandSpace R))

/-- Homogeneous strands are those with no coefficients outside the indicated degree. -/
def piece (q : ℤ) : Submodule R (StrandSpace R) where
  carrier := {f | ∀ k, degree X Y k ≠ q → f k = 0}
  zero_mem' := fun _ _ => rfl
  add_mem' := fun hf hg k hk => by
    simp only [DFinsupp.add_apply, hf k hk, hg k hk, add_zero]
  smul_mem' := fun r f hf k hk => by
    change r * f k = 0
    rw [hf k hk, mul_zero]

/-- The only possible dot index for the requested internal degree. -/
def dotIndex (q : ℤ) : ℕ := ((q - crossingDegree X Y) / 2).toNat

omit [CommRing R] in
lemma dotIndex_of_degree {q : ℤ} {k : ℕ} (h : degree X Y k = q) : dotIndex X Y q = k := by
  unfold dotIndex degree at *
  omega

/-- Every homogeneous strand is a single coefficient at its only possible dot index. -/
lemma eq_single {q : ℤ} (f : piece X Y q) :
    f.val = DFinsupp.single (dotIndex X Y q) (f.val (dotIndex X Y q)) := by
  ext k
  by_cases hk : k = dotIndex X Y q
  · subst k
    simp
  · rw [DFinsupp.single_eq_of_ne hk]
    exact f.property k (fun h => hk (dotIndex_of_degree X Y h).symm)

lemma single_mem (q : ℤ) (k : ℕ) (r : R) (hk : degree X Y k = q) :
    DFinsupp.single k r ∈ piece X Y q := by
  intro j hj
  exact DFinsupp.single_eq_of_ne (fun h => hj (h.symm ▸ hk))

/-- Read the one possible coefficient, with inverse given by the original strand diagram. -/
def coefficientEquiv (q : ℤ) (h : degree X Y (dotIndex X Y q) = q) :
    piece X Y q ≃ₗ[R] R where
  toFun f := f.val (dotIndex X Y q)
  invFun r := ⟨DFinsupp.single (dotIndex X Y q) r, single_mem X Y q _ r h⟩
  left_inv f := Subtype.ext (eq_single X Y f).symm
  right_inv _ := DFinsupp.single_eq_same
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma eq_zero_of_inadmissible (q : ℤ) (h : degree X Y (dotIndex X Y q) ≠ q)
    (f : piece X Y q) : f = 0 := by
  apply Subtype.ext
  rw [eq_single X Y f, f.property _ h, DFinsupp.single_zero]
  rfl

/-- The homogeneous piece has one coordinate exactly when a nonnegative dot index exists. -/
def size (q : ℤ) : ℕ := if degree X Y (dotIndex X Y q) = q then 1 else 0

/-- Certified finite coordinates for every internal degree, including inadmissible degrees. -/
def coordinates (q : ℤ) : piece X Y q ≃ₗ[R] (Fin (size X Y q) → R) := by
  by_cases h : degree X Y (dotIndex X Y q) = q
  · exact ((coefficientEquiv X Y q h).trans (LinearEquiv.funUnique (Fin 1) R R).symm).trans
      (LinearEquiv.funCongrLeft R R (finCongr (show size X Y q = 1 from if_pos h)))
  · haveI : Subsingleton (piece X Y q) := ⟨fun f g =>
      (eq_zero_of_inadmissible X Y q h f).trans (eq_zero_of_inadmissible X Y q h g).symm⟩
    haveI : IsEmpty (Fin (size X Y q)) :=
      ⟨fun i => Fin.elim0 (Fin.cast (show size X Y q = 0 from if_neg h) i)⟩
    exact LinearEquiv.ofSubsingleton _ _

variable [DecidableEq R]

/-- Composition of individual strand diagrams follows the existing convolution rule exactly. -/
lemma single_comp_single (i j : ℕ) (r s : R) :
    CategoryStruct.comp (X := X) (Y := Y) (Z := Z)
      (DFinsupp.single i r) (DFinsupp.single j s) =
      DFinsupp.single (i + j + compShift X Y Z) (r * s) := by
  change (DFinsupp.single i r : StrandSpace R).sum (fun k a =>
    (DFinsupp.single j s : StrandSpace R).sum (fun l b =>
      (a * b) • StrandSpace.dots R (k + l + compShift X Y Z))) = _
  rw [DFinsupp.sum_single_index (by simp)]
  rw [DFinsupp.sum_single_index (by simp)]
  simp [StrandSpace.dots, ← DFinsupp.single_smul]

/-- The certified homogeneous submodules are closed under the original diagram composition. -/
lemma comp_mem {p q : ℤ} (f : piece X Y p) (g : piece Y Z q) :
    CategoryStruct.comp (X := X) (Y := Y) (Z := Z) f.val g.val ∈ piece X Z (p + q) := by
  by_cases hp : degree X Y (dotIndex X Y p) = p
  · by_cases hq : degree Y Z (dotIndex Y Z q) = q
    · rw [eq_single X Y f, eq_single Y Z g, single_comp_single]
      exact single_mem X Z _ _ _ (by rw [degree_comp, hp, hq])
    · have hg : g.val = 0 := congrArg Subtype.val (eq_zero_of_inadmissible Y Z q hq g)
      rw [hg, Limits.comp_zero]
      exact (piece X Z (p + q)).zero_mem
  · have hf : f.val = 0 := congrArg Subtype.val (eq_zero_of_inadmissible X Y p hp f)
    rw [hf, Limits.zero_comp]
    exact (piece X Z (p + q)).zero_mem

/-- The one-black-strand model supplies the complete graded-coordinate input contract. -/
def gradedCoordinates : GradedHomCoordinates R (KLRWCategory n R) where
  piece := piece
  size := size
  coordinates := coordinates
  compose X Y Z p q x y := coordinates X Z (p + q)
    ⟨CategoryStruct.comp (X := X) (Y := Y) (Z := Z)
      ((coordinates X Y p).symm x).val ((coordinates Y Z q).symm y).val,
      comp_mem X Y Z _ _⟩
  decode_compose X _Y Z p q _x _y :=
    congrArg Subtype.val ((coordinates X Z (p + q)).symm_apply_apply _)

/-- Scalar multiplication of strands agrees with postcomposition by the scalar identity. -/
lemma comp_smul_id (f : StrandSpace R) (r : R) :
    CategoryStruct.comp (X := X) (Y := Y) (Z := Y) f (r • 𝟙 Y) = r • f := by
  change f.sum (fun i a => (r • StrandSpace.dots R 0).sum (fun j b =>
    (a * b) • StrandSpace.dots R (i + j + compShift X Y Y))) = r • f
  simp only [StrandSpace.dots, ← DFinsupp.single_smul, smul_eq_mul, mul_one]
  conv_lhs =>
    arg 2
    ext i a
    rw [DFinsupp.sum_single_index (by simp)]
  simp only [compShift_self_right, add_zero]
  conv_rhs => rw [← DFinsupp.sum_single (f := f)]
  rw [DFinsupp.smul_sum]
  congr 1
  funext i a
  simp [← DFinsupp.single_smul, mul_comm]

/-- Local module complex at degree one of postcomposition by `r • id`, before fixing a grading. -/
def scalarAmbient (r : R) : ShortComplex (ModuleCat R) :=
  ShortComplex.moduleCatMk (r • (LinearMap.id : StrandSpace R →ₗ[R] StrandSpace R))
    (0 : StrandSpace R →ₗ[R] (Fin 0 → R)) (by simp)

/-- The ambient differential is the original diagrammatic operation, not a specialization. -/
lemma scalarAmbient_apply (r : R) (f : StrandSpace R) :
    (scalarAmbient r).f.hom f =
      CategoryStruct.comp (X := X) (Y := Y) (Z := Y) f (r • 𝟙 Y) :=
  (comp_smul_id X Y f r).symm

/-- Restrict the two-term scalar complex at its target, with equal shifts on the two terms. -/
def scalarPiece (r : R) (q shift : ℤ) : ShortComplex (ModuleCat R) :=
  restrictAtDegree (scalarAmbient r) (piece X X) (piece X X) (fun _ => ⊤)
    q shift shift 0
    (fun _ hx => (piece X X (q + shift)).smul_mem r hx)
    (fun _ _ => Submodule.mem_top)

/-- The homogeneous scalar complex has the certified zero- or one-coordinate bases. -/
def scalarCoordinates (r : R) (q shift : ℤ) : LocalCoordinates (scalarPiece X r q shift) where
  sourceSize := size X X (q + shift)
  middleSize := size X X (q + shift)
  targetSize := 0
  source := coordinates X X (q + shift)
  middle := coordinates X X (q + shift)
  target := Submodule.topEquiv

end ComputableCohomology.OneBlackStrand
