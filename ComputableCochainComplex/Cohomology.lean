/-
Copyright (c) 2026 Annie Yao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Annie Yao
-/
module

public import ComputableCochainComplex.ModuleAlgorithms
public import ComputableCochainComplex.FiniteFreeCochainComplex
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Certified cohomology presentations and induced maps

For consecutive differential matrices `A`, `B`, compute kernel generators `K`, their syzygies
`S`, and a boundary lift `T` with `K * T = A`. The matrix `[S | T]` presents cohomology.
Generator lifts also compute induced maps. Both constructions are compared with Mathlib
homology and accept either backend computations or individual certificates.

The degree adapters use ordinary cochain complexes with `FiniteFreeComplex`.
They need no finite support assumption. Kernels and cohomology need not be free.
-/

@[expose] public section

namespace ComputableCohomology

open CategoryTheory
open scoped Matrix

section Presentations

variable {R : Type*} [CommRing R] {a b c : ℕ}

/-- Interpret consecutive matrices in Mathlib's existing category of short complexes.
This shared interpretation avoids introducing a second notion of a complex. -/
def matrixShortComplex (A : Matrix (Fin b) (Fin a) R) {B : Matrix (Fin c) (Fin b) R}
    (hBA : B * A = 0) : ShortComplex (ModuleCat R) :=
  ShortComplex.moduleCatMk A.mulVecLin B.mulVecLin
    (by rw [← Matrix.mulVecLin_mul, hBA, Matrix.mulVecLin_zero])

/-- The computed data for local cohomology. Storing the lifted boundary matrix avoids
repeating solver calls and records the equation relating it to the original differential. -/
structure CohomologyPresentation (A : Matrix (Fin b) (Fin a) R)
    (B : Matrix (Fin c) (Fin b) R) where
  /-- Complete cocycle generators in the original chain term. -/
  kernel : Matrix.KernelGenerators B
  /-- Complete syzygies of the cocycle generators; these supply intrinsic relations. -/
  relations : Matrix.KernelGenerators kernel.generators
  /-- Coordinates of each original boundary generator in the cocycle generators. -/
  boundaries : Matrix (Fin kernel.size) (Fin a) R
  /-- Lifted boundaries reconstruct the given differential, preserving original coordinates. -/
  generators_mul_boundaries : kernel.generators * boundaries = A

/-- Compute a finite cohomology presentation using only the caller's two algorithms.
The square-zero proof guarantees that each incoming column can be lifted through the kernel. -/
def computeCohomology [EffectiveModuleAlgorithms R]
    (A : Matrix (Fin b) (Fin a) R) (B : Matrix (Fin c) (Fin b) R) (hBA : B * A = 0) :
    CohomologyPresentation A B :=
  let k := EffectiveModuleAlgorithms.syzygies B
  let s := EffectiveModuleAlgorithms.syzygies k.generators
  let columns := fun j => k.lift ⟨fun i => A i j, by
    ext i
    exact congrFun (congrFun hBA i) j⟩
  { kernel := k
    relations := s
    boundaries := fun i j => (columns j).val i
    generators_mul_boundaries := by
      ext i j
      exact congrFun (columns j).property i }

namespace CohomologyPresentation

variable {A : Matrix (Fin b) (Fin a) R} {B : Matrix (Fin c) (Fin b) R}
  (p : CohomologyPresentation A B)

/-- Intrinsic generator relations and lifted boundaries together present cohomology.
Including both blocks is essential when cocycle generators are dependent. -/
def relationMatrix : Matrix (Fin p.kernel.size) (Fin (p.relations.size + a)) R :=
  (Matrix.fromCols p.relations.generators p.boundaries).submatrix id finSumFinEquiv.symm

/-- The output module is Mathlib's quotient by the computed relation matrix. A named alias
retains the presentation parameter for typeclass inference; no freeness is asserted. -/
def PresentedModule := (Fin p.kernel.size → R) ⧸ LinearMap.range p.relationMatrix.mulVecLin
  deriving AddCommGroup, Module R

/-- The explicit matrix quotient satisfies Mathlib's finite-presentation predicate.
This exposes the standard abstract property without creating a second module-presentation theory. -/
instance : Module.FinitePresentation R p.PresentedModule := by
  apply Module.finitePresentation_of_surjective (LinearMap.range p.relationMatrix.mulVecLin).mkQ
    (Submodule.mkQ_surjective _)
  rw [Submodule.ker_mkQ]
  exact Submodule.fg_range _

/-- Presentation relations are precisely generator vectors representing original boundaries.
This proves both directions needed to identify the computed quotient with cohomology. -/
lemma relation_iff (x : Fin p.kernel.size → R) :
    (∃ z, p.relationMatrix *ᵥ z = x) ↔ ∃ y, A *ᵥ y = p.kernel.generators *ᵥ x := by
  constructor
  · rintro ⟨z, rfl⟩
    have hz : p.kernel.generators *ᵥ
        (p.relations.generators *ᵥ ((z ∘ finSumFinEquiv) ∘ Sum.inl)) = 0 := by
      change _ ∈ LinearMap.ker p.kernel.generators.mulVecLin
      rw [← p.relations.range_eq_ker]
      exact ⟨_, rfl⟩
    refine ⟨(z ∘ finSumFinEquiv) ∘ Sum.inr, ?_⟩
    rw [relationMatrix, Matrix.submatrix_mulVec_equiv, Equiv.symm_symm, Function.comp_id,
      Matrix.fromCols_mulVec, Matrix.mulVec_add, hz, zero_add,
      Matrix.mulVec_mulVec, p.generators_mul_boundaries]
  · rintro ⟨y, hy⟩
    have hz : p.kernel.generators *ᵥ (x - p.boundaries *ᵥ y) = 0 := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, p.generators_mul_boundaries, hy, sub_self]
    obtain ⟨w, hw⟩ := p.relations.range_eq_ker.symm ▸
      (show x - p.boundaries *ᵥ y ∈ LinearMap.ker p.kernel.generators.mulVecLin from hz)
    refine ⟨Sum.elim w y ∘ finSumFinEquiv.symm, ?_⟩
    rw [relationMatrix, Matrix.submatrix_mulVec_equiv]
    simp only [Equiv.symm_symm, Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id]
    rw [Matrix.fromCols_mulVec_sumElim, show p.relations.generators *ᵥ w = _ from hw,
      sub_add_cancel]

variable (hBA : B * A = 0)

/-- Interpret presentation classes in the concrete kernel quotient. Its linear action
comes directly from the generator matrix, independently of how the algorithms chose it. -/
def toCyclesQuotient : p.PresentedModule →ₗ[R]
    (LinearMap.ker B.mulVecLin ⧸
      LinearMap.range (matrixShortComplex A hBA).moduleCatToCycles) :=
  (LinearMap.range p.relationMatrix.mulVecLin).mapQ _ p.kernel.toKernel (by
    rintro x ⟨z, hz⟩
    obtain ⟨y, hy⟩ := (p.relation_iff x).mp ⟨z, hz⟩
    exact ⟨y, Subtype.ext hy⟩)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The computed presentation is exactly the cocycle quotient. Classical inversion is
confined to this comparison; representative computations use the supplied solver. -/
noncomputable def cyclesQuotientEquiv : p.PresentedModule ≃ₗ[R]
    (LinearMap.ker B.mulVecLin ⧸
      LinearMap.range (matrixShortComplex A hBA).moduleCatToCycles) :=
  LinearEquiv.ofBijective (p.toCyclesQuotient hBA) (by
    constructor
    · intro x y h
      induction x using Submodule.Quotient.induction_on with
      | _ x =>
        induction y using Submodule.Quotient.induction_on with
        | _ y =>
          apply (Submodule.Quotient.eq _).mpr
          obtain ⟨z, hz⟩ := (Submodule.Quotient.eq _).mp h
          apply (p.relation_iff (x - y)).mpr
          refine ⟨z, ?_⟩
          have hz' := congrArg Subtype.val hz
          change A *ᵥ z = p.kernel.generators *ᵥ x - p.kernel.generators *ᵥ y at hz'
          simpa only [Matrix.mulVec_sub] using hz'
    · intro x
      induction x using Submodule.Quotient.induction_on with
      | _ x =>
        have hx : x.val ∈ LinearMap.range p.kernel.generators.mulVecLin := by
          rw [p.kernel.range_eq_ker]
          exact x.property
        obtain ⟨y, hy⟩ := hx
        refine ⟨Submodule.Quotient.mk y, ?_⟩
        exact congrArg Submodule.Quotient.mk (Subtype.ext hy))

/-- Identify the computed module with Mathlib homology, so all algorithm implementations
share the same semantic correctness theorem. -/
noncomputable def homologyIso :
    (matrixShortComplex A hBA).homology ≅ ModuleCat.of R p.PresentedModule :=
  (matrixShortComplex A hBA).moduleCatHomologyIso ≪≫ (p.cyclesQuotientEquiv hBA).symm.toModuleIso

/-- Compute a cocycle's presentation class without claiming a canonical vector of coordinates.
Different lifts agree modulo the relation matrix, as proved by the quotient comparison. -/
def classOf [EffectiveModuleAlgorithms R] (x : LinearMap.ker B.mulVecLin) : p.PresentedModule :=
  Submodule.Quotient.mk (p.kernel.lift x).val

/-- The executable class constructor represents the supplied cocycle in the actual quotient.
This is the correctness guarantee for using computed classes in subsequent maps. -/
lemma toCyclesQuotient_classOf [EffectiveModuleAlgorithms R] (x : LinearMap.ker B.mulVecLin) :
    p.toCyclesQuotient hBA (p.classOf x) = Submodule.Quotient.mk x :=
  congrArg Submodule.Quotient.mk (Subtype.ext (p.kernel.lift x).property)

/-- A computed class vanishes exactly for original boundaries. Together with the
lifting operation, this produces original-coordinate witnesses when vanishing is known. -/
lemma classOf_eq_zero_iff [EffectiveModuleAlgorithms R]
    (x : LinearMap.ker B.mulVecLin) :
    p.classOf x = 0 ↔ x.val ∈ LinearMap.range A.mulVecLin := by
  change (Submodule.Quotient.mk (p.kernel.lift x).val :
    (Fin p.kernel.size → R) ⧸ LinearMap.range p.relationMatrix.mulVecLin) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  change (∃ z, p.relationMatrix *ᵥ z = (p.kernel.lift x).val) ↔ ∃ y, A *ᵥ y = x.val
  rw [p.relation_iff, (p.kernel.lift x).property]

end CohomologyPresentation

end Presentations

section InducedMaps

variable {R : Type*} [CommRing R]
  {S T : ShortComplex (ModuleCat R)}

/-- A map of short complexes restricts its middle component to the concrete kernels. -/
def cyclesLinearMap (φ : S ⟶ T) : LinearMap.ker S.g.hom →ₗ[R] LinearMap.ker T.g.hom :=
  (φ.τ₂.hom.comp (LinearMap.ker S.g.hom).subtype).codRestrict _ (fun x => by
    change T.g.hom (φ.τ₂.hom x.val) = 0
    have h := congrArg (fun f => f.hom x.val) φ.comm₂₃
    change T.g.hom (φ.τ₂.hom x.val) = φ.τ₃.hom (S.g.hom x.val) at h
    rw [show S.g.hom x.val = 0 from x.property, map_zero] at h
    exact h)

/-- Boundaries map to boundaries, which is needed to descend to the kernel quotient. -/
lemma cyclesLinearMap_boundary (φ : S ⟶ T) (x : S.X₁) :
    cyclesLinearMap φ (S.moduleCatToCycles x) = T.moduleCatToCycles (φ.τ₁.hom x) := by
  apply Subtype.ext
  exact (congrArg (fun f => f.hom x) φ.comm₁₂).symm

/-- The executable map induced on Mathlib's concrete kernel quotients. -/
def quotientLinearMap (φ : S ⟶ T) :
    (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) →ₗ[R]
      (LinearMap.ker T.g.hom ⧸ LinearMap.range T.moduleCatToCycles) :=
  (LinearMap.range S.moduleCatToCycles).mapQ (LinearMap.range T.moduleCatToCycles)
    (cyclesLinearMap φ) (by
      rintro _ ⟨x, rfl⟩
      exact ⟨φ.τ₁.hom x, (cyclesLinearMap_boundary φ x).symm⟩)

/-- The explicit quotient map agrees with Mathlib's induced homology map. -/
lemma quotientLinearMap_naturality (φ : S ⟶ T) :
    ShortComplex.homologyMap φ ≫ T.moduleCatHomologyIso.hom =
      S.moduleCatHomologyIso.hom ≫ ModuleCat.ofHom (quotientLinearMap φ) :=
  (show ShortComplex.LeftHomologyMapData φ S.moduleCatLeftHomologyData
      T.moduleCatLeftHomologyData from
    { φK := ModuleCat.ofHom (cyclesLinearMap φ)
      φH := ModuleCat.ofHom (quotientLinearMap φ)
      commi := rfl
      commf' := by
        apply ModuleCat.hom_ext
        ext x
        exact cyclesLinearMap_boundary φ x
      commπ := rfl }).homologyMap_comm

namespace CohomologyPresentation

variable {a b c a' b' c' : ℕ}
  {A : Matrix (Fin b) (Fin a) R} {B : Matrix (Fin c) (Fin b) R} {hBA : B * A = 0}
  {D : Matrix (Fin b') (Fin a') R} {E : Matrix (Fin c') (Fin b') R} {hED : E * D = 0}
  (k : CohomologyPresentation A B) (l : CohomologyPresentation D E)
  (φ : matrixShortComplex A hBA ⟶ matrixShortComplex D hED)

/-- Lift the images of the source generators column by column. This computes a matrix on
generator coefficients without requiring a linear or unique choice of cocycle lifts. -/
def mapMatrix [EffectiveModuleAlgorithms R] :
    Matrix (Fin l.kernel.size) (Fin k.kernel.size) R := fun i j =>
  (l.kernel.lift (cyclesLinearMap φ ⟨fun r => k.kernel.generators r j, by
    change (fun r => k.kernel.generators r j) ∈ LinearMap.ker B.mulVecLin
    rw [← k.kernel.range_eq_ker]
    refine ⟨Pi.single j 1, ?_⟩
    exact Matrix.mulVec_single_one _ j⟩)).val i

/-- The computed columns represent the actual cochain-map images. This matrix equation
is the finite compatibility witness needed to descend the map to cohomology. -/
lemma generators_mul_mapMatrix [EffectiveModuleAlgorithms R] :
    l.kernel.generators * k.mapMatrix l φ = LinearMap.toMatrix' φ.τ₂.hom * k.kernel.generators := by
  ext i j
  exact (congrFun (l.kernel.lift _).property i).trans
    (congrFun (LinearMap.toMatrix'_mulVec φ.τ₂.hom (fun r => k.kernel.generators r j)) i).symm

variable (U : Matrix (Fin l.kernel.size) (Fin k.kernel.size) R)
  (hU : l.kernel.generators * U = LinearMap.toMatrix' φ.τ₂.hom * k.kernel.generators)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
include hU in
/-- A certified generator matrix represents the cochain map on every vector. This finite
equation is sufficient for validating externally computed map matrices. -/
lemma generators_mulVec_mulVec (x : Fin k.kernel.size → R) :
    l.kernel.generators *ᵥ (U *ᵥ x) = φ.τ₂.hom (k.kernel.generators *ᵥ x) := by
  rw [Matrix.mulVec_mulVec, hU, ← Matrix.mulVec_mulVec,
    LinearMap.toMatrix'_mulVec]
  rfl

/-- Descend any certified generator matrix to the presentation quotient, without a backend.
Relations are checked using their boundary meaning, so redundant generators cause no ambiguity. -/
def mapOfMatrix : k.PresentedModule →ₗ[R] l.PresentedModule :=
  (LinearMap.range k.relationMatrix.mulVecLin).mapQ _
    U.mulVecLin (by
      rintro x ⟨z, hz⟩
      obtain ⟨y, hy⟩ := (k.relation_iff x).mp ⟨z, hz⟩
      apply (l.relation_iff _).mpr
      refine ⟨φ.τ₁.hom y, ?_⟩
      change D *ᵥ φ.τ₁.hom y = l.kernel.generators *ᵥ (U *ᵥ x)
      rw [k.generators_mulVec_mulVec l φ U hU, ← hy]
      exact congrArg (fun f => f.hom y) φ.comm₁₂)

/-- The executable presentation map commutes with the concrete kernel-quotient map.
This bridges computation to the existing Mathlib naturality theorem. -/
lemma toCyclesQuotient_naturality :
    (quotientLinearMap φ).comp (k.toCyclesQuotient hBA) =
      (l.toCyclesQuotient hED).comp (k.mapOfMatrix l φ U hU) := by
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    apply congrArg Submodule.Quotient.mk
    exact Subtype.ext (k.generators_mulVec_mulVec l φ U hU x).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The computed quotient map agrees with Mathlib homology. This is the correctness
statement reused to obtain functoriality, and to validate certificate-only computations. -/
lemma mapOfMatrix_naturality :
    ShortComplex.homologyMap φ ≫ (l.homologyIso hED).hom =
      (k.homologyIso hBA).hom ≫ ModuleCat.ofHom (k.mapOfMatrix l φ U hU) := by
  simp only [homologyIso, Iso.trans_hom, ← Category.assoc]
  rw [ComputableCohomology.quotientLinearMap_naturality]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  let y := (matrixShortComplex A hBA).moduleCatHomologyIso.hom.hom x
  apply (l.cyclesQuotientEquiv hED).injective
  change (l.cyclesQuotientEquiv hED)
      ((l.cyclesQuotientEquiv hED).symm ((quotientLinearMap φ) y)) =
    (l.cyclesQuotientEquiv hED)
      ((k.mapOfMatrix l φ U hU) ((k.cyclesQuotientEquiv hBA).symm y))
  rw [LinearEquiv.apply_symm_apply]
  change (quotientLinearMap φ) y =
    ((l.toCyclesQuotient hED).comp (k.mapOfMatrix l φ U hU))
      ((k.cyclesQuotientEquiv hBA).symm y)
  rw [← k.toCyclesQuotient_naturality l φ U hU]
  change (quotientLinearMap φ) y = (quotientLinearMap φ)
    ((k.cyclesQuotientEquiv hBA) ((k.cyclesQuotientEquiv hBA).symm y))
  rw [LinearEquiv.apply_symm_apply]

/-- Compute the quotient map using the backend's known-member lifts. The certificate-only
constructor handles the correctness proof, so backend and external computations share it. -/
def map [EffectiveModuleAlgorithms R] : k.PresentedModule →ₗ[R] l.PresentedModule :=
  k.mapOfMatrix l φ (k.mapMatrix l φ) (k.generators_mul_mapMatrix l φ)

/-- The automatically computed map has the same Mathlib comparison as any certified matrix.
This specializes the certificate theorem without duplicating its proof. -/
lemma map_naturality [EffectiveModuleAlgorithms R] :
    ShortComplex.homologyMap φ ≫ (l.homologyIso hED).hom =
      (k.homologyIso hBA).hom ≫ ModuleCat.ofHom (k.map l φ) :=
  k.mapOfMatrix_naturality l φ (k.mapMatrix l φ) (k.generators_mul_mapMatrix l φ)

/-- Acting on a computed cocycle class agrees with applying the original cochain map
and then constructing its class. This links the executable input and induced-map APIs. -/
lemma map_classOf [EffectiveModuleAlgorithms R] (x : LinearMap.ker B.mulVecLin) :
    k.map l φ (k.classOf x) = l.classOf (cyclesLinearMap φ x) := by
  apply (l.cyclesQuotientEquiv hED).injective
  change ((l.toCyclesQuotient hED).comp
    (k.mapOfMatrix l φ (k.mapMatrix l φ) (k.generators_mul_mapMatrix l φ))) (k.classOf x) = _
  rw [← k.toCyclesQuotient_naturality l φ (k.mapMatrix l φ) (k.generators_mul_mapMatrix l φ),
    LinearMap.comp_apply, k.toCyclesQuotient_classOf hBA]
  exact (l.toCyclesQuotient_classOf hED (cyclesLinearMap φ x)).symm

/-- Identity holds on cohomology even when lifting a generator chooses different
coefficients. The Mathlib comparison proves it without imposing a normal form on lifts. -/
@[simp] lemma map_id [EffectiveModuleAlgorithms R] :
    k.map k (𝟙 (matrixShortComplex A hBA)) = LinearMap.id := by
  have h := k.map_naturality k (𝟙 (matrixShortComplex A hBA))
  have h' := congrArg (fun f => (k.homologyIso hBA).inv ≫ f) h
  simpa using congrArg ModuleCat.Hom.hom h'.symm

variable {a'' b'' c'' : ℕ} {F : Matrix (Fin b'') (Fin a'') R}
  {G : Matrix (Fin c'') (Fin b'') R} {hGF : G * F = 0}
  (m : CohomologyPresentation F G)
  (ψ : matrixShortComplex D hED ⟶ matrixShortComplex F hGF)

/-- Composition holds after passing to relations; equality of the chosen generator
matrices is neither needed nor generally true. -/
lemma map_comp [EffectiveModuleAlgorithms R] : k.map m (φ ≫ ψ) = (l.map m ψ).comp (k.map l φ) := by
  suffices h : ModuleCat.ofHom (k.map m (φ ≫ ψ)) =
      ModuleCat.ofHom (k.map l φ) ≫ ModuleCat.ofHom (l.map m ψ) from
    congrArg ModuleCat.Hom.hom h
  apply (cancel_epi (k.homologyIso hBA).hom).mp
  rw [← k.map_naturality m (φ ≫ ψ), ShortComplex.homologyMap_comp]
  rw [Category.assoc, l.map_naturality m ψ, ← Category.assoc,
    k.map_naturality l φ, Category.assoc]

end CohomologyPresentation

end InducedMaps

end ComputableCohomology

namespace CochainComplex

open CategoryTheory
open scoped Matrix

section Presentations

variable {R : Type*} [CommRing R] (C : CochainComplex (ModuleCat R) ℤ)
  [FiniteFreeComplex C] (n : ℤ)

/-- The incoming differential in the chosen coordinates of the inherited module complex. -/
def incoming : Matrix (Fin (C.size n)) (Fin (C.size (n - 1))) R :=
  C.dMatrix (n - 1) n

/-- Matrix coordinates evaluate to the original incoming map, allowing local calculations. -/
@[simp] lemma incoming_mulVec (x : Fin (C.size (n - 1)) → R) :
    C.incoming n *ᵥ x =
      C.coordinates n ((C.d (n - 1) n).hom ((C.coordinates (n - 1)).symm x)) :=
  C.dMatrix_mulVec _ _ x

/-- Consecutive coordinate matrices still square to zero, as required by the local input. -/
lemma d_mul_incoming : C.dMatrix n (n + 1) * C.incoming n = 0 :=
  C.dMatrix_mul_dMatrix _ _ _

/-- The local matrices describe exactly the three relevant terms of the original complex. -/
def localShortComplexIso :
    C.sc' (n - 1) n (n + 1) ≅
      ComputableCohomology.matrixShortComplex (C.incoming n) (C.d_mul_incoming n) :=
  ShortComplex.isoMk (C.coordinates (n - 1)).toModuleIso (C.coordinates n).toModuleIso
    (C.coordinates (n + 1)).toModuleIso
    (by
      apply ModuleCat.hom_ext
      ext x
      exact C.dMatrix_coordinates _ _ x)
    (by
      apply ModuleCat.hom_ext
      ext x
      exact C.dMatrix_coordinates _ _ x)

/-- Cohomology at a degree depends only on its two adjacent differential matrices. -/
noncomputable def localHomologyIso :
    C.homology n ≅
      (ComputableCohomology.matrixShortComplex
        (C.incoming n) (C.d_mul_incoming n)).homology :=
  C.homologyIsoSc' (n - 1) n (n + 1) (by simp) (by simp) ≪≫
    ShortComplex.homologyMapIso (C.localShortComplexIso n)

/-- Compute at one degree of an ordinary complex with finite free coordinates. Its square-zero
proof supplies valid local input. No support bound or second complex datatype is needed. -/
def computeCohomology [EffectiveModuleAlgorithms R] :
    ComputableCohomology.CohomologyPresentation (C.incoming n) (C.dMatrix n (n + 1)) :=
  ComputableCohomology.computeCohomology
    (C.incoming n) (C.dMatrix n (n + 1)) (C.d_mul_incoming n)

/-- Transport a computed presentation to the requested degree of the original complex.
Only the two adjacent matrices are used; no boundedness assumption is required. -/
noncomputable def cohomologyPresentationIso
    (p : ComputableCohomology.CohomologyPresentation (C.incoming n) (C.dMatrix n (n + 1))) :
    C.homology n ≅ ModuleCat.of R p.PresentedModule :=
  C.localHomologyIso n ≪≫ p.homologyIso (C.d_mul_incoming n)

end Presentations

end CochainComplex

namespace HomologicalComplex.Hom

open CategoryTheory ComputableCohomology CochainComplex

variable {R : Type*} [CommRing R] {C D : CochainComplex (ModuleCat R) ℤ}
  [FiniteFreeComplex C] [FiniteFreeComplex D]

/-- Restrict an existing cochain map to the two differential matrices at a requested degree. -/
def localMap (f : C ⟶ D) (n : ℤ) :
    matrixShortComplex (C.incoming n) (C.d_mul_incoming n) ⟶
      matrixShortComplex (D.incoming n) (D.d_mul_incoming n) :=
  (C.localShortComplexIso n).inv ≫
    (HomologicalComplex.shortComplexFunctor' (ModuleCat R) (.up ℤ)
      (n - 1) n (n + 1)).map f ≫ (D.localShortComplexIso n).hom

/-- The local matrix comparison is natural in the original finite-free cochain map. -/
lemma localHomologyIso_naturality (f : C ⟶ D) (n : ℤ) :
    HomologicalComplex.homologyMap f n ≫ (D.localHomologyIso n).hom =
      (C.localHomologyIso n).hom ≫ ShortComplex.homologyMap (f.localMap n) := by
  have h := (HomologicalComplex.homologyFunctorIso' (ModuleCat R) (.up ℤ)
    (n - 1) n (n + 1) (by simp) (by simp)).hom.naturality f
  change HomologicalComplex.homologyMap f n ≫
      (D.homologyIsoSc' (n - 1) n (n + 1) _ _).hom =
    (C.homologyIsoSc' (n - 1) n (n + 1) _ _).hom ≫
      ShortComplex.homologyMap ((HomologicalComplex.shortComplexFunctor'
        (ModuleCat R) (.up ℤ) (n - 1) n (n + 1)).map f) at h
  simp only [localHomologyIso, Iso.trans_hom, ShortComplex.homologyMapIso_hom,
    localMap, ShortComplex.homologyMap_comp, ← Category.assoc]
  rw [h]
  simp [← ShortComplex.homologyMap_comp, Category.assoc]

/-- Compute the map between supplied presentations at one degree. Reusing the existing
local cochain map keeps the adapter independent of the ring's algorithms. -/
def cohomologyPresentationMap [EffectiveModuleAlgorithms R] (f : C ⟶ D) (n : ℤ)
    (p : CohomologyPresentation (C.incoming n) (C.dMatrix n (n + 1)))
    (q : CohomologyPresentation (D.incoming n) (D.dMatrix n (n + 1))) :=
  p.map q (f.localMap n)

/-- The degree adapter agrees with Mathlib's homology map on the original complexes;
this carries the local calculation through the existing coordinate interpretation. -/
lemma cohomologyPresentationMap_naturality [EffectiveModuleAlgorithms R]
    (f : C ⟶ D) (n : ℤ)
    (p : CohomologyPresentation (C.incoming n) (C.dMatrix n (n + 1)))
    (q : CohomologyPresentation (D.incoming n) (D.dMatrix n (n + 1))) :
    HomologicalComplex.homologyMap f n ≫
        (D.cohomologyPresentationIso n q).hom =
      (C.cohomologyPresentationIso n p).hom ≫
        ModuleCat.ofHom (f.cohomologyPresentationMap n p q) := by
  simp only [cohomologyPresentationIso, Iso.trans_hom, cohomologyPresentationMap]
  rw [← Category.assoc, f.localHomologyIso_naturality, Category.assoc,
    p.map_naturality q (f.localMap n), Category.assoc]

end HomologicalComplex.Hom
