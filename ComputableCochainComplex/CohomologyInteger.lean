/-
Copyright (c) 2026 Annie Yao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Annie Yao
-/
module

public import ComputableCochainComplex.CohomologyIntegerReduction
public import ComputableCochainComplex.CohomologyMap

/-!
# Certified integral cohomology

The integral backend uses the same kernel certificate and Mathlib comparison as the field
backend. Its model separates free integer coordinates from nontrivial cyclic factors, with
canonical representatives and executable boundary witnesses in the original coordinates.
Every successful result includes proofs; reduction or certificate failure is explicit.
-/

@[expose] public section

namespace ComputableCohomology

open CategoryTheory
open scoped Matrix

variable {a b c : ℕ}

/-- Certified integral cohomology, including a normalized Smith presentation of its relations. -/
structure IntegerCohomologyCertificate (A : Matrix (Fin b) (Fin a) ℤ)
    (B : Matrix (Fin c) (Fin b) ℤ) where
  /-- The matrices are consecutive differentials. -/
  square_zero : B * A = 0
  /-- An integral basis for the entire cocycle module. -/
  kernel : KernelCertificate B
  /-- Diagonal coordinates and witnesses for the boundary relations. -/
  quotient : SmithPresentationData a kernel.size
  /-- Every coordinate transformation and relation-module equation has been checked. -/
  valid : quotient.Valid (kernel.retraction * A)

namespace IntegerCohomologyCertificate

variable {A : Matrix (Fin b) (Fin a) ℤ} {B : Matrix (Fin c) (Fin b) ℤ}
  (result : IntegerCohomologyCertificate A B)

/-- The free integer summand and the nontrivial cyclic summands, omitting unit factors. -/
abbrev Model := result.quotient.Model

/-- Canonical class coordinates of an original-coordinate cocycle. -/
def normalize (x : Fin b → ℤ) : result.Model :=
  result.quotient.splitEquiv (result.quotient.normalize (result.kernel.retraction *ᵥ x))

/-- The chosen cocycle representing a free and torsion coordinate vector. -/
def representative (x : result.Model) : Fin b → ℤ :=
  result.kernel.inclusion *ᵥ
    result.quotient.representative (result.quotient.splitEquiv.symm x)

/-- Original-coordinate preimage of the boundary part removed by normalization. -/
def preimage (x : Fin b → ℤ) : Fin a → ℤ :=
  result.quotient.preimage (result.kernel.retraction *ᵥ x)

lemma representative_is_cocycle (x : result.Model) :
    B *ᵥ result.representative x = 0 := result.kernel.inclusion_mem_ker _

@[simp] lemma normalize_representative (x : result.Model) :
    result.normalize (result.representative x) = x := by
  unfold normalize representative
  rw [result.kernel.retraction_inclusion,
    result.quotient.normalize_representative _ result.valid, LinearEquiv.apply_symm_apply]

lemma normalize_boundary (x : Fin a → ℤ) : result.normalize (A *ᵥ x) = 0 := by
  unfold normalize
  rw [Matrix.mulVec_mulVec x result.kernel.retraction A,
    result.quotient.normalize_boundary _ result.valid, map_zero]

/-- Vanishing canonical coordinates are equivalent to the actual preimage equation. -/
lemma normalize_eq_zero_iff (x : Fin b → ℤ) (hx : B *ᵥ x = 0) :
    result.normalize x = 0 ↔ A *ᵥ result.preimage x = x := by
  rw [normalize, EmbeddingLike.map_eq_zero_iff]
  exact (result.quotient.normalize_eq_zero_iff _ result.valid _).trans
    (result.kernel.boundary_preimage_iff A result.square_zero x hx _)

/-- The integer boundary test is complete for every cocycle. -/
lemma boundary_iff (x : Fin b → ℤ) (hx : B *ᵥ x = 0) :
    (∃ y, A *ᵥ y = x) ↔ result.normalize x = 0 := by
  constructor
  · rintro ⟨y, rfl⟩
    exact result.normalize_boundary y
  · intro h
    exact ⟨result.preimage x, (result.normalize_eq_zero_iff x hx).mp h⟩

/-- Return an original-coordinate preimage together with its verified boundary equation. -/
def boundaryPreimage (x : Fin b → ℤ) (hx : B *ᵥ x = 0) :
    Option {y : Fin a → ℤ // A *ᵥ y = x} :=
  if h : result.normalize x = 0 then
    some ⟨result.preimage x, (result.normalize_eq_zero_iff x hx).mp h⟩ else none

/-- The presentation quotient is equivalent to the free and nontrivial torsion coordinates. -/
def quotientEquiv :
    ((Fin result.kernel.size → ℤ) ⧸ LinearMap.range (result.kernel.retraction * A).mulVecLin) ≃ₗ[ℤ]
      result.Model :=
  (result.quotient.quotientEquiv _ result.valid).trans result.quotient.splitEquiv

/-- The integral coordinates describe Mathlib's homology of the local complex. -/
noncomputable def homologyIso :
    (KernelCertificate.shortComplex A result.square_zero).homology ≅
      ModuleCat.of ℤ result.Model :=
  result.kernel.homologyIso A result.square_zero ≪≫ result.quotientEquiv.toModuleIso

variable {a' b' c' a'' b'' c'' : ℕ}
  {D : Matrix (Fin b') (Fin a') ℤ} {E : Matrix (Fin c') (Fin b') ℤ}
  {F : Matrix (Fin b'') (Fin a'') ℤ} {G : Matrix (Fin c'') (Fin b'') ℤ}
  (target : IntegerCohomologyCertificate D E) (next : IntegerCohomologyCertificate F G)
  (φ : KernelCertificate.shortComplex A result.square_zero ⟶
    KernelCertificate.shortComplex D target.square_zero)
  (ψ : KernelCertificate.shortComplex D target.square_zero ⟶
    KernelCertificate.shortComplex F next.square_zero)

/-- The induced integral map is defined through the quotient, so it respects all torsion relations. -/
def map : result.Model →ₗ[ℤ] target.Model :=
  target.quotientEquiv.toLinearMap.comp
    ((result.kernel.presentationMap target.kernel φ).comp result.quotientEquiv.symm.toLinearMap)

@[simp] lemma map_apply (x : result.Model) :
    result.map target φ x = target.normalize (φ.τ₂.hom (result.representative x)) := rfl

/-- The executable map on free and torsion coordinates agrees with Mathlib homology. -/
lemma map_naturality :
    ShortComplex.homologyMap φ ≫ target.homologyIso.hom =
      result.homologyIso.hom ≫ ModuleCat.ofHom (result.map target φ) := by
  simp only [homologyIso, Iso.trans_hom, ← Category.assoc,
    result.kernel.presentationMap_naturality target.kernel φ]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change _ = target.quotientEquiv ((result.kernel.presentationMap target.kernel φ)
    (result.quotientEquiv.symm (result.quotientEquiv _)))
  rw [LinearEquiv.symm_apply_apply]
  rfl

@[simp] lemma map_id : result.map result (𝟙 _) = LinearMap.id := by
  have h := result.map_naturality result (𝟙 _)
  have h' := congrArg (fun f => result.homologyIso.inv ≫ f) h
  simpa using congrArg ModuleCat.Hom.hom h'.symm

/-- Composition on integral models follows from the Mathlib comparison. -/
lemma map_comp : result.map next (φ ≫ ψ) = (target.map next ψ).comp (result.map target φ) := by
  suffices h : ModuleCat.ofHom (result.map next (φ ≫ ψ)) =
      ModuleCat.ofHom (result.map target φ) ≫ ModuleCat.ofHom (target.map next ψ) from
    congrArg ModuleCat.Hom.hom h
  apply (cancel_epi result.homologyIso.hom).mp
  rw [← result.map_naturality next (φ ≫ ψ), ShortComplex.homologyMap_comp]
  rw [Category.assoc, target.map_naturality next ψ, ← Category.assoc,
    result.map_naturality target φ, Category.assoc]

end IntegerCohomologyCertificate

/-- Compute and check integral cocycle and Smith coordinates using only the local matrices.
There is no fuel parameter. Descent or certificate failure returns an error, never a result
without proofs. Universal success of the candidate generator is not a theorem of this API. -/
def computeInteger (A : Matrix (Fin b) (Fin a) ℤ) (B : Matrix (Fin c) (Fin b) ℤ) :
    Except String (IntegerCohomologyCertificate A B) := do
  if hBA : B * A = 0 then
    let reducedB ← integerReduce B
    let data := reducedB.kernelData
    if hk : data.Valid B then
      let kernel := data.certificate B hk
      let reducedW ← integerReduce (kernel.retraction * A)
      let quotient := reducedW.smithPresentationData
      if hw : quotient.Valid (kernel.retraction * A) then
        return ⟨hBA, kernel, quotient, hw⟩
      else throw "integer cohomology: normalized Smith presentation check failed"
    else throw "integer cohomology: complete integral kernel check failed"
  else throw "integer cohomology: consecutive differentials do not compose to zero"

end ComputableCohomology

namespace FiniteFreeCochainComplex

open CategoryTheory ComputableCohomology
open scoped Matrix

variable (C : FiniteFreeCochainComplex ℤ) (n : ℤ)

/-- Compute integral cohomology using only the two differentials at the requested degree. -/
def computeIntegerCohomology :
    Except String (IntegerCohomologyCertificate (C.incoming n) (C.d n)) :=
  computeInteger (C.incoming n) (C.d n)

/-- Transport the computed integral model to Mathlib cohomology of the original complex. -/
noncomputable def integerCohomologyIso
    (result : IntegerCohomologyCertificate (C.incoming n) (C.d n)) :
    C.toCochainComplex.homology n ≅ ModuleCat.of ℤ result.Model :=
  C.localHomologyIso n ≪≫ result.homologyIso

variable {C D E : FiniteFreeCochainComplex ℤ}
  (f : C ⟶ D) (g : D ⟶ E)
  (source : IntegerCohomologyCertificate (C.incoming n) (C.d n))
  (target : IntegerCohomologyCertificate (D.incoming n) (D.d n))
  (next : IntegerCohomologyCertificate (E.incoming n) (E.d n))

/-- Compute an existing cochain map on the free and torsion models at the requested degree. -/
def Hom.integerCohomologyMap : source.Model →ₗ[ℤ] target.Model :=
  source.map target (f.localMap n)

@[simp] lemma Hom.integerCohomologyMap_apply (x : source.Model) :
    f.integerCohomologyMap n source target x =
      target.normalize (f.f n *ᵥ source.representative x) := by
  rw [Hom.integerCohomologyMap, IntegerCohomologyCertificate.map_apply, Hom.localMap_τ₂]
  rfl

/-- The integral model map agrees with Mathlib's map on the original complexes. -/
lemma Hom.integerCohomologyMap_naturality :
    HomologicalComplex.homologyMap f.toCochainMap n ≫ (D.integerCohomologyIso n target).hom =
      (C.integerCohomologyIso n source).hom ≫
        ModuleCat.ofHom (f.integerCohomologyMap n source target) := by
  simp only [integerCohomologyIso, Iso.trans_hom, Hom.integerCohomologyMap]
  rw [← Category.assoc, f.localHomologyIso_naturality, Category.assoc,
    source.map_naturality target (f.localMap n), Category.assoc]

@[simp] lemma integerCohomologyMap_id :
    (𝟙 C : C ⟶ C).integerCohomologyMap n source source = LinearMap.id := by
  simp [Hom.integerCohomologyMap]

lemma integerCohomologyMap_comp :
    (f ≫ g).integerCohomologyMap n source next =
      (g.integerCohomologyMap n target next).comp (f.integerCohomologyMap n source target) := by
  simp only [Hom.integerCohomologyMap, localMap_comp]
  exact source.map_comp target next (f.localMap n) (g.localMap n)

end FiniteFreeCochainComplex

namespace BasedCochainComplex

open CategoryTheory ComputableCohomology

variable {C : Type*} [Category C] [Preadditive C]
  {K : BoundedCochainComplex (CMat_ C)} (data : BasedCochainComplex ℤ K) (n : ℤ)

/-- Transport the integral result through the supplied realization's coordinate isomorphism. -/
noncomputable def integerCohomologyIso
    (result : IntegerCohomologyCertificate
      (data.toFiniteFree.incoming n) (data.toFiniteFree.d n)) :
    data.realized.toHomologicalComplex.homology n ≅ ModuleCat.of ℤ result.Model :=
  data.cohomologyPresentationIso n result.kernel ≪≫ result.quotientEquiv.toModuleIso

end BasedCochainComplex
