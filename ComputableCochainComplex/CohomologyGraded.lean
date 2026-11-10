/-
Copyright (c) 2026 Annie Yao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Annie Yao
-/
module

public import ComputableCochainComplex.CohomologyInteger

/-!
# Finite coordinates for one homogeneous piece

The shift convention is `M⟨s⟩_q = M_(q+s)`. Restriction requires proofs that both
differentials send these pieces to the corresponding target pieces. No decomposition of an
ambient module, grading of a quotient presentation, or local-finiteness theorem is assumed.

`LocalCoordinates` gives finite ordered coordinates on an existing Mathlib short complex.
It forms matrices by evaluating the differentials on basis vectors, and transports computed
cohomology and representatives back to the supplied modules. `GradedHomCoordinates` is the
small upstream contract for diagrammatic categories, over the actual solver coefficient ring.
-/

@[expose] public section

namespace ComputableCohomology

open CategoryTheory
open scoped Matrix

variable {R : Type*} [CommRing R]

/-- Restrict an existing local complex to a fixed internal degree, after the stated shifts.
The two preservation proofs are necessary input; inhomogeneous differentials do not qualify. -/
def restrictAtDegree (S : ShortComplex (ModuleCat R))
    (H₁ : ℤ → Submodule R S.X₁) (H₂ : ℤ → Submodule R S.X₂)
    (H₃ : ℤ → Submodule R S.X₃) (q s₁ s₂ s₃ : ℤ)
    (hf : ∀ x ∈ H₁ (q + s₁), S.f.hom x ∈ H₂ (q + s₂))
    (hg : ∀ x ∈ H₂ (q + s₂), S.g.hom x ∈ H₃ (q + s₃)) :
    ShortComplex (ModuleCat R) :=
  ShortComplex.moduleCatMk
    ((S.f.hom.domRestrict (H₁ (q + s₁))).codRestrict (H₂ (q + s₂))
      (fun x => hf x.val x.property))
    ((S.g.hom.domRestrict (H₂ (q + s₂))).codRestrict (H₃ (q + s₃))
      (fun x => hg x.val x.property)) (by
        apply LinearMap.ext
        intro x
        apply Subtype.ext
        exact congrArg (fun f => f.hom x.val) S.zero)

/-- Finite ordered bases on the three terms of an existing local complex. -/
structure LocalCoordinates (S : ShortComplex (ModuleCat R)) where
  /-- Number of incoming-term coordinates. -/
  sourceSize : ℕ
  /-- Number of middle-term coordinates. -/
  middleSize : ℕ
  /-- Number of outgoing-term coordinates. -/
  targetSize : ℕ
  /-- Executable encoding and decoding, including the finite-basis compatibility proof. -/
  source : S.X₁ ≃ₗ[R] (Fin sourceSize → R)
  /-- Executable middle-term coordinates. -/
  middle : S.X₂ ≃ₗ[R] (Fin middleSize → R)
  /-- Executable outgoing-term coordinates. -/
  target : S.X₃ ≃ₗ[R] (Fin targetSize → R)

namespace LocalCoordinates

variable {S : ShortComplex (ModuleCat R)} (data : LocalCoordinates S)

/-- Evaluate the incoming differential on source basis vectors and encode its outputs. -/
def incoming : Matrix (Fin data.middleSize) (Fin data.sourceSize) R :=
  LinearMap.toMatrix' (data.middle.toLinearMap.comp (S.f.hom.comp data.source.symm.toLinearMap))

/-- Evaluate the outgoing differential on middle basis vectors and encode its outputs. -/
def outgoing : Matrix (Fin data.targetSize) (Fin data.middleSize) R :=
  LinearMap.toMatrix' (data.target.toLinearMap.comp (S.g.hom.comp data.middle.symm.toLinearMap))

@[simp] lemma incoming_mulVec (x : Fin data.sourceSize → R) :
    data.incoming *ᵥ x = data.middle (S.f.hom (data.source.symm x)) :=
  LinearMap.toMatrix'_mulVec _ _

@[simp] lemma outgoing_mulVec (x : Fin data.middleSize → R) :
    data.outgoing *ᵥ x = data.target (S.g.hom (data.middle.symm x)) :=
  LinearMap.toMatrix'_mulVec _ _

lemma square_zero : data.outgoing * data.incoming = 0 := by
  apply Matrix.ext_iff_mulVec.mpr
  intro x
  rw [Matrix.zero_mulVec, ← Matrix.mulVec_mulVec, outgoing_mulVec, incoming_mulVec,
    LinearEquiv.symm_apply_apply]
  have h := congrArg (fun f => f.hom (data.source.symm x)) S.zero
  change S.g.hom (S.f.hom (data.source.symm x)) = 0 at h
  rw [h, map_zero]

/-- Compare with executable matrices supplied separately from possibly noncomputable ambient maps.
Only the coordinate transformations are used as data; differential compatibility is proof input. -/
def shortComplexIsoOfMatrices
    (A : Matrix (Fin data.middleSize) (Fin data.sourceSize) R)
    (B : Matrix (Fin data.targetSize) (Fin data.middleSize) R) (hBA : B * A = 0)
    (hA : ∀ x, A *ᵥ x = data.middle (S.f.hom (data.source.symm x)))
    (hB : ∀ x, B *ᵥ x = data.target (S.g.hom (data.middle.symm x))) :
    S ≅ KernelCertificate.shortComplex A hBA :=
  ShortComplex.isoMk data.source.toModuleIso data.middle.toModuleIso data.target.toModuleIso
    (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change A *ᵥ data.source x = data.middle (S.f.hom x)
      rw [hA, LinearEquiv.symm_apply_apply])
    (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change B *ᵥ data.middle x = data.target (S.g.hom x)
      rw [hB, LinearEquiv.symm_apply_apply])

/-- The supplied bases identify the original local complex with its evaluated matrices. -/
def shortComplexIso : S ≅ KernelCertificate.shortComplex data.incoming data.square_zero :=
  data.shortComplexIsoOfMatrices data.incoming data.outgoing data.square_zero
    data.incoming_mulVec data.outgoing_mulVec

/-- Transport a checked free result without evaluating the ambient quotient operations. -/
noncomputable def freeHomologyIsoOfMatrices
    {A : Matrix (Fin data.middleSize) (Fin data.sourceSize) R}
    {B : Matrix (Fin data.targetSize) (Fin data.middleSize) R}
    (hA : ∀ x, A *ᵥ x = data.middle (S.f.hom (data.source.symm x)))
    (hB : ∀ x, B *ᵥ x = data.target (S.g.hom (data.middle.symm x)))
    (result : FreeCohomologyCertificate A B) :
    S.homology ≅ ModuleCat.of R (Fin result.size → R) :=
  ShortComplex.homologyMapIso
    (data.shortComplexIsoOfMatrices A B result.square_zero hA hB) ≪≫ result.homologyIso

/-- Computed free cohomology is the cohomology of the supplied homogeneous modules. -/
noncomputable def freeHomologyIso
    (result : FreeCohomologyCertificate data.incoming data.outgoing) :
    S.homology ≅ ModuleCat.of R (Fin result.size → R) :=
  ShortComplex.homologyMapIso data.shortComplexIso ≪≫ result.homologyIso

/-- Recover a computed free-model cocycle as an element of the original middle module. -/
def freeRepresentative (result : FreeCohomologyCertificate data.incoming data.outgoing)
    (x : Fin result.size → R) : S.X₂ := data.middle.symm (result.representative x)

lemma freeRepresentative_is_cocycle
    (result : FreeCohomologyCertificate data.incoming data.outgoing) (x : Fin result.size → R) :
    S.g.hom (data.freeRepresentative result x) = 0 := by
  apply data.target.injective
  rw [map_zero]
  exact (data.outgoing_mulVec _).symm.trans (result.representative_is_cocycle x)

end LocalCoordinates

namespace LocalCoordinates

variable {S : ShortComplex (ModuleCat ℤ)} (data : LocalCoordinates S)

/-- Transport a checked integral result without evaluating the ambient quotient operations. -/
noncomputable def integerHomologyIsoOfMatrices
    {A : Matrix (Fin data.middleSize) (Fin data.sourceSize) ℤ}
    {B : Matrix (Fin data.targetSize) (Fin data.middleSize) ℤ}
    (hA : ∀ x, A *ᵥ x = data.middle (S.f.hom (data.source.symm x)))
    (hB : ∀ x, B *ᵥ x = data.target (S.g.hom (data.middle.symm x)))
    (result : IntegerCohomologyCertificate A B) :
    S.homology ≅ ModuleCat.of ℤ result.Model :=
  ShortComplex.homologyMapIso
    (data.shortComplexIsoOfMatrices A B result.square_zero hA hB) ≪≫ result.homologyIso

/-- The computed integral model is the cohomology of the supplied homogeneous modules. -/
noncomputable def integerHomologyIso
    (result : IntegerCohomologyCertificate data.incoming data.outgoing) :
    S.homology ≅ ModuleCat.of ℤ result.Model :=
  ShortComplex.homologyMapIso data.shortComplexIso ≪≫ result.homologyIso

/-- Recover a computed integral cocycle in the original, possibly diagrammatic, middle module. -/
def integerRepresentative (result : IntegerCohomologyCertificate data.incoming data.outgoing)
    (x : result.Model) : S.X₂ := data.middle.symm (result.representative x)

lemma integerRepresentative_is_cocycle
    (result : IntegerCohomologyCertificate data.incoming data.outgoing) (x : result.Model) :
    S.g.hom (data.integerRepresentative result x) = 0 := by
  apply data.target.injective
  rw [map_zero]
  exact (data.outgoing_mulVec _).symm.trans (result.representative_is_cocycle x)

end LocalCoordinates

/-- Upstream finite graded-coordinate contract for an existing diagrammatic category.
The ring `R` is the ring of the finite free pieces being solved, not an implicit specialization
of a polynomial coefficient ring. Equivalences certify spanning and independence of the supplied
pieces; construction of these equivalences and identification of the actual grading are upstream. -/
structure GradedHomCoordinates (R : Type*) [CommRing R] (C : Type*) [Category C]
    [Preadditive C] [∀ X Y : C, Module R (X ⟶ Y)] where
  /-- The actual homogeneous submodules, supplied by the category's grading construction. -/
  piece : ∀ X Y : C, ℤ → Submodule R (X ⟶ Y)
  /-- Finite rank over the actual solver coefficient ring, in each requested piece. -/
  size : C → C → ℤ → ℕ
  /-- Executable finite ordered coordinates, respecting addition and scalar actions. -/
  coordinates : ∀ X Y q, piece X Y q ≃ₗ[R] (Fin (size X Y q) → R)
  /-- Executable composition on coordinate vectors of homogeneous morphisms. -/
  compose : ∀ X Y Z p q, (Fin (size X Y p) → R) → (Fin (size Y Z q) → R) →
    (Fin (size X Z (p + q)) → R)
  /-- Decoding the coordinate composition equals composition in the original category. -/
  decode_compose : ∀ X Y Z p q x y,
    ((coordinates X Z (p + q)).symm (compose X Y Z p q x y)).val =
      ((coordinates X Y p).symm x).val ≫ ((coordinates Y Z q).symm y).val

end ComputableCohomology
