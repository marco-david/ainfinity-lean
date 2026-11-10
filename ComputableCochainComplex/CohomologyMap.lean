/-
Copyright (c) 2026 Annie Yao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Annie Yao
-/
module

public import ComputableCochainComplex.CohomologyField

/-!
# Induced maps on computed cohomology

Maps first act on Mathlib's explicit kernel quotient, then pass through the certified
coordinate equivalences. The comparison with Mathlib homology is shared by the field and
integer backends. No additional category of complexes or homology theory is introduced.
-/

@[expose] public section

namespace ComputableCohomology

open CategoryTheory
open scoped Matrix

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

@[simp] lemma cyclesLinearMap_apply (φ : S ⟶ T) (x : LinearMap.ker S.g.hom) :
    (cyclesLinearMap φ x).val = φ.τ₂.hom x.val := rfl

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

@[simp] lemma quotientLinearMap_mk (φ : S ⟶ T) (x : LinearMap.ker S.g.hom) :
    quotientLinearMap φ (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (cyclesLinearMap φ x) := rfl

/-- The concrete quotient map is a homology map in Mathlib's existing universal-property API. -/
def moduleHomologyMapData (φ : S ⟶ T) :
    ShortComplex.LeftHomologyMapData φ S.moduleCatLeftHomologyData T.moduleCatLeftHomologyData where
  φK := ModuleCat.ofHom (cyclesLinearMap φ)
  φH := ModuleCat.ofHom (quotientLinearMap φ)
  commi := by rfl
  commf' := by
    apply ModuleCat.hom_ext
    ext x
    exact cyclesLinearMap_boundary φ x
  commπ := by rfl

/-- The explicit quotient map agrees with Mathlib's induced homology map. -/
lemma quotientLinearMap_naturality (φ : S ⟶ T) :
    ShortComplex.homologyMap φ ≫ T.moduleCatHomologyIso.hom =
      S.moduleCatHomologyIso.hom ≫ ModuleCat.ofHom (quotientLinearMap φ) :=
  (moduleHomologyMapData φ).homologyMap_comm

namespace KernelCertificate

variable {a b c a' b' c' : ℕ}
  {A : Matrix (Fin b) (Fin a) R} {B : Matrix (Fin c) (Fin b) R} {hBA : B * A = 0}
  {D : Matrix (Fin b') (Fin a') R} {E : Matrix (Fin c') (Fin b') R} {hED : E * D = 0}
  (k : KernelCertificate B) (l : KernelCertificate E)
  (φ : shortComplex A hBA ⟶ shortComplex D hED)

/-- Transport the concrete homology map to the certified matrix presentations. -/
def presentationMap :
    ((Fin k.size → R) ⧸ LinearMap.range (k.retraction * A).mulVecLin) →ₗ[R]
      ((Fin l.size → R) ⧸ LinearMap.range (l.retraction * D).mulVecLin) :=
  (l.quotientEquiv D hED).toLinearMap.comp
    ((quotientLinearMap φ).comp (k.quotientEquiv A hBA).symm.toLinearMap)

@[simp] lemma presentationMap_mk (x : Fin k.size → R) :
    k.presentationMap l φ (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (l.retraction *ᵥ φ.τ₂.hom (k.inclusion *ᵥ x)) := rfl

/-- Presentation maps describe exactly Mathlib's homology map, including all relations. -/
lemma presentationMap_naturality :
    ShortComplex.homologyMap φ ≫ (l.homologyIso D hED).hom =
      (k.homologyIso A hBA).hom ≫ ModuleCat.ofHom (k.presentationMap l φ) := by
  simp only [homologyIso, Iso.trans_hom, ← Category.assoc, quotientLinearMap_naturality]
  apply ModuleCat.hom_ext
  ext x
  simp [presentationMap]

end KernelCertificate

namespace FreeCohomologyCertificate

variable {a b c a' b' c' a'' b'' c'' : ℕ}
  {A : Matrix (Fin b) (Fin a) R} {B : Matrix (Fin c) (Fin b) R}
  {D : Matrix (Fin b') (Fin a') R} {E : Matrix (Fin c') (Fin b') R}
  {F : Matrix (Fin b'') (Fin a'') R} {G : Matrix (Fin c'') (Fin b'') R}
  (source : FreeCohomologyCertificate A B) (target : FreeCohomologyCertificate D E)
  (next : FreeCohomologyCertificate F G)
  (φ : KernelCertificate.shortComplex A source.square_zero ⟶
    KernelCertificate.shortComplex D target.square_zero)
  (ψ : KernelCertificate.shortComplex D target.square_zero ⟶
    KernelCertificate.shortComplex F next.square_zero)

/-- The induced linear map between computed free cohomology models. -/
def map : (Fin source.size → R) →ₗ[R] (Fin target.size → R) :=
  (target.quotient.quotientEquiv _ target.valid).toLinearMap.comp
    ((source.kernel.presentationMap target.kernel φ).comp
      (source.quotient.quotientEquiv _ source.valid).symm.toLinearMap)

@[simp] lemma map_apply (x : Fin source.size → R) :
    source.map target φ x = target.normalize (φ.τ₂.hom (source.representative x)) := rfl

/-- Matrix of the induced map in the computed class coordinates. -/
def mapMatrix : Matrix (Fin target.size) (Fin source.size) R :=
  target.quotient.normalize * target.kernel.retraction * LinearMap.toMatrix' φ.τ₂.hom *
    source.kernel.inclusion * source.quotient.representatives

/-- Compute an induced map by representing a class, applying the cochain map, and normalizing. -/
lemma mapMatrix_mulVec (x : Fin source.size → R) :
    source.mapMatrix target φ *ᵥ x =
      target.normalize (φ.τ₂.hom (source.representative x)) := by
  simp only [mapMatrix, ← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec]
  rfl

@[simp] lemma mapMatrix_mulVecLin :
    (source.mapMatrix target φ).mulVecLin = source.map target φ := by
  apply LinearMap.ext
  exact source.mapMatrix_mulVec target φ

/-- The coordinate map agrees with the abstract induced homology map. -/
lemma map_naturality :
    ShortComplex.homologyMap φ ≫ target.homologyIso.hom =
      source.homologyIso.hom ≫ ModuleCat.ofHom (source.map target φ) := by
  simp only [homologyIso, Iso.trans_hom, ← Category.assoc,
    source.kernel.presentationMap_naturality target.kernel φ]
  apply ModuleCat.hom_ext
  ext x
  simp [map]

/-- Identity is inherited from Mathlib's homology map. -/
@[simp] lemma map_id : source.map source (𝟙 _) = LinearMap.id := by
  have h := source.map_naturality source (𝟙 _)
  have h' := congrArg (fun f => source.homologyIso.inv ≫ f) h
  simpa using congrArg ModuleCat.Hom.hom h'.symm

/-- Composition is inherited from Mathlib's homology map. -/
lemma map_comp : source.map next (φ ≫ ψ) = (target.map next ψ).comp (source.map target φ) := by
  suffices h : ModuleCat.ofHom (source.map next (φ ≫ ψ)) =
      ModuleCat.ofHom (source.map target φ) ≫ ModuleCat.ofHom (target.map next ψ) from
    congrArg ModuleCat.Hom.hom h
  apply (cancel_epi source.homologyIso.hom).mp
  rw [← source.map_naturality next (φ ≫ ψ), ShortComplex.homologyMap_comp]
  rw [Category.assoc, target.map_naturality next ψ, ← Category.assoc,
    source.map_naturality target φ, Category.assoc]

@[simp] lemma mapMatrix_id : source.mapMatrix source (𝟙 _) = 1 := by
  apply Matrix.toLin'.injective
  change (source.mapMatrix source (𝟙 _)).mulVecLin = (1 : Matrix _ _ R).mulVecLin
  rw [mapMatrix_mulVecLin, map_id, Matrix.mulVecLin_one]

lemma mapMatrix_comp : source.mapMatrix next (φ ≫ ψ) =
    target.mapMatrix next ψ * source.mapMatrix target φ := by
  apply Matrix.toLin'.injective
  change (source.mapMatrix next (φ ≫ ψ)).mulVecLin =
    (target.mapMatrix next ψ * source.mapMatrix target φ).mulVecLin
  rw [Matrix.mulVecLin_mul, mapMatrix_mulVecLin, mapMatrix_mulVecLin, mapMatrix_mulVecLin,
    source.map_comp target next φ ψ]

end FreeCohomologyCertificate

end ComputableCohomology

namespace FiniteFreeCochainComplex

open CategoryTheory ComputableCohomology

variable {R : Type*} [CommRing R] {C D E : FiniteFreeCochainComplex R}

/-- Restrict an existing cochain map to the two differential matrices at a requested degree. -/
def Hom.localMap (f : C ⟶ D) (n : ℤ) :
    KernelCertificate.shortComplex (C.incoming n) (C.d_mul_incoming n) ⟶
      KernelCertificate.shortComplex (D.incoming n) (D.d_mul_incoming n) :=
  (C.localShortComplexIso n).inv ≫
    (HomologicalComplex.shortComplexFunctor' (ModuleCat R) (.up ℤ)
      (n - 1) n (n + 1)).map f.toCochainMap ≫ (D.localShortComplexIso n).hom

@[simp] lemma Hom.localMap_τ₂ (f : C ⟶ D) (n : ℤ) :
    (f.localMap n).τ₂ = ModuleCat.ofHom (f.f n).mulVecLin := by
  change 𝟙 _ ≫ ModuleCat.ofHom (f.f n).mulVecLin ≫ 𝟙 _ = _
  simp

@[simp] lemma localMap_id (C : FiniteFreeCochainComplex R) (n : ℤ) :
    (𝟙 C : C ⟶ C).localMap n = 𝟙 _ := by
  simp [Hom.localMap]

lemma localMap_comp (f : C ⟶ D) (g : D ⟶ E) (n : ℤ) :
    (f ≫ g).localMap n = f.localMap n ≫ g.localMap n := by
  simp [Hom.localMap]

/-- The local matrix comparison is natural in the original finite-free cochain map. -/
lemma Hom.localHomologyIso_naturality (f : C ⟶ D) (n : ℤ) :
    HomologicalComplex.homologyMap f.toCochainMap n ≫ (D.localHomologyIso n).hom =
      (C.localHomologyIso n).hom ≫ ShortComplex.homologyMap (f.localMap n) := by
  have h := (HomologicalComplex.homologyFunctorIso' (ModuleCat R) (.up ℤ)
    (n - 1) n (n + 1) (by simp) (by simp)).hom.naturality f.toCochainMap
  change HomologicalComplex.homologyMap f.toCochainMap n ≫
      (D.toCochainComplex.homologyIsoSc' (n - 1) n (n + 1) _ _).hom =
    (C.toCochainComplex.homologyIsoSc' (n - 1) n (n + 1) _ _).hom ≫
      ShortComplex.homologyMap ((HomologicalComplex.shortComplexFunctor'
        (ModuleCat R) (.up ℤ) (n - 1) n (n + 1)).map f.toCochainMap) at h
  simp only [localHomologyIso, Iso.trans_hom, ShortComplex.homologyMapIso_hom,
    Hom.localMap, ShortComplex.homologyMap_comp, ← Category.assoc]
  rw [h]
  simp [← ShortComplex.homologyMap_comp, Category.assoc]

end FiniteFreeCochainComplex

namespace FiniteFreeCochainComplex

open CategoryTheory ComputableCohomology
open scoped Matrix

variable {R : Type*} [Field R] {C D E : FiniteFreeCochainComplex R}
  (f : C ⟶ D) (g : D ⟶ E) (n : ℤ)
  (source : FreeCohomologyCertificate (C.incoming n) (C.d n))
  (target : FreeCohomologyCertificate (D.incoming n) (D.d n))
  (next : FreeCohomologyCertificate (E.incoming n) (E.d n))

/-- Compute the matrix of an existing cochain map on the supplied cohomology models. -/
def Hom.fieldCohomologyMatrix : Matrix (Fin target.size) (Fin source.size) R :=
  source.mapMatrix target (f.localMap n)

/-- The matrix acts by lifting a class, applying `f.f n`, and normalizing in the target. -/
lemma Hom.fieldCohomologyMatrix_mulVec (x : Fin source.size → R) :
    f.fieldCohomologyMatrix n source target *ᵥ x =
      target.normalize (f.f n *ᵥ source.representative x) := by
  rw [Hom.fieldCohomologyMatrix, source.mapMatrix_mulVec, Hom.localMap_τ₂]
  rfl

/-- The computed matrix agrees with Mathlib's induced map on the original complexes. -/
lemma Hom.fieldCohomologyMatrix_naturality :
    HomologicalComplex.homologyMap f.toCochainMap n ≫ (D.fieldCohomologyIso n target).hom =
      (C.fieldCohomologyIso n source).hom ≫
        ModuleCat.ofHom (f.fieldCohomologyMatrix n source target).mulVecLin := by
  simp only [fieldCohomologyIso, Iso.trans_hom, Hom.fieldCohomologyMatrix,
    FreeCohomologyCertificate.mapMatrix_mulVecLin]
  rw [← Category.assoc, f.localHomologyIso_naturality, Category.assoc,
    source.map_naturality target (f.localMap n), Category.assoc]

@[simp] lemma fieldCohomologyMatrix_id :
    (𝟙 C : C ⟶ C).fieldCohomologyMatrix n source source = 1 := by
  simp [Hom.fieldCohomologyMatrix]

lemma fieldCohomologyMatrix_comp :
    (f ≫ g).fieldCohomologyMatrix n source next =
      g.fieldCohomologyMatrix n target next * f.fieldCohomologyMatrix n source target := by
  simp only [Hom.fieldCohomologyMatrix, localMap_comp]
  exact source.mapMatrix_comp target next (f.localMap n) (g.localMap n)

end FiniteFreeCochainComplex
