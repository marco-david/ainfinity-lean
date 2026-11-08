/-
Copyright (c) 2026 Annie Yao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Annie Yao
-/
module

public import ComputableCochainComplex.CohomologyKernel
public import ComputableCochainComplex.BasedCochainComplex
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Cohomology certificates for finite free complexes

Only the incoming and outgoing differentials at the requested integer degree are used.
The certificate comparison targets Mathlib's homology of the existing matrix interpretation.
For based categorical complexes it is transported through the existing `coordinateIso`.
-/

@[expose] public section

open CategoryTheory
open scoped Matrix

namespace FiniteFreeCochainComplex

variable {R : Type*} [CommRing R] (C : FiniteFreeCochainComplex R) (n : ℤ)

/-- The incoming differential, with its target indexed by `size n`.
The standard-coordinate matrix handles the equality `(n - 1) + 1 = n` without exposing casts. -/
def incoming : Matrix (Fin (C.size n)) (Fin (C.size (n - 1))) R :=
  LinearMap.toMatrix' (C.toCochainComplex.d (n - 1) n).hom

@[simp] lemma incoming_mulVec (x : Fin (C.size (n - 1)) → R) :
    C.incoming n *ᵥ x = (C.toCochainComplex.d (n - 1) n).hom x :=
  LinearMap.toMatrix'_mulVec _ _

@[simp] lemma incoming_mulVecLin :
    (C.incoming n).mulVecLin = (C.toCochainComplex.d (n - 1) n).hom :=
  Matrix.toLin'_toMatrix' _

lemma d_mul_incoming : C.d n * C.incoming n = 0 := by
  apply Matrix.ext_iff_mulVec.mpr
  intro x
  rw [Matrix.zero_mulVec, ← Matrix.mulVec_mulVec, C.incoming_mulVec,
    ← C.toCochainComplex_d_apply]
  exact congrArg (fun f => f.hom x) (C.toCochainComplex.d_comp_d (n - 1) n (n + 1))

/-- The local matrices describe exactly the three relevant terms of the original complex. -/
def localShortComplexIso :
    C.toCochainComplex.sc' (n - 1) n (n + 1) ≅
      ComputableCohomology.KernelCertificate.shortComplex (C.incoming n) (C.d_mul_incoming n) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp [ComputableCohomology.KernelCertificate.shortComplex, ShortComplex.moduleCatMk])
    (by simp [ComputableCohomology.KernelCertificate.shortComplex, ShortComplex.moduleCatMk])

/-- Kernel coordinates compute Mathlib's cohomology in the requested degree. -/
noncomputable def cohomologyPresentationIso
    (k : ComputableCohomology.KernelCertificate (C.d n)) :
    C.toCochainComplex.homology n ≅
      ModuleCat.of R ((Fin k.size → R) ⧸ LinearMap.range (k.retraction * C.incoming n).mulVecLin) :=
  C.toCochainComplex.homologyIsoSc' (n - 1) n (n + 1) (by simp) (by simp) ≪≫
    ShortComplex.homologyMapIso (C.localShortComplexIso n) ≪≫
    k.homologyIso (C.incoming n) (C.d_mul_incoming n)

end FiniteFreeCochainComplex

namespace BasedCochainComplex

universe u v w

variable {R : Type u} [CommRing R] {C : Type v} [Category.{w} C] [Preadditive C]
  {K : BoundedCochainComplex (CMat_ C)} (data : BasedCochainComplex R K) (n : ℤ)

/-- Transport the certified presentation through the supplied categorical coordinates. -/
noncomputable def cohomologyPresentationIso
    (k : ComputableCohomology.KernelCertificate (data.toFiniteFree.d n)) :
    data.realized.toHomologicalComplex.homology n ≅
      ModuleCat.of R ((Fin k.size → R) ⧸
        LinearMap.range (k.retraction * data.toFiniteFree.incoming n).mulVecLin) :=
  HomologicalComplex.homologyMapIso data.coordinateIso n ≪≫
    data.toFiniteFree.cohomologyPresentationIso n k

end BasedCochainComplex
