import Mathlib
import KLRW.KLRWAlgebra
import KLRW.KLRWCategory

namespace KLRW

open CategoryTheory

variable {V : Type*} [DecidableEq V] [Fintype V]
variable {parameters : KLRWStructure V}
variable (R : Type*) [CommRing R]

-- LEFT IDEAL THINGS

/-- The left ideal Ae as an A-submodule of A. -/
noncomputable def leftIdeal (X : KLRWObject parameters) :
    Submodule (KLRWAlg R parameters) (KLRWAlg R parameters) :=
  LinearMap.range (LinearMap.mulRight (KLRWAlg R parameters) (idem_morph R X))

/-- The projection map p : A → Ae given by a ↦ a * e. -/
noncomputable def leftIdealProj (X : KLRWObject parameters) :
    (KLRWAlg R parameters) →ₗ[KLRWAlg R parameters] leftIdeal R X :=
  LinearMap.codRestrict (leftIdeal R X)
    (LinearMap.mulRight (KLRWAlg R parameters) (idem_morph R X))
    (fun a => LinearMap.mem_range_self _ a)

/-- Pointwise equality: p(i(x)) = x for all x ∈ Ae. -/
lemma leftIdealProj_subtype (X : KLRWObject parameters) (x : leftIdeal R X) :
    leftIdealProj R X (x : KLRWAlg R parameters) = x := by
  ext
  obtain ⟨a, ha⟩ := x.property
  dsimp [leftIdealProj, LinearMap.mulRight] at *
  rw [← ha, mul_assoc, idem_is_idem, ha]

/-- Map equality: p ∘ₗ i = LinearMap.id -/
lemma leftIdealProj_comp_subtype (X : KLRWObject parameters) :
    leftIdealProj R X ∘ₗ (leftIdeal R X).subtype = LinearMap.id := by
  ext x
  dsimp
  rw [leftIdealProj_subtype]

/-- Ae is a projective left A-module. -/
instance leftIdeal_projective (X : KLRWObject parameters) :
    Module.Projective (KLRWAlg R parameters) (leftIdeal R X) :=
  Module.Projective.of_split (leftIdeal R X).subtype (leftIdealProj R X) (leftIdealProj_comp_subtype R X)


-- RIGHT IDEAL THINGS

open MulOpposite

/-- A ring A is projective as a module over its opposite ring Aᵐᵒᵖ. -/
instance ring_projective_opposite (A : Type*) [Ring A] : Module.Projective Aᵐᵒᵖ A :=
  have e : Aᵐᵒᵖ ≃ₗ[Aᵐᵒᵖ] A := {
    toFun := unop
    invFun := op
    left_inv := op_unop
    right_inv := unop_op
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
  }
  Module.Projective.of_equiv' e

/-- The right ideal eA as an Aᵐᵒᵖ-submodule of A. -/
noncomputable def rightIdeal (X : KLRWObject parameters) :
    Submodule (KLRWAlg R parameters)ᵐᵒᵖ (KLRWAlg R parameters) :=
  LinearMap.range (LinearMap.mulLeft (KLRWAlg R parameters)ᵐᵒᵖ (idem_morph R X))

/-- The projection map p : A → eA given by a ↦ e * a. -/
noncomputable def rightIdealProj (X : KLRWObject parameters) :
    (KLRWAlg R parameters) →ₗ[(KLRWAlg R parameters)ᵐᵒᵖ] rightIdeal R X :=
  LinearMap.codRestrict (rightIdeal R X)
    (LinearMap.mulLeft (KLRWAlg R parameters)ᵐᵒᵖ (idem_morph R X))
    (fun a => LinearMap.mem_range_self _ a)

lemma rightIdealProj_subtype (X : KLRWObject parameters) (x : rightIdeal R X) :
    rightIdealProj R X (x : KLRWAlg R parameters) = x := by
  ext
  obtain ⟨a, ha⟩ := x.property
  dsimp [rightIdealProj, LinearMap.mulLeft] at *
  rw [← ha, ← mul_assoc, idem_is_idem, ha]

lemma rightIdealProj_comp_subtype (X : KLRWObject parameters) :
    rightIdealProj R X ∘ₗ (rightIdeal R X).subtype = LinearMap.id :=
  LinearMap.ext (rightIdealProj_subtype R X)

/-- eA is a projective left Aᵐᵒᵖ-module (i.e. projective right A-module). -/
instance rightIdeal_projective (X : KLRWObject parameters) :
    Module.Projective (KLRWAlg R parameters)ᵐᵒᵖ (rightIdeal R X) :=
  Module.Projective.of_split (rightIdeal R X).subtype (rightIdealProj R X) (rightIdealProj_comp_subtype R X)

instance idem_morph_are_COI (parameters : KLRWStructure V) :
  CompleteOrthogonalIdempotents (idem_morph (parameters:=parameters) R) where

  idem := idem_is_idem (parameters:=parameters)
  ortho := by
    intro X Y hXY
    apply rel_eq_same_con_class
    apply implicit_rel_eq_rel
    exact KLRWImplicitConRel.bad_comp (.idem Y) (.idem X) hXY.symm
  complete := by
    change ∑ i, (KLRWRel R parameters).mk' (FreeAlgebra.ι _ (.idem i)) = 1
    rw [← map_sum]
    apply rel_eq_same_con_class
    apply implicit_rel_eq_rel
    exact KLRWImplicitConRel.id_sum

def isRightViolated (X : KLRWObject parameters) :
  Prop :=
  match X.strandSeq.toList.getLast? with
  | some strand => strand.color = .black
  | none        => false

def isLeftViolated (X : KLRWObject parameters) :
  Prop :=
  match X.strandSeq.toList[0]? with
  | some strand => strand.color = .black
  | none        => false

def isViolated (X : KLRWObject parameters) :
  Prop :=
  isRightViolated X ∨ isLeftViolated X

noncomputable def idem_violated (parameters : KLRWStructure V) :
  KLRWAlg R parameters :=
  ∑ X ∈ Finset.univ.filter (isViolated (parameters:=parameters)), idem_morph R X

lemma idem_violated_is_idem (parameters: KLRWStructure V) :
  IsIdempotentElem (idem_violated R parameters) := by
 sorry

end KLRW
