import Mathlib
import KLRW.KLRWAlgebra
import KLRW.KLRWCategory

namespace KLRW

open CategoryTheory

variable {V : Type*} [DecidableEq V] [Fintype V]
variable {parameters : KLRWStructure V}
variable (R : Type*) [CommRing R]


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

instance (X : KLRWObject parameters): Decidable (isViolated X) := by
  unfold isViolated isRightViolated isLeftViolated
  split <;> split <;> infer_instance

noncomputable def idem_violated (parameters : KLRWStructure V) :
  KLRWAlg R parameters :=
  ∑ X ∈ Finset.univ.filter (isViolated (parameters:=parameters)), idem_morph R X

lemma idem_violated_is_idem (parameters: KLRWStructure V) :
  IsIdempotentElem (idem_violated R parameters) := by
  unfold idem_violated
  exact (idem_morph_are_COI R parameters).isIdempotentElem_sum

end KLRW
