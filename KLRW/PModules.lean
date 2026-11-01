module

public import KLRW.KLRWCategory

/-!
# Violated idempotents in the KLRW algebra

The straight-line idempotents `e_X = idem_morph R X` form a complete family of orthogonal
idempotents in `KLRWAlg R parameters`. An object `X` is *violated* if its leftmost or rightmost
strand is black. The sum of the `e_X` over all violated `X` is again an idempotent; it is the
first ingredient in the construction of the right modules `eA` and `eAfA`.
-/

@[expose] public section

namespace KLRW

variable {V : Type*} [DecidableEq V] [Fintype V]
variable {parameters : KLRWStructure V}
variable (R : Type*) [CommRing R]

-- *NOTE*: The following theorem should probably be placed in KLRWCategory.lean.
/-- The straight-line idempotents `e_X` are pairwise orthogonal and sum to `1`. -/
lemma completeOrthogonalIdempotents_idem_morph (parameters : KLRWStructure V) :
    CompleteOrthogonalIdempotents (idem_morph (parameters := parameters) R) where
  idem := idem_is_idem
  ortho X Y hXY := by
    apply rel_eq_same_con_class
    apply implicit_rel_eq_rel
    exact KLRWImplicitConRel.bad_comp (.idem Y) (.idem X) hXY.symm
  complete := by
    change ∑ i, (KLRWRel R parameters).mk' (FreeAlgebra.ι _ (.idem i)) = 1
    rw [← map_sum]
    apply rel_eq_same_con_class
    apply implicit_rel_eq_rel
    exact KLRWImplicitConRel.id_sum

/-- An object is *right violated* if its rightmost strand is black. -/
def IsRightViolated (X : KLRWObject parameters) : Prop :=
  X.strandSeq.toList.getLast?.map StrandData.color = some .black

/-- An object is *left violated* if its leftmost strand is black. -/
def IsLeftViolated (X : KLRWObject parameters) : Prop :=
  X.strandSeq.toList.head?.map StrandData.color = some .black

/-- An object is *violated* if its rightmost or leftmost strand is black. -/
def IsViolated (X : KLRWObject parameters) : Prop :=
  IsRightViolated X ∨ IsLeftViolated X

instance : DecidablePred (IsRightViolated (parameters := parameters)) := fun _ => decEq _ _

instance : DecidablePred (IsLeftViolated (parameters := parameters)) := fun _ => decEq _ _

instance : DecidablePred (IsViolated (parameters := parameters)) := fun X =>
  inferInstanceAs (Decidable (IsRightViolated X ∨ IsLeftViolated X))

/-- `f = violatedIdem` is the sum of the straight-line idempotents
    `e_X` over all violated objects `X`. -/
noncomputable def violatedIdem (parameters : KLRWStructure V) : KLRWAlg R parameters :=
  ∑ X ∈ Finset.univ.filter (IsViolated (parameters := parameters)), idem_morph R X

/--`violatedIdem` is idempotent, being a partial sum of orthogonal idempotents. -/
lemma isIdempotentElem_violatedIdem (parameters : KLRWStructure V) :
    IsIdempotentElem (violatedIdem R parameters) :=
  (completeOrthogonalIdempotents_idem_morph R parameters).isIdempotentElem_sum

/-- Multiplying `e_X` on the left by `violatedIdem` keeps `e_X` if `X` is violated and kills it
otherwise. -/
lemma violatedIdem_mul_idem_morph (X : KLRWObject parameters) :
    violatedIdem R parameters * idem_morph R X =
      if IsViolated X then idem_morph R X else 0 := by
  classical
  simp [violatedIdem, Finset.sum_mul,
    (completeOrthogonalIdempotents_idem_morph R parameters).mul_eq]

/-- `violatedIdem * e_X = e_X` when `X` is violated. -/
lemma violatedIdem_mul_idem_morph_of_isViolated {X : KLRWObject parameters}
    (hX : IsViolated X) : violatedIdem R parameters * idem_morph R X = idem_morph R X := by
  rw [violatedIdem_mul_idem_morph, if_pos hX]

/-- `violatedIdem * e_X = 0` when `X` is not violated. -/
lemma violatedIdem_mul_idem_morph_of_not_isViolated {X : KLRWObject parameters}
    (hX : ¬IsViolated X) : violatedIdem R parameters * idem_morph R X = 0 := by
  rw [violatedIdem_mul_idem_morph, if_neg hX]

/-- `e_X * violatedIdem = e_X` when `X` is violated. -/
lemma idem_morph_mul_violatedIdem_of_isViolated {X : KLRWObject parameters}
    (hX : IsViolated X) : idem_morph R X * violatedIdem R parameters = idem_morph R X :=
  (completeOrthogonalIdempotents_idem_morph R parameters).mul_sum_of_mem (by simpa using hX)

/-- `e_X * violatedIdem = 0` when `X` is not violated. -/
lemma idem_morph_mul_violatedIdem_of_not_isViolated {X : KLRWObject parameters}
    (hX : ¬IsViolated X) : idem_morph R X * violatedIdem R parameters = 0 :=
  (completeOrthogonalIdempotents_idem_morph R parameters).mul_sum_of_notMem (by simpa using hX)

end KLRW
