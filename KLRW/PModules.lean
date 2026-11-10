module

public import KLRW.KLRWCategory

/-!
# Violated idempotents in the KLRW algebra

For an object $X$, write $e_X$ for the straight-line idempotent `idem_morph R X`. The $e_X$ form a
complete family of orthogonal idempotents in $A$ = `KLRWAlg R parameters`. An object is
*violated* if its leftmost or rightmost strand is black, and
$$f = \sum_{X \text{ violated}} e_X$$
(`violatedIdem`) is again an idempotent. It is the first ingredient in the construction of the
module $eA/eAfA$. Here, $e$ is a divided-power idempotent yet to be formalized.

## Implementation notes

This implementation is based on Ben Webster's "Knot invariants and higher representation theory",
Definition 4.3, available at <https://arxiv.org/abs/1309.3796>. There are two main discrepancies.

Firstly, Webster defines violated to only concern what we call left violated. This is to define the
cyclotomic quotient (Definition 4.6). This project works inside the full KLRW-algebra $A$.
For constructions that later require quotienting by right violated diagrams inside the
cyclotomic quotient, we instead quotient by all violated diagrams.

Secondly, Webster defines violated to be a property of diagrams/morphisms, whereas we define
violated objects. A morphism $a$ is violated in Webster's sense iff it factors as
$a = b \, e_X \, c$ for some left violated object $X$. Consequently, the (left or right) violated
diagrams span the two-sided ideal $AfA$.

## TODO
* Formalize the characterizations of violated diagrams above.
* Formalize divided-power idempotents.
-/

@[expose] public section

namespace KLRW

variable {V : Type*} [DecidableEq V] [Fintype V]
variable {parameters : KLRWStructure V}
variable (R : Type*) [CommRing R]

-- TODO: Move the following to KLRWCategory.lean under section of idempotents.
/-- The straight-line idempotents are a complete orthogonal family of idempotents, i.e.
the $e_X$ are pairwise orthogonal and sum to 1. -/
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

/-- An object is *left violated* if its leftmost strand is black. `X` is left violated iff
`idem_morph R X` is violated in the sense of Webster's Definition 4.3. -/
def IsLeftViolated (X : KLRWObject parameters) : Prop :=
  X.strandSeq.toList.head?.map StrandData.color = some .black

/-- An object is *violated* if its rightmost or leftmost strand is black. -/
def IsViolated (X : KLRWObject parameters) : Prop :=
  IsRightViolated X ∨ IsLeftViolated X

instance : DecidablePred (IsRightViolated (parameters := parameters)) := fun _ => decEq _ _

instance : DecidablePred (IsLeftViolated (parameters := parameters)) := fun _ => decEq _ _

instance : DecidablePred (IsViolated (parameters := parameters)) := fun X =>
  inferInstanceAs (Decidable (IsRightViolated X ∨ IsLeftViolated X))

/-- The idempotent $f = \sum_{X \text{ violated}} e_X$, is the sum of the straight-line idempotents
$e_X$ over all violated objects $X$. -/
noncomputable def violatedIdem (parameters : KLRWStructure V) : KLRWAlg R parameters :=
  ∑ X ∈ Finset.univ.filter (IsViolated (parameters := parameters)), idem_morph R X

/-- `violatedIdem` is idempotent, being a partial sum of orthogonal idempotents. -/
lemma isIdempotentElem_violatedIdem (parameters : KLRWStructure V) :
    IsIdempotentElem (violatedIdem R parameters) :=
  (completeOrthogonalIdempotents_idem_morph R parameters).isIdempotentElem_sum

/-- $f e_X = e_X$ if $X$ is violated and $0$ otherwise. -/
lemma violatedIdem_mul_idem_morph (X : KLRWObject parameters) :
    violatedIdem R parameters * idem_morph R X =
      if IsViolated X then idem_morph R X else 0 := by
  classical
  simp [violatedIdem, Finset.sum_mul,
    (completeOrthogonalIdempotents_idem_morph R parameters).mul_eq]

/-- $f e_X = e_X$ when $X$ is violated. -/
lemma violatedIdem_mul_idem_morph_of_isViolated {X : KLRWObject parameters}
    (hX : IsViolated X) : violatedIdem R parameters * idem_morph R X = idem_morph R X := by
  rw [violatedIdem_mul_idem_morph, if_pos hX]

/-- $f e_X = 0$ when $X$ is not violated. -/
lemma violatedIdem_mul_idem_morph_of_not_isViolated {X : KLRWObject parameters}
    (hX : ¬IsViolated X) : violatedIdem R parameters * idem_morph R X = 0 := by
  rw [violatedIdem_mul_idem_morph, if_neg hX]

/-- $e_X f = e_X$ when $X$ is violated. -/
lemma idem_morph_mul_violatedIdem_of_isViolated {X : KLRWObject parameters}
    (hX : IsViolated X) : idem_morph R X * violatedIdem R parameters = idem_morph R X :=
  (completeOrthogonalIdempotents_idem_morph R parameters).mul_sum_of_mem (by simpa using hX)

/-- $e_X f = 0$ when $X$ is not violated. -/
lemma idem_morph_mul_violatedIdem_of_not_isViolated {X : KLRWObject parameters}
    (hX : ¬IsViolated X) : idem_morph R X * violatedIdem R parameters = 0 :=
  (completeOrthogonalIdempotents_idem_morph R parameters).mul_sum_of_notMem (by simpa using hX)

end KLRW
