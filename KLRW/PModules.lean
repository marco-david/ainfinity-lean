/-
Copyright (c) 2026 Hallvard Hareide. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hallvard Hareide
-/

module

public import KLRW.KLRWCategory

/-!
# Violated idempotents in the KLRW algebra

We work inside the KLRW algebra $A$ = `KLRWAlg R parameters`. For an object $X$, write $e_X$ for
the straight-line idempotent `idem_morph R X`. An object is *violated* if its leftmost or rightmost
strand is black. The element
$$f = \sum_{X \text{ violated}} e_X$$
(`violatedIdem`) is an idempotent. It is the first ingredient in the construction of the
module $L_λ = eA/eAfA$, where $e$ is a specific idempotent.

## Main definitions

* `KLRW.IsLeftViolated`, `KLRW.IsRightViolated`: an object is left (resp. right) violated if its
  leftmost (resp. rightmost) strand is black.
* `KLRW.IsViolated`: an object is violated if it is left or right violated.
* `KLRW.violatedIdem`: the idempotent $f = \sum_{X \text{ violated}} e_X$.

## Implementation notes

This implementation is based on Ben Webster's *Knot invariants and higher representation theory*,
Definition 4.3. There are two main discrepancies.

Firstly, Webster defines violated to only concern what we call left violated. This is to define the
cyclotomic quotient $A/AgA$ with $g$ the sum of all idempotents of left violated objects
(Definition 4.6).
Following LePage–Shende (Section 2.1), who work with the KLRW category without passing to a
cyclotomic quotient, this project works inside the full KLRW algebra $A$.
For the constructions that later require quotienting by right violated diagrams inside the
cyclotomic quotient (e.g. $L_λ$), we instead quotient by all violated diagrams in $A$. We expect
that this results in an isomorphic module, but there are some nuances in this translation which are
yet to be spelled out (see TODO).

Secondly, Webster defines violated to be a property of diagrams, whereas we define
violated objects. A diagram $a$ is violated in Webster's sense iff it factors as
$a = b \, e_X \, c$ for some left violated object $X$. One can likewise define the notion of
right violated diagrams, and the diagrams that are left violated or right violated span the
two-sided ideal $AfA$.

## TODO

* Formalize the characterizations of violated diagrams above.
* Prove that our $L_λ$ is isomorphic to Webster's.
* Spell out nuances of transitioning from $A$-modules to $A/AgA$-modules. For example, the
  transition from projective $A$-resolutions to projective $A/AgA$ resolutions.

## References

* [B. Webster, *Knot invariants and higher representation theory*, Mem. Amer. Math. Soc. 250
  (2017), no. 1191](https://arxiv.org/abs/1309.3796)
* [E. LePage and V. Shende, *Aganagic's invariant is Khovanov homology*
  (2025)](https://arxiv.org/abs/2505.00327)
-/

@[expose] public section

namespace KLRW

variable {V : Type*} [DecidableEq V] [Fintype V]
variable {parameters : KLRWStructure V}
variable {R : Type*} [CommRing R]


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

variable (R) in
/-- The idempotent $f = \sum_{X \text{ violated}} e_X$, where $e_X$ is the straight-line
idempotent `idem_morph R X`. -/
noncomputable def violatedIdem (parameters : KLRWStructure V) : KLRWAlg R parameters :=
  ∑ X ∈ Finset.univ.filter (IsViolated (parameters := parameters)), idem_morph R X

variable (R) in
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
  rw [violatedIdem_mul_idem_morph, ite_eq_left hX]

/-- $f e_X = 0$ when $X$ is not violated. -/
lemma violatedIdem_mul_idem_morph_of_not_isViolated {X : KLRWObject parameters}
    (hX : ¬IsViolated X) : violatedIdem R parameters * idem_morph R X = 0 := by
  rw [violatedIdem_mul_idem_morph, ite_eq_right hX]

/-- $e_X f = e_X$ when $X$ is violated. -/
lemma idem_morph_mul_violatedIdem_of_isViolated {X : KLRWObject parameters}
    (hX : IsViolated X) : idem_morph R X * violatedIdem R parameters = idem_morph R X :=
  (completeOrthogonalIdempotents_idem_morph R parameters).mul_sum_of_mem (by simpa using hX)

/-- $e_X f = 0$ when $X$ is not violated. -/
lemma idem_morph_mul_violatedIdem_of_not_isViolated {X : KLRWObject parameters}
    (hX : ¬IsViolated X) : idem_morph R X * violatedIdem R parameters = 0 :=
  (completeOrthogonalIdempotents_idem_morph R parameters).mul_sum_of_notMem (by simpa using hX)

end KLRW
