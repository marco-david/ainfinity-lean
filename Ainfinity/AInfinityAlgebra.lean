import Mathlib
import Ainfinity.Grading

open CategoryTheory Finset AInfinityCategoryTheory

noncomputable section

namespace AInfinityAlgebraTheory

universe u v
variable {β : Type v} [GradingCore β] [AddCommGroup β]

def shiftOfInt (n : ℤ) : β :=
  Has_Int_or_Parity.deg_cast
    (β := β)
    (nat_to_correct_type (Has_Int_or_Parity.kind (β := β)) n)

abbrev GradedRModule (R : Type u) [CommRing R] :=
  GradedObject β (ModuleCat.{u} R)

structure AInfinityAlgebraData (R : Type u) [CommRing R] where
  A : GradedRModule (β := β) (R := R)

  m :
    (n : ℕ) →
    (deg : Fin n → β) →
    MultilinearMap R (fun i => A (deg i))
      (A ((∑ i, deg i) + shiftOfInt (β := β) (2 - (n : ℤ))))

namespace AInfinityAlgebraData

variable {R : Type u} [CommRing R]

abbrev validStasheffIndices (n r s : ℕ) : Prop :=
  1 ≤ s ∧ r + s ≤ n

def stasheffTerm
  (X : AInfinityAlgebraData (β := β) R)
  (n : ℕ)
  (deg : Fin n → β)
  (x : ∀ i, X.A (deg i))
  (r s : ℕ)
  (hs : 1 ≤ s)
  (hr : r + s ≤ n) :
  X.A ((∑ i, deg i) + shiftOfInt (β := β) (3 - (n : ℤ))) :=
by
  /-
  This is the place where the real implementation goes.

  Recommended pattern:
    let degIn : Fin s → β := ...
    let xIn   : ∀ i : Fin s, X.A (degIn i) := ...
    let inner : X.A (...) := X.m s degIn xIn

    let degOut : Fin (n + 1 - s) → β := ...
    let xOut   : ∀ i : Fin (n + 1 - s), X.A (degOut i) := ...

    have hdeg : ... = ((∑ i, deg i) + shiftOfInt (β := β) (3 - (n : ℤ))) := ...
    exact cast (by rw [hdeg]) (X.m (n + 1 - s) degOut xOut)

  Keeping these as local lets is usually better than making all of them top-level defs.
  -/
  sorry

/--
A single summand in the Stasheff sum, returning `0` when the indices are invalid.
This is the object that appears inside the double finite sum.
-/
def stasheffSummand
  (X : AInfinityAlgebraData (β := β) R)
  (n : ℕ)
  (deg : Fin n → β)
  (x : ∀ i, X.A (deg i))
  (r s : ℕ) :
  X.A ((∑ i, deg i) + shiftOfInt (β := β) (3 - (n : ℤ))) :=
  if h : validStasheffIndices n r s then
    X.stasheffTerm n deg x r s h.1 h.2
  else
    0

/-- The full Stasheff sum in arity `n`. -/
def stasheffSum
  (X : AInfinityAlgebraData (β := β) R)
  (n : ℕ)
  (deg : Fin n → β)
  (x : ∀ i, X.A (deg i)) :
  X.A ((∑ i, deg i) + shiftOfInt (β := β) (3 - (n : ℤ))) :=
  ∑ r ∈ Finset.range (n + 1),
    ∑ s ∈ Finset.Ico 1 (n - r + 1),
      X.stasheffSummand n deg x r s

/-- The Stasheff identities as a property of the raw A∞ data. -/
def satisfiesStasheff
  (X : AInfinityAlgebraData (β := β) R) : Prop :=
  ∀ (n : ℕ) (deg : Fin n → β) (x : ∀ i, X.A (deg i)),
    X.stasheffSum n deg x = 0

/-- If the indices are valid, the summand is exactly the corresponding term. -/
lemma stasheffSummand_eq_term
  (X : AInfinityAlgebraData (β := β) R)
  (n : ℕ)
  (deg : Fin n → β)
  (x : ∀ i, X.A (deg i))
  (r s : ℕ)
  (h : validStasheffIndices n r s) :
  X.stasheffSummand n deg x r s
    = X.stasheffTerm n deg x r s h.1 h.2 := by
  sorry

/-- If the indices are invalid, the summand vanishes. -/
lemma stasheffSummand_eq_zero
  (X : AInfinityAlgebraData (β := β) R)
  (n : ℕ)
  (deg : Fin n → β)
  (x : ∀ i, X.A (deg i))
  (r s : ℕ)
  (h : ¬ validStasheffIndices n r s) :
  X.stasheffSummand n deg x r s = 0 := by
  sorry

end AInfinityAlgebraData

/-- An A∞-algebra is raw data together with the Stasheff identities. -/
structure AInfinityAlgebra (R : Type u) [CommRing R]
  extends AInfinityAlgebraData (β := β) R where
  stasheff :
    AInfinityAlgebraData.satisfiesStasheff
      (β := β) toAInfinityAlgebraData

namespace AInfinityAlgebra

variable {R : Type u} [CommRing R]

/-- Re-export the Stasheff identity in a convenient form. -/
lemma stasheff_eq_zero
  (X : AInfinityAlgebra (β := β) R)
  (n : ℕ)
  (deg : Fin n → β)
  (x : ∀ i, X.A (deg i)) :
  X.toAInfinityAlgebraData.stasheffSum n deg x = 0 :=
  X.stasheff n deg x

end AInfinityAlgebra

end AInfinityAlgebraTheory
