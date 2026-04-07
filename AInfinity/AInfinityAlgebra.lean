module

public import Mathlib
public import AInfinity.Stasheff

@[expose] public section

open CategoryTheory Finset AInfinityTheory

noncomputable section

namespace AInfinityAlgebraTheory

universe u v
variable {β : Type v} [Grading β]
variable {n : ℕ}

structure AInfinityAlgStruct (R : Type u) [CommRing R]
    (A : GradedRModule (β := β) (R := R)) where
  m :
    (n : ℕ) →
    (deg : Fin n → β) →
    MultilinearMap R (fun i => A (deg i))
      (A (operationTargetDeg deg))

namespace AInfinityAlgStruct

variable {R : Type u} [CommRing R]
variable {A : GradedRModule (β := β) (R := R)}

/-- The `(r,s)` summand in the arity-`n` Stasheff relation. -/
def stasheffTerm
  (X : AInfinityAlgStruct R A)
  (n : ℕ)
  (deg : Fin n → β)
  (x : ∀ i, A (deg i))
  (r s : ℕ)
  (hs : 1 ≤ s)
  (hr : r + s ≤ n) :
  A (stasheffTargetDeg deg) :=
  algebraStasheffTerm X.m n deg x r s hs hr

/--
A single summand in the Stasheff sum, returning `0` when the indices are invalid.
This is the object that appears inside the double finite sum.
-/
def stasheffSummand
  (X : AInfinityAlgStruct (β := β) R A)
  (n : ℕ)
  (deg : Fin n → β)
  (x : ∀ i, A (deg i))
  (r s : ℕ) :
  A (stasheffTargetDeg deg) :=
  if h : validStasheffIndices n r s then
    X.stasheffTerm n deg x r s h.1 h.2
  else
    0

/-- The sign parity for the `(r,s)` Stasheff term:
    `sign(deg(r+s)) + ⋯ + sign(deg(n-1)) - (n-r-s)` in `ZMod 2`.
    This computes the parity of `|a_{r+s+1}| + ⋯ + |a_n| - t` where `t = n - r - s`. -/
def stasheffSignParity
    (deg : Fin n → β)
    (r s : ℕ)
    (hr : r + s ≤ n) : Parity :=
  (∑ i : Fin (n - r - s), Grading.sign (deg ⟨r + s + i.val, by omega⟩)) -
    ((n - r - s : ℕ) : Parity)

/-- The sign `(-1)^(|a_{r+s+1}| + ⋯ + |a_n| - t)` as an integer,
    defaulting to `1` for invalid indices. -/
def stasheffSign
    (deg : Fin n → β)
    (r s : ℕ) : ℤ :=
  if h : r + s ≤ n then
    (-1) ^ (stasheffSignParity deg r s h).val
  else
    1

/-- The full Stasheff sum in arity `n`, with Koszul signs. -/
def stasheffSum
  (X : AInfinityAlgStruct (β := β) R A)
  (n : ℕ)
  (deg : Fin n → β)
  (x : ∀ i, A (deg i)) :
  A (stasheffTargetDeg deg) :=
  ∑ r ∈ Finset.range (n + 1),
    ∑ s ∈ Finset.Ico 1 (n - r + 1),
      (stasheffSign deg r s) • (X.stasheffSummand n deg x r s)

/-- The Stasheff identities as a property of the raw A∞ data. -/
def satisfiesStasheff
  (X : AInfinityAlgStruct (β := β) R A) : Prop :=
  ∀ (n : ℕ) (deg : Fin n → β) (x : ∀ i, A (deg i)),
    X.stasheffSum n deg x = 0

/-- If the indices are valid, the summand is exactly the corresponding term. -/
lemma stasheffSummand_eq_term
  (X : AInfinityAlgStruct (β := β) R A)
  (n : ℕ)
  (deg : Fin n → β)
  (x : ∀ i, A (deg i))
  (r s : ℕ)
  (h : validStasheffIndices n r s) :
  X.stasheffSummand n deg x r s
    = X.stasheffTerm n deg x r s h.1 h.2 := by
  unfold stasheffSummand
  aesop

/-- If the indices are invalid, the summand vanishes. -/
lemma stasheffSummand_eq_zero
  (X : AInfinityAlgStruct (β := β) R A)
  (n : ℕ)
  (deg : Fin n → β)
  (x : ∀ i, A (deg i))
  (r s : ℕ)
  (h : ¬ validStasheffIndices n r s) :
  X.stasheffSummand n deg x r s = 0 := by
  unfold AInfinityAlgStruct.stasheffSummand
  aesop

end AInfinityAlgStruct

/-- An A∞-algebra is raw data together with the Stasheff identities. -/
class AInfinityAlgebra (R : Type u) [CommRing R]
    (A : GradedRModule (β := β) (R := R))
  extends AInfinityAlgStruct (β := β) R A where
  stasheff :
    AInfinityAlgStruct.satisfiesStasheff
      (β := β) toAInfinityAlgStruct

namespace AInfinityAlgebra

variable {R : Type u} [CommRing R]
variable {A : GradedRModule (β := β) (R := R)}

/-- Re-export the Stasheff identity in a convenient form. -/
lemma stasheff_eq_zero
  (X : AInfinityAlgebra (β := β) R A)
  (n : ℕ)
  (deg : Fin n → β)
  (x : ∀ i, A (deg i)) :
  X.toAInfinityAlgStruct.stasheffSum n deg x = 0 :=
  X.stasheff n deg x

end AInfinityAlgebra

end AInfinityAlgebraTheory
