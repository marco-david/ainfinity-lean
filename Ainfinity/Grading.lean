module

public import Mathlib

@[expose] public section

open ChainComplex CategoryTheory DirectSum GradedMonoid GradedObject

namespace AInfinityCategoryTheory


/- Grading policy:
In order to define A∞-relations etc., we need to assign signs to elements of the
grading type β. Policy:
• β remains arbitrary type
• Include the datum of a cast β → ℤ/2ℤ.
• Include the datum of a cast ℤ → β or ℤ/2ℤ → β.
• For sanity, require that the composition ℤ → β → ℤ/2ℤ is the standard projection, or ℤ/2ℤ → β → ℤ/2ℤ is the identity.

In consequence,
• Sign is computed via β → ℤ/2ℤ
• Correct degree is |a_1| + … + |a_k| + (2-k) ∈ β.
-/

inductive Int_or_Parity where
  | int
  | parity

/-- additive signs as ℤ/2ℤ -/
abbrev Parity := ZMod 2      -- values:  0 or 1

def correct_type (kind : Int_or_Parity) : Type 0 :=
  match kind with
  | Int_or_Parity.int => ℤ
  | Int_or_Parity.parity => Parity

def toParity {kind : Int_or_Parity} (n : correct_type kind) : Parity := by
  cases h : kind

  -- case int
  have h : correct_type kind = ℤ := by
    simpa [correct_type] using congrArg correct_type h
  have result : ℤ := by
    simpa [h] using n
  exact (result : Parity)

  -- case parity
  have h : correct_type kind = Parity := by
    simpa [correct_type] using congrArg correct_type h
  have result : Parity := by
    simpa [h] using n
  exact (result : Parity)

def nat_to_correct_type (kind : Int_or_Parity) (n : ℤ) : correct_type kind := by
  cases h : kind

  have aux : correct_type Int_or_Parity.int = ℤ := by rfl
  simpa [aux] using n

  have aux : correct_type Int_or_Parity.parity = Parity := by rfl
  simpa [aux] using (n : Parity)

class Has_Int_or_Parity.{u} (β : Type u) where
  kind : Int_or_Parity
  sign_cast : β → Parity
  deg_cast : (correct_type kind) → β
  cast_compat : ∀n : correct_type kind, sign_cast (deg_cast n) = toParity n

instance : Has_Int_or_Parity (ZMod 2) where
  kind := Int_or_Parity.parity
  sign_cast := fun n ↦ n
  deg_cast := fun n ↦ n
  cast_compat := by intro n; rfl

instance : Has_Int_or_Parity ℤ where
  kind := Int_or_Parity.int
  sign_cast := fun n ↦ n
  deg_cast := fun n ↦ n
  cast_compat := by intro n; rfl

class GradingCore.{u} (β : Type u) extends AddCommGroup β, Has_Int_or_Parity β

class GQuiver.{u, v, w} (β : Type u) (obj : Type v) where
  /-- The type of morphisms between a given source and target. -/
  data : obj → obj → GradedObject β (Type w)


end AInfinityCategoryTheory
