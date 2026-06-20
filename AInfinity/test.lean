module

public import Mathlib
public import AInfinity.Grading

@[expose] public section

open CategoryTheory Finset AInfinityTheory

noncomputable section

namespace AInfinityTheory

universe u v w
variable {β : Type v} [GradingIndex β]
variable {n : ℕ}

/-- Target degree of the `n`-ary operation `m`. -/
abbrev operationTargetDeg
    (deg : Fin n → β) : β :=
  (∑ i, deg i) + shift_ofInt (2 - (n : ℤ))

/-- Target degree of the arity-`n` Stasheff relation. -/
abbrev stasheffTargetDeg
    (deg : Fin n → β) : β :=
  (∑ i, deg i) + shift_ofInt (3 - (n : ℤ))

/-- Valid index pairs for an arity-`n` Stasheff summand. -/
abbrev ValidStasheffIndices (n r s : ℕ) : Prop :=
  1 ≤ s ∧ r + s ≤ n

/-- The type of the `i`-th morphism in a composable string of objects and degrees. -/
abbrev ComposableHomType
    {R : Type u} [CommRing R]
    {Obj : Type w}
    (Hom : Obj → Obj → GradedRModule (β := β) (R := R))
    {n : ℕ}
    (obj : Fin (n + 1) → Obj)
    (deg : Fin n → β)
    (i : Fin n) : ModuleCat R :=
  Hom
    (obj ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
    (obj ⟨i.val + 1, by omega⟩)
    (deg i)

/-- The target type of the `n`-ary operation on a composable string. -/
abbrev operationTargetType
    {R : Type u} [CommRing R]
    {Obj : Type w}
    (Hom : Obj → Obj → GradedRModule (β := β) (R := R))
    {n : ℕ}
    (obj : Fin (n + 1) → Obj)
    (deg : Fin n → β) : ModuleCat R :=
  Hom (obj 0) (obj (Fin.last n)) (operationTargetDeg deg)


class AInfinityCategoryStruct
    (R : Type u) [CommRing R] (Obj : Type w)
    extends RLinearGQuiver (β := β) R Obj where
  m :
    {n : ℕ} → [NeZero n] →
    (obj : Fin (n + 1) → Obj) →
    (deg : Fin n → β) →
    MultilinearMap R
      (fun i : Fin n => ComposableHomType (GHom β R) obj deg i)
      (operationTargetType (GHom β R) obj deg)

end AInfinityTheory
