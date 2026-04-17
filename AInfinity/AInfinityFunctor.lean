module

public import Mathlib
public import AInfinity.Grading
public import AInfinity.AInfinityCategory

@[expose] public section

open CategoryTheory AInfinityTheory AInfinityCategoryTheory

noncomputable section

namespace AInfinityFunctorTheory

universe u v w x y
variable {β_A : Type v} [Grading β_A]
variable {β_B : Type w} [Grading β_B]

/-- Target degree of `φ_n` applied to inputs of the given degrees.
    `φ_n` has degree `1 − n`, so the output lives in
    `∑ i, deg_trans(deg i) + ofInt(1 − n)` in `β_B`. -/
abbrev functorTargetDeg
    (deg_trans : β_A →+ β_B)
    {n : ℕ} (deg : Fin n → β_A) : β_B :=
  (∑ i, deg_trans (deg i)) + shift_ofInt (1 - (n : ℤ))

/-- Target module of `φ_n` for a chain of objects and input degrees. -/
abbrev functorTargetType
    {R : Type u} [CommRing R]
    {ObjA : Type x} {ObjB : Type y}
    (BHom : ObjB → ObjB → GradedRModule (β := β_B) (R := R))
    (F : ObjA → ObjB)
    (deg_trans : β_A →+ β_B)
    {n : ℕ+}
    (obj : Fin ((n : ℕ) + 1) → ObjA)
    (deg : Fin (n : ℕ) → β_A) :
    ModuleCat R :=
  (BHom (F (obj 0)) (F (obj (Fin.last n)))) (functorTargetDeg deg_trans deg)

/-- Raw data for an A∞ functor between graded `R`-linear quivers. -/
structure AInfinityFunctorData
    {R : Type u} [CommRing R]
    {ObjA : Type x} {ObjB : Type y}
    (A : RLinearGQuiver (β := β_A) R ObjA)
    (B : RLinearGQuiver (β := β_B) R ObjB) where
  /-- The map on objects. -/
  F : ObjA → ObjB
  /-- Group homofunctor translating degrees from `β_A` to `β_B`. -/
  deg_trans : β_A →+ β_B
  /-- `deg_trans` is compatible with the integer embeddings. -/
  deg_trans_ofInt : ∀ n : ℤ, deg_trans (Grading.ofInt n) = Grading.ofInt n
  /-- `deg_trans` preserves sign/parity. -/
  deg_trans_sign : ∀ b : β_A, Grading.sign (deg_trans b) = Grading.sign b

  phi :
    {n : ℕ+} →
    (obj : Fin ((n : ℕ) + 1) → ObjA) →
    (deg : Fin (n : ℕ) → β_A) →
    MultilinearMap R
      (fun i : Fin (n : ℕ) => composableHomType A.Hom obj deg i)
      (functorTargetType B.Hom F deg_trans obj deg)



namespace AInfinityFunctorData

variable {R : Type u} [CommRing R]
variable {ObjA : Type x} {ObjB : Type y}
variable {A : RLinearGQuiver (β := β_A) R ObjA}
variable {B : RLinearGQuiver (β := β_B) R ObjB}

/-- Target degree of the functor equation.
    Both sides of the A∞-functor equation land in
    `∑ i, deg_trans(deg i) + ofInt(2 − n)` in `β_B`. -/
abbrev functorEqTargetDeg
    (deg_trans : β_A →+ β_B)
    {n : ℕ} (deg : Fin n → β_A) : β_B :=
  (∑ i, deg_trans (deg i)) + shift_ofInt (2 - (n : ℤ))

abbrev functorEqTargetType
    {R : Type u} [CommRing R]
    {ObjA : Type x} {ObjB : Type y}
    (BHom : ObjB → ObjB → GradedRModule (β := β_B) (R := R))
    (F : ObjA → ObjB)
    (deg_trans : β_A →+ β_B)
    {n : ℕ}
    (obj : Fin (n + 1) → ObjA)
    (deg : Fin n → β_A) :
    ModuleCat R :=
  (BHom (F (obj 0)) (F (obj (Fin.last n)))) (functorEqTargetDeg deg_trans deg)


/- The LHS of the A∞-functor equation is:
  `∑_{r+s+t=n, s≥1} (-1)^† φ_{r+1+t}(a_1, …, a_r, m^A_s(a_{r+1}, …, a_{r+s}), a_{r+s+1}, …, a_n)`
where `† = |a_{r+s+1}| + ⋯ + |a_n| − t` (the same sign as in the Stasheff relation).
Structurally this is the same as the Stasheff term, except the *outer* operation is `φ`
(mapping `A → B`) rather than `m^A` (mapping `A → A`).
-/
section LHS
--helper lemmas
lemma functorLHS_deg_compat
    (F : AInfinityFunctorData A B)
    {n : ℕ}
    (deg : Fin n → β_A)
    (r s : ℕ)
    (hr : r + s ≤ n) :
    functorTargetDeg F.deg_trans (stasheffDegOut deg r s hr) =
    functorEqTargetDeg F.deg_trans deg := by
  unfold functorTargetDeg functorEqTargetDeg;
  rw [ ← map_sum ];
  rw [ show F.deg_trans ( ∑ x : Fin ( n + 1 - s ), stasheffDegOut deg r s hr x ) = F.deg_trans ( ∑ i : Fin n, deg i + shift_ofInt ( 2 - ( s : ℤ ) ) ) by
        exact congr_arg _ ( stasheffDegOut_sum_core deg r s hr ) ];
  rw [ map_add, show F.deg_trans ( shift_ofInt ( 2 - s : ℤ ) ) = shift_ofInt ( 2 - s : ℤ ) from ?_, show ( n + 1 - s : ℕ ) = ( n - s ) + 1 from ?_ ] ; norm_num ; ring;
  · simp +decide [ add_assoc, Nat.cast_sub ( show s ≤ n from by linarith ) ];
    simp +decide [ shift_ofInt ];
  · rw [ Nat.sub_add_comm ( by linarith ) ];
  · exact F.deg_trans_ofInt _


/-- The `(r, s)` summand on the LHS of the functor equation:

(obj : Fin ((n : ℕ) + 1) → ObjA) →
    (deg : Fin (n : ℕ) → β_A)
    `φ_{r+1+t}(a_1, …, a_r, m^A_s(a_{r+1}, …, a_{r+s}), a_{r+s+1}, …, a_n)`. -/
def functorLHSTerm
    (X_A : AInfinityCategoryData R ObjA)
    (F : AInfinityFunctorData X_A.toRLinearGQuiver B)
    (n : ℕ)
    (obj : Fin (n + 1) → ObjA)
    (deg : Fin n → β_A)
    (x : ∀ i : Fin n, composableHomType X_A.Hom obj deg i)
    (r s : ℕ)
    (hs : 1 ≤ s)
    (hr : r + s ≤ n) :
    functorEqTargetType B.Hom F.F F.deg_trans obj deg := by
  -- Inner: apply m^A_s to the (r+1, …, r+s) block
  let degIn := stasheffDegIn deg r s hr
  let objIn := stasheffObjIn obj r s hr
  let xIn : ∀ i : Fin s, composableHomType X_A.Hom objIn degIn i := fun i => by
    simpa [composableHomType, objIn, stasheffObjIn, degIn, stasheffDegIn]
      using x ⟨r + i.val, by omega⟩
  let inner := X_A.m (n := ⟨s, hs⟩) objIn degIn xIn

  -- Outer: apply φ_{n+1-s} to (a_1, …, a_r, inner, a_{r+s+1}, …, a_n)
  let outerN : ℕ := (n : ℕ) + 1 - s
  let degOut := stasheffDegOut deg r s hr
  let objOut := stasheffObjOut obj r s hr
  let xOut : ∀ i : Fin outerN, composableHomType X_A.Hom objOut degOut i := by
    intro i
    by_cases hlt : i.val < r
    · simpa [composableHomType, objOut, stasheffObjOut, degOut, stasheffDegOut, hlt,
        Nat.le_of_lt hlt]
        using x ⟨i.val, by omega⟩
    · by_cases heq : i.val = r
      · simpa
          [composableHomType, operationTargetType, objIn, stasheffObjIn,
            degIn, stasheffDegIn, objOut, stasheffObjOut, degOut, stasheffDegOut,
            stasheffInnerDeg, hlt, heq]
          using inner
      · have hgt : ¬ i.val ≤ r := by omega
        have hsucc : i.val + s - 1 + 1 = i.val + s := by omega
        simpa
          [composableHomType, objOut, stasheffObjOut, degOut, stasheffDegOut,
            hlt, heq, hgt, hsucc]
          using x ⟨i.val + s - 1, by omega⟩
  have houterN : 0 < outerN := by
    dsimp [outerN]
    omega
  let outer := F.phi (n := ⟨outerN, houterN⟩) objOut degOut xOut

  have hdeg : functorEqTargetType B.Hom F.F F.deg_trans obj deg =
    functorTargetType (n := ⟨outerN, houterN⟩) B.Hom F.F F.deg_trans objOut degOut:= by
    sorry

  exact hdeg ▸ outer

/-- The full LHS sum with signs:
    `∑_{r,s} (-1)^† φ_{r+1+t}(…, m^A_s(…), …)`. -/
def functorLHSSum
    (X_A : AInfinityCategoryData R ObjA)
    (F : AInfinityFunctorData X_A.toRLinearGQuiver B)
    (n : ℕ)
    (obj : Fin (n + 1) → ObjA)
    (deg : Fin n → β_A)
    (x : ∀ i : Fin n, composableHomType X_A.Hom obj deg i) :
    functorEqTargetType B.Hom F.F F.deg_trans obj deg :=
  Finset.sum ((Finset.range (n + 1)).attach) fun r =>
    Finset.sum ((Finset.Ico 1 (n - r.1 + 1)).attach) fun s =>
      let h : validStasheffIndices n r.1 s.1 :=
        validStasheffIndices_of_mem_ranges (n := (n : ℕ)) r.2 s.2
      (stasheffSign deg r.1 s.1 h.2) •
        (F.functorLHSTerm X_A n obj deg x r.1 s.1 h.1 h.2)


end LHS


end AInfinityFunctorData

end AInfinityFunctorTheory
