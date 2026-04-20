module

public import Mathlib
public import AInfinity.AInfinityCategory

@[expose] public section

open CategoryTheory Finset AInfinityTheory AInfinityCategoryTheory

noncomputable section

namespace AInfinityExamples

universe u

local instance : Grading ℤ where
  toAddCommGroup := inferInstance
  ofInt := AddMonoidHom.id ℤ
  sign := Int.castAddHom Parity
  sign_ofInt n := by
    simp

variable (R : Type u) [CommRing R]
variable (S : Type u) [CommRing S] [Algebra R S]

def concentratedAt0 : GradedRModule (β := ℤ) R :=
  fun i => if i = 0 then ModuleCat.of R S else ModuleCat.of R PUnit

abbrev OneObj : Type := PUnit

abbrev oneObjHom : OneObj → OneObj → GradedRModule (β := ℤ) R :=
  fun _ _ => concentratedAt0 (R := R) (S := S)

@[reducible] def concentratedAt0Quiver
    (R : Type u) [CommRing R]
    (S : Type u) [CommRing S] [Algebra R S] :
    RLinearGQuiver (β := ℤ) R OneObj where
  GHom' _ _ := concentratedAt0 (R := R) (S := S)

def degreeZeroMul :
    MultilinearMap R
      (fun _ : Fin 2 => ModuleCat.of R S)
      (ModuleCat.of R S) :=
  MultilinearMap.mk'
    (R := R)
    (ι := Fin 2)
    (M₁ := fun _ : Fin 2 => ModuleCat.of R S)
    (M₂ := ModuleCat.of R S)
    (fun x => x 0 * x 1)
    (by
      intro m i x y
      fin_cases i
      · simp [add_mul]
      · simp [mul_add])
    (by
      intro m i a x
      fin_cases i
      · simp
      · simp)

def concentratedAt0Map
    {n : ℕ} [NeZero n]
    (deg : Fin n → ℤ) :
    MultilinearMap R
      (fun i : Fin n => concentratedAt0 (R := R) (S := S) (deg i))
      (concentratedAt0 (R := R) (S := S) (operationTargetDeg deg)) := by
  classical
  by_cases hn : n = 2
  · subst hn
    by_cases h0 : deg 0 = 0
    · by_cases h1 : deg 1 = 0
      · have hdeg : deg = fun _ : Fin 2 => 0 := by
          ext i
          fin_cases i <;> simp [h0, h1]
        subst hdeg
        simpa [concentratedAt0, operationTargetDeg, shift_ofInt] using
          degreeZeroMul (R := R) (S := S)
      · exact 0
    · exact 0
  · exact 0

@[simp]
lemma concentratedAt0Map_ne_two
    {n : ℕ} [NeZero n]
    (deg : Fin n → ℤ)
    (hn : n ≠ 2) :
    concentratedAt0Map (R := R) (S := S) deg = 0 := by
  simp [concentratedAt0Map, hn]

@[simp]
lemma concentratedAt0Map_two_left_ne_zero
    (deg : Fin 2 → ℤ)
    (h0 : deg 0 ≠ 0) :
    concentratedAt0Map (R := R) (S := S) deg = 0 := by
  simp [concentratedAt0Map, h0]

@[simp]
lemma concentratedAt0Map_two_right_ne_zero
    (deg : Fin 2 → ℤ)
    (h0 : deg 0 = 0)
    (h1 : deg 1 ≠ 0) :
    concentratedAt0Map (R := R) (S := S) deg = 0 := by
  simp [concentratedAt0Map, h0, h1]

@[simp]
lemma concentratedAt0Map_two_zero_zero_apply
    (x : ∀ _ : Fin 2, ModuleCat.of R S) :
    concentratedAt0Map (R := R) (S := S) (fun _ : Fin 2 => 0) x = x 0 * x 1 := by
  rfl

@[reducible] def concentratedAt0CategoryData :
    AInfinityCategoryData (β := ℤ) R OneObj where
  toRLinearGQuiver := concentratedAt0Quiver (R := R) (S := S)
  m := by
    intro n _ obj deg
    simpa [composableHomType, operationTargetType, concentratedAt0] using
      concentratedAt0Map (R := R) (S := S) deg

@[simp]
lemma concentratedAt0CategoryData_m_ne_two
    {n : ℕ} [NeZero n]
    (obj : Fin (n + 1) → OneObj)
    (deg : Fin n → ℤ)
    (hn : n ≠ 2) :
    (concentratedAt0CategoryData (R := R) (S := S)).m obj deg = 0 := by
  simpa [concentratedAt0CategoryData, composableHomType, operationTargetType, concentratedAt0] using
    concentratedAt0Map_ne_two (R := R) (S := S) deg hn

@[simp]
lemma concentratedAt0CategoryData_m_two_left_ne_zero
    (obj : Fin 3 → OneObj)
    (deg : Fin 2 → ℤ)
    (h0 : deg 0 ≠ 0) :
    (concentratedAt0CategoryData (R := R) (S := S)).m obj deg = 0 := by
  simpa [concentratedAt0CategoryData, composableHomType, operationTargetType, concentratedAt0] using
    concentratedAt0Map_two_left_ne_zero (R := R) (S := S) deg h0

@[simp]
lemma concentratedAt0CategoryData_m_two_right_ne_zero
    (obj : Fin 3 → OneObj)
    (deg : Fin 2 → ℤ)
    (h0 : deg 0 = 0)
    (h1 : deg 1 ≠ 0) :
    (concentratedAt0CategoryData (R := R) (S := S)).m obj deg = 0 := by
  simpa [concentratedAt0CategoryData, composableHomType, operationTargetType, concentratedAt0] using
    concentratedAt0Map_two_right_ne_zero (R := R) (S := S) deg h0 h1

lemma concentratedAt0CategoryData_m_two_zero_zero_apply
    (obj : Fin 3 → OneObj)
    (x : ∀ _ : Fin 2, ModuleCat.of R S) :
    (concentratedAt0CategoryData (R := R) (S := S)).m
      obj (fun _ : Fin 2 => 0) x = x 0 * x 1 := by
  rfl

lemma concentratedAt0_eq_zero_of_ne_zero_degree
    {d : ℤ}
    (hd : d ≠ 0)
    (x : concentratedAt0 (R := R) (S := S) d) :
    x = 0 := by
  haveI : Subsingleton (concentratedAt0 (R := R) (S := S) d) := by
    simpa [concentratedAt0, hd] using
      (inferInstance : Subsingleton (ModuleCat.of R PUnit))
  exact Subsingleton.elim x 0

lemma concentratedAt0CategoryData_m_eq_zero_of_coord_zero
    {n : ℕ} [NeZero n]
    (obj : Fin (n + 1) → OneObj)
    (deg : Fin n → ℤ)
    (x : ∀ i : Fin n,
      composableHomType
        (fun _ _ => concentratedAt0 (R := R) (S := S))
        obj deg i)
    (i : Fin n)
    (hx : x i = 0) :
    (concentratedAt0CategoryData (R := R) (S := S)).m obj deg x = 0 := by
  exact
    MultilinearMap.map_coord_zero
      ((concentratedAt0CategoryData (R := R) (S := S)).m obj deg) i hx

end AInfinityExamples
