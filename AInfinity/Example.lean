module

public import Mathlib
public import AInfinity.AInfinityCategory

@[expose] public section

open CategoryTheory Finset AInfinityTheory

noncomputable section

namespace AInfinityTheory
namespace Examples

universe u

local instance : GradingIndex ℤ where
  toAddCommGroupWithOne := inferInstance
  parity := Int.castAddHom (ZMod 2)
  parity_one := by
    simp

variable (R : Type u) [CommRing R]
variable (S : Type u) [CommRing S] [Algebra R S]

def concentratedAt0 : GradedRModule (β := ℤ) R :=
  fun i => if i = 0 then ModuleCat.of R S else ModuleCat.of R PUnit

abbrev OneObj (_S : Type u) : Type := PUnit

abbrev oneObjHom : OneObj S → OneObj S → GradedRModule (β := ℤ) R :=
  fun _ _ => concentratedAt0 (R := R) (S := S)

instance concentratedAt0Quiver
    (R : Type u) [CommRing R]
    (S : Type u) [CommRing S] [Algebra R S] :
    RLinearGQuiver (β := ℤ) R (OneObj S) where
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

instance concentratedAt0CategoryData
    (R : Type u) [CommRing R]
    (S : Type u) [CommRing S] [Algebra R S] :
    AInfinityCategoryStruct (β := ℤ) R (OneObj S) where
  toRLinearGQuiver := concentratedAt0Quiver (R := R) (S := S)
  m := by
    intro n _ obj deg
    simpa [ComposableHomType, operationTargetType, concentratedAt0] using
      concentratedAt0Map (R := R) (S := S) deg

@[simp]
lemma concentratedAt0CategoryData_m_ne_two
    (R : Type u) [CommRing R]
    (S : Type u) [CommRing S] [Algebra R S]
    {n : ℕ} [NeZero n]
    (obj : Fin (n + 1) → OneObj S)
    (deg : Fin n → ℤ)
    (hn : n ≠ 2) :
    (concentratedAt0CategoryData (R := R) (S := S)).m obj deg = 0 := by
  simpa [concentratedAt0CategoryData, ComposableHomType, operationTargetType, concentratedAt0] using
    concentratedAt0Map_ne_two (R := R) (S := S) deg hn

@[simp]
lemma concentratedAt0CategoryData_m_two_left_ne_zero
    (R : Type u) [CommRing R]
    (S : Type u) [CommRing S] [Algebra R S]
    (obj : Fin 3 → OneObj S)
    (deg : Fin 2 → ℤ)
    (h0 : deg 0 ≠ 0) :
    (concentratedAt0CategoryData (R := R) (S := S)).m obj deg = 0 := by
  simpa [concentratedAt0CategoryData, ComposableHomType, operationTargetType, concentratedAt0] using
    concentratedAt0Map_two_left_ne_zero (R := R) (S := S) deg h0

@[simp]
lemma concentratedAt0CategoryData_m_two_right_ne_zero
    (R : Type u) [CommRing R]
    (S : Type u) [CommRing S] [Algebra R S]
    (obj : Fin 3 → OneObj S)
    (deg : Fin 2 → ℤ)
    (h0 : deg 0 = 0)
    (h1 : deg 1 ≠ 0) :
    (concentratedAt0CategoryData (R := R) (S := S)).m obj deg = 0 := by
  simpa [concentratedAt0CategoryData, ComposableHomType, operationTargetType, concentratedAt0] using
    concentratedAt0Map_two_right_ne_zero (R := R) (S := S) deg h0 h1

lemma concentratedAt0CategoryData_m_two_zero_zero_apply
    (R : Type u) [CommRing R]
    (S : Type u) [CommRing S] [Algebra R S]
    (obj : Fin 3 → OneObj S)
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
    (R : Type u) [CommRing R]
    (S : Type u) [CommRing S] [Algebra R S]
    {n : ℕ} [NeZero n]
    (obj : Fin (n + 1) → OneObj S)
    (deg : Fin n → ℤ)
    (x : ∀ i : Fin n,
      ComposableHomType
        (fun _ _ => concentratedAt0 (R := R) (S := S))
        obj deg i)
    (i : Fin n)
    (hx : x i = 0) :
    (concentratedAt0CategoryData (R := R) (S := S)).m obj deg x = 0 := by
  exact
    MultilinearMap.map_coord_zero
      ((concentratedAt0CategoryData (R := R) (S := S)).m obj deg) i hx

lemma concentratedAt0CategoryData_stasheffTerm_eq_zero_of_ne_three
    (R : Type u) [CommRing R]
    (S : Type u) [CommRing S] [Algebra R S]
    {n : ℕ} [NeZero n]
    (obj : Fin (n + 1) → OneObj S)
    (deg : Fin n → ℤ)
    (x : ∀ i : Fin n,
      ComposableHomType
        (fun _ _ => concentratedAt0 (R := R) (S := S))
        obj deg i)
    (r s : ℕ)
    (hs : 1 ≤ s)
    (hr : r + s ≤ n)
    (hn : n ≠ 3) :
    indexedStasheffTerm
      (fun _ _ => concentratedAt0 (R := R) (S := S))
      (concentratedAt0CategoryData (R := R) (S := S)).m
      obj deg x r s hs hr = 0 := by
  by_cases hs2 : s = 2
  · have hout : n + 1 - s ≠ 2 := by
      omega
    haveI : NeZero (n + 1 - s) := ⟨Nat.ne_of_gt (indexedStasheffOuterArity_pos r s hr)⟩
    exact
      indexedStasheffTerm_eq_zero_of_outer_map_eq_zero
        (Hom := fun _ _ => concentratedAt0 (R := R) (S := S))
        (m := (concentratedAt0CategoryData (R := R) (S := S)).m)
        obj deg x r s hs hr
        (concentratedAt0CategoryData_m_ne_two
          (R := R) (S := S)
          (obj := stasheffObjOut obj r s hr)
          (deg := stasheffDegOut deg r s hr)
          hout)
  · exact
      letI : NeZero s := ⟨by omega⟩
      indexedStasheffTerm_eq_zero_of_inner_map_eq_zero
        (Hom := fun _ _ => concentratedAt0 (R := R) (S := S))
        (m := (concentratedAt0CategoryData (R := R) (S := S)).m)
        obj deg x r s hs hr
        (concentratedAt0CategoryData_m_ne_two
          (R := R) (S := S)
          (obj := stasheffObjIn obj r s hr)
          (deg := stasheffDegIn deg r s hr)
          hs2)

lemma concentratedAt0CategoryData_stasheffTerm_eq_zero_of_s_ne_two
    (R : Type u) [CommRing R]
    (S : Type u) [CommRing S] [Algebra R S]
    (obj : Fin 4 → OneObj S)
    (deg : Fin 3 → ℤ)
    (x : ∀ i : Fin 3,
      ComposableHomType
        (fun _ _ => concentratedAt0 (R := R) (S := S))
        obj deg i)
    (r s : ℕ)
    (hs : 1 ≤ s)
    (hr : r + s ≤ 3)
    (hs2 : s ≠ 2) :
    indexedStasheffTerm
      (fun _ _ => concentratedAt0 (R := R) (S := S))
      (concentratedAt0CategoryData (R := R) (S := S)).m
      obj deg x r s hs hr = 0 := by
  letI : NeZero s := ⟨by omega⟩
  exact
    indexedStasheffTerm_eq_zero_of_inner_map_eq_zero
      (Hom := fun _ _ => concentratedAt0 (R := R) (S := S))
      (m := (concentratedAt0CategoryData (R := R) (S := S)).m)
      obj deg x r s hs hr
      (concentratedAt0CategoryData_m_ne_two
        (R := R) (S := S)
        (obj := stasheffObjIn obj r s hr)
        (deg := stasheffDegIn deg r s hr)
        hs2)

lemma concentratedAt0CategoryData_stasheffTerm_r0_s2_zero_degrees
    (R : Type u) [CommRing R]
    (S : Type u) [CommRing S] [Algebra R S]
    (obj : Fin 4 → OneObj S)
    (x : Fin 3 → ModuleCat.of R S) :
    indexedStasheffTerm
      (fun _ _ => concentratedAt0 (R := R) (S := S))
      (concentratedAt0CategoryData (R := R) (S := S)).m
      obj (fun _ : Fin 3 => 0)
      (fun i => by
        simpa [ComposableHomType, concentratedAt0] using x i)
      0 2 (by omega) (by omega) =
      (x 0 * x 1) * x 2 := by
  let x' : ∀ i : Fin 3,
      ComposableHomType
        (fun _ _ => concentratedAt0 (R := R) (S := S))
        obj (fun _ : Fin 3 => 0) i :=
    fun i => by
      simpa [ComposableHomType, concentratedAt0] using x i
  have hinner :
      indexedStasheffInner
        (fun _ _ => concentratedAt0 (R := R) (S := S))
        (concentratedAt0CategoryData (R := R) (S := S)).m
        obj (fun _ : Fin 3 => 0) x' 0 2 (by omega) (by omega) =
      x 0 * x 1 := by
    simpa [indexedStasheffInner, indexedStasheffXIn_apply, x', concentratedAt0] using
      (concentratedAt0CategoryData_m_two_zero_zero_apply
        (R := R) (S := S)
        (obj := stasheffObjIn obj 0 2 (by omega))
        (x := fun i : Fin 2 => x ⟨i.1, by omega⟩))
  have hdegOut :
      stasheffDegOut (fun _ : Fin 3 => 0) 0 2 (by omega) = (fun _ : Fin 2 => (0 : ℤ)) := by
    have hdegIn :
        stasheffDegIn (fun _ : Fin 3 => 0) 0 2 (by omega) = (fun _ : Fin 2 => (0 : ℤ)) := by
      ext i
      fin_cases i <;> rfl
    have hinnerDeg : stasheffInnerDeg (fun _ : Fin 3 => 0) 0 2 (by omega) = (0 : ℤ) := by
      rw [stasheffInnerDeg, hdegIn]
      simp [operationTargetDeg, shift_ofInt]
    ext i
    fin_cases i <;> simp [stasheffDegOut, hinnerDeg]
  let z : ∀ i : Fin 2, ModuleCat.of R S :=
    fun i => by
      simpa [ComposableHomType, concentratedAt0, hdegOut] using
        indexedStasheffXOut
          (fun _ _ => concentratedAt0 (R := R) (S := S))
          (concentratedAt0CategoryData (R := R) (S := S)).m
          obj (fun _ : Fin 3 => 0) x' 0 2 (by omega) (by omega) i
  have hz0 : z 0 = x 0 * x 1 := by
    simpa [z, hdegOut, concentratedAt0, hinner, indexedStasheffMiddleIndex] using
      (indexedStasheffXOut_middle_eq
        (Hom := fun _ _ => concentratedAt0 (R := R) (S := S))
        (m := (concentratedAt0CategoryData (R := R) (S := S)).m)
        (obj := obj) (deg := fun _ : Fin 3 => 0) (x := x')
        (r := 0) (s := 2) (hs := by omega) (hr := by omega))
  have hz1 : z 1 = x 2 := by
    simpa [z, hdegOut, concentratedAt0] using
      (indexedStasheffXOut_apply_of_gt
        (Hom := fun _ _ => concentratedAt0 (R := R) (S := S))
        (m := (concentratedAt0CategoryData (R := R) (S := S)).m)
        (obj := obj) (deg := fun _ : Fin 3 => 0) (x := x')
        (r := 0) (s := 2) (hs := by omega) (hr := by omega)
        (i := 1) (by decide))
  have hmcast :
      (concentratedAt0CategoryData (R := R) (S := S)).m
        (stasheffObjOut obj 0 2 (by omega))
        (fun _ : Fin 2 => 0)
        z =
      (concentratedAt0CategoryData (R := R) (S := S)).m
        (stasheffObjOut obj 0 2 (by omega))
        (stasheffDegOut (fun _ : Fin 3 => 0) 0 2 (by omega))
        (indexedStasheffXOut
          (fun _ _ => concentratedAt0 (R := R) (S := S))
          (concentratedAt0CategoryData (R := R) (S := S)).m
          obj (fun _ : Fin 3 => 0) x' 0 2 (by omega) (by omega)) := by
    simpa [z, hdegOut, concentratedAt0] using
      (multilinearFamily_eq_of_deg_eq
        (Hom := fun _ _ => concentratedAt0 (R := R) (S := S))
        (m := (concentratedAt0CategoryData (R := R) (S := S)).m)
        (obj := stasheffObjOut obj 0 2 (by omega))
        hdegOut
        (indexedStasheffXOut
          (fun _ _ => concentratedAt0 (R := R) (S := S))
          (concentratedAt0CategoryData (R := R) (S := S)).m
          obj (fun _ : Fin 3 => 0) x' 0 2 (by omega) (by omega)))
  have houter0 :
      indexedStasheffOuter
        (fun _ _ => concentratedAt0 (R := R) (S := S))
        (concentratedAt0CategoryData (R := R) (S := S)).m
        obj (fun _ : Fin 3 => 0) x' 0 2 (by omega) (by omega)
        =
      (concentratedAt0CategoryData (R := R) (S := S)).m
        (stasheffObjOut obj 0 2 (by omega))
        (fun _ : Fin 2 => 0)
        z := by
    simpa [indexedStasheffOuter] using hmcast.symm
  have hz :
      (concentratedAt0CategoryData (R := R) (S := S)).m
        (stasheffObjOut obj 0 2 (by omega))
        (fun _ : Fin 2 => 0)
        z =
      z 0 * z 1 := by
    simpa using
      (concentratedAt0CategoryData_m_two_zero_zero_apply
        (R := R) (S := S)
        (obj := stasheffObjOut obj 0 2 (by omega))
        (x := z))
  have houter :
      indexedStasheffOuter
        (fun _ _ => concentratedAt0 (R := R) (S := S))
        (concentratedAt0CategoryData (R := R) (S := S)).m
        obj (fun _ : Fin 3 => 0) x' 0 2 (by omega) (by omega) =
      (x 0 * x 1) * x 2 := by
    exact houter0.trans <| hz.trans <| by rw [hz0, hz1]
  rw [indexedStasheffTerm, houter]
  cases indexedStasheffTargetModuleEq
    (Hom := fun _ _ => concentratedAt0 (R := R) (S := S))
    (obj := obj) (deg := fun _ : Fin 3 => 0) (r := 0) (s := 2) (hr := by omega)
  rfl

lemma concentratedAt0CategoryData_stasheffTerm_r1_s2_zero_degrees
    (R : Type u) [CommRing R]
    (S : Type u) [CommRing S] [Algebra R S]
    (obj : Fin 4 → OneObj S)
    (x : Fin 3 → ModuleCat.of R S) :
    indexedStasheffTerm
      (fun _ _ => concentratedAt0 (R := R) (S := S))
      (concentratedAt0CategoryData (R := R) (S := S)).m
      obj (fun _ : Fin 3 => 0)
      (fun i => by
        simpa [ComposableHomType, concentratedAt0] using x i)
      1 2 (by omega) (by omega) =
      x 0 * (x 1 * x 2) := by
  let x' : ∀ i : Fin 3,
      ComposableHomType
        (fun _ _ => concentratedAt0 (R := R) (S := S))
        obj (fun _ : Fin 3 => 0) i :=
    fun i => by
      simpa [ComposableHomType, concentratedAt0] using x i
  have hinner :
      indexedStasheffInner
        (fun _ _ => concentratedAt0 (R := R) (S := S))
        (concentratedAt0CategoryData (R := R) (S := S)).m
        obj (fun _ : Fin 3 => 0) x' 1 2 (by omega) (by omega) =
      x 1 * x 2 := by
    simpa [indexedStasheffInner, indexedStasheffXIn_apply, x', concentratedAt0] using
      (concentratedAt0CategoryData_m_two_zero_zero_apply
        (R := R) (S := S)
        (obj := stasheffObjIn obj 1 2 (by omega))
        (x := fun i : Fin 2 => x ⟨1 + i.1, by omega⟩))
  have hdegOut :
      stasheffDegOut (fun _ : Fin 3 => 0) 1 2 (by omega) = (fun _ : Fin 2 => (0 : ℤ)) := by
    have hdegIn : stasheffDegIn (fun _ : Fin 3 => 0) 1 2 (by omega) = (fun _ : Fin 2 => (0 : ℤ)) := by
      ext i
      fin_cases i <;> rfl
    have hinnerDeg : stasheffInnerDeg (fun _ : Fin 3 => 0) 1 2 (by omega) = (0 : ℤ) := by
      rw [stasheffInnerDeg, hdegIn]
      simp [operationTargetDeg, shift_ofInt]
    ext i
    fin_cases i <;> simp [stasheffDegOut, hinnerDeg]
  let z : ∀ i : Fin 2, ModuleCat.of R S :=
    fun i => by
      simpa [ComposableHomType, concentratedAt0, hdegOut] using
        indexedStasheffXOut
          (fun _ _ => concentratedAt0 (R := R) (S := S))
          (concentratedAt0CategoryData (R := R) (S := S)).m
          obj (fun _ : Fin 3 => 0) x' 1 2 (by omega) (by omega) i
  have hz0 : z 0 = x 0 := by
    simpa [z, hdegOut, concentratedAt0] using
      (indexedStasheffXOut_apply_of_lt
        (Hom := fun _ _ => concentratedAt0 (R := R) (S := S))
        (m := (concentratedAt0CategoryData (R := R) (S := S)).m)
        (obj := obj) (deg := fun _ : Fin 3 => 0) (x := x')
        (r := 1) (s := 2) (hs := by omega) (hr := by omega)
        (i := 0) (by decide))
  have hz1 : z 1 = x 1 * x 2 := by
    simpa [z, hdegOut, concentratedAt0, hinner, indexedStasheffMiddleIndex] using
      (indexedStasheffXOut_middle_eq
        (Hom := fun _ _ => concentratedAt0 (R := R) (S := S))
        (m := (concentratedAt0CategoryData (R := R) (S := S)).m)
        (obj := obj) (deg := fun _ : Fin 3 => 0) (x := x')
        (r := 1) (s := 2) (hs := by omega) (hr := by omega))
  have hmcast :
      (concentratedAt0CategoryData (R := R) (S := S)).m
        (stasheffObjOut obj 1 2 (by omega))
        (fun _ : Fin 2 => 0)
        z =
      (concentratedAt0CategoryData (R := R) (S := S)).m
        (stasheffObjOut obj 1 2 (by omega))
        (stasheffDegOut (fun _ : Fin 3 => 0) 1 2 (by omega))
        (indexedStasheffXOut
          (fun _ _ => concentratedAt0 (R := R) (S := S))
          (concentratedAt0CategoryData (R := R) (S := S)).m
          obj (fun _ : Fin 3 => 0) x' 1 2 (by omega) (by omega)) := by
    simpa [z, hdegOut, concentratedAt0] using
      (multilinearFamily_eq_of_deg_eq
        (Hom := fun _ _ => concentratedAt0 (R := R) (S := S))
        (m := (concentratedAt0CategoryData (R := R) (S := S)).m)
        (obj := stasheffObjOut obj 1 2 (by omega))
        hdegOut
        (indexedStasheffXOut
          (fun _ _ => concentratedAt0 (R := R) (S := S))
          (concentratedAt0CategoryData (R := R) (S := S)).m
          obj (fun _ : Fin 3 => 0) x' 1 2 (by omega) (by omega)))
  have houter0 :
      indexedStasheffOuter
        (fun _ _ => concentratedAt0 (R := R) (S := S))
        (concentratedAt0CategoryData (R := R) (S := S)).m
        obj (fun _ : Fin 3 => 0) x' 1 2 (by omega) (by omega)
        =
      (concentratedAt0CategoryData (R := R) (S := S)).m
        (stasheffObjOut obj 1 2 (by omega))
        (fun _ : Fin 2 => 0)
        z := by
    simpa [indexedStasheffOuter] using hmcast.symm
  have hz :
      (concentratedAt0CategoryData (R := R) (S := S)).m
        (stasheffObjOut obj 1 2 (by omega))
        (fun _ : Fin 2 => 0)
        z =
      z 0 * z 1 := by
    simpa using
      (concentratedAt0CategoryData_m_two_zero_zero_apply
        (R := R) (S := S)
        (obj := stasheffObjOut obj 1 2 (by omega))
        (x := z))
  have houter :
      indexedStasheffOuter
        (fun _ _ => concentratedAt0 (R := R) (S := S))
        (concentratedAt0CategoryData (R := R) (S := S)).m
        obj (fun _ : Fin 3 => 0) x' 1 2 (by omega) (by omega) =
      x 0 * (x 1 * x 2) := by
    exact houter0.trans <| hz.trans <| by rw [hz0, hz1]
  rw [indexedStasheffTerm, houter]
  cases indexedStasheffTargetModuleEq
    (Hom := fun _ _ => concentratedAt0 (R := R) (S := S))
    (obj := obj) (deg := fun _ : Fin 3 => 0) (r := 1) (s := 2) (hr := by omega)
  rfl

lemma concentratedAt0CategoryData_stasheffTerm_r0_s2_eq_zero_of_not_all_zero
    (R : Type u) [CommRing R]
    (S : Type u) [CommRing S] [Algebra R S]
    (obj : Fin 4 → OneObj S)
    (deg : Fin 3 → ℤ)
    (x : ∀ i : Fin 3,
      ComposableHomType
        (fun _ _ => concentratedAt0 (R := R) (S := S))
        obj deg i)
    (hdeg : deg ≠ fun _ : Fin 3 => (0 : ℤ)) :
    indexedStasheffTerm
      (fun _ _ => concentratedAt0 (R := R) (S := S))
      (concentratedAt0CategoryData (R := R) (S := S)).m
      obj deg x 0 2 (by omega) (by omega) = 0 := by
  by_cases h0 : deg 0 = 0
  · by_cases h1 : deg 1 = 0
    · have h2 : deg 2 ≠ 0 := by
        intro h2
        apply hdeg
        ext i
        fin_cases i <;> simp [h0, h1, h2]
      have hdegIn : stasheffDegIn deg 0 2 (by omega) = (fun _ : Fin 2 => (0 : ℤ)) := by
        ext i
        fin_cases i <;> simp [stasheffDegIn, h0, h1]
      have hinnerDeg : stasheffInnerDeg deg 0 2 (by omega) = (0 : ℤ) := by
        rw [stasheffInnerDeg, hdegIn]
        simp [operationTargetDeg, shift_ofInt]
      exact
        indexedStasheffTerm_eq_zero_of_outer_map_eq_zero
          (Hom := fun _ _ => concentratedAt0 (R := R) (S := S))
          (m := (concentratedAt0CategoryData (R := R) (S := S)).m)
          obj deg x 0 2 (by omega) (by omega)
          (concentratedAt0CategoryData_m_two_right_ne_zero
            (R := R) (S := S)
            (obj := stasheffObjOut obj 0 2 (by omega))
            (deg := stasheffDegOut deg 0 2 (by omega))
            (h0 := by simp [stasheffDegOut, hinnerDeg])
            (h1 := by simpa [stasheffDegOut, hinnerDeg] using h2))
    · exact
        indexedStasheffTerm_eq_zero_of_inner_map_eq_zero
          (Hom := fun _ _ => concentratedAt0 (R := R) (S := S))
          (m := (concentratedAt0CategoryData (R := R) (S := S)).m)
          obj deg x 0 2 (by omega) (by omega)
          (concentratedAt0CategoryData_m_two_right_ne_zero
            (R := R) (S := S)
            (obj := stasheffObjIn obj 0 2 (by omega))
            (deg := stasheffDegIn deg 0 2 (by omega))
            (h0 := by simpa [stasheffDegIn] using h0)
            (h1 := by simpa [stasheffDegIn] using h1))
  · exact
      indexedStasheffTerm_eq_zero_of_inner_map_eq_zero
        (Hom := fun _ _ => concentratedAt0 (R := R) (S := S))
        (m := (concentratedAt0CategoryData (R := R) (S := S)).m)
        obj deg x 0 2 (by omega) (by omega)
        (concentratedAt0CategoryData_m_two_left_ne_zero
          (R := R) (S := S)
          (obj := stasheffObjIn obj 0 2 (by omega))
          (deg := stasheffDegIn deg 0 2 (by omega))
          (h0 := by simpa [stasheffDegIn] using h0))

lemma concentratedAt0CategoryData_stasheffTerm_r1_s2_eq_zero_of_not_all_zero
    (R : Type u) [CommRing R]
    (S : Type u) [CommRing S] [Algebra R S]
    (obj : Fin 4 → OneObj S)
    (deg : Fin 3 → ℤ)
    (x : ∀ i : Fin 3,
      ComposableHomType
        (fun _ _ => concentratedAt0 (R := R) (S := S))
        obj deg i)
    (hdeg : deg ≠ fun _ : Fin 3 => (0 : ℤ)) :
    indexedStasheffTerm
      (fun _ _ => concentratedAt0 (R := R) (S := S))
      (concentratedAt0CategoryData (R := R) (S := S)).m
      obj deg x 1 2 (by omega) (by omega) = 0 := by
  by_cases h1 : deg 1 = 0
  · by_cases h2 : deg 2 = 0
    · have h0 : deg 0 ≠ 0 := by
        intro h0
        apply hdeg
        ext i
        fin_cases i <;> simp [h0, h1, h2]
      exact
        indexedStasheffTerm_eq_zero_of_outer_map_eq_zero
          (Hom := fun _ _ => concentratedAt0 (R := R) (S := S))
          (m := (concentratedAt0CategoryData (R := R) (S := S)).m)
          obj deg x 1 2 (by omega) (by omega)
          (concentratedAt0CategoryData_m_two_left_ne_zero
            (R := R) (S := S)
            (obj := stasheffObjOut obj 1 2 (by omega))
            (deg := stasheffDegOut deg 1 2 (by omega))
            (h0 := by simpa [stasheffDegOut] using h0))
    · exact
        indexedStasheffTerm_eq_zero_of_inner_map_eq_zero
          (Hom := fun _ _ => concentratedAt0 (R := R) (S := S))
          (m := (concentratedAt0CategoryData (R := R) (S := S)).m)
          obj deg x 1 2 (by omega) (by omega)
          (concentratedAt0CategoryData_m_two_right_ne_zero
            (R := R) (S := S)
            (obj := stasheffObjIn obj 1 2 (by omega))
            (deg := stasheffDegIn deg 1 2 (by omega))
            (h0 := by simpa [stasheffDegIn] using h1)
            (h1 := by simpa [stasheffDegIn] using h2))
  · exact
      indexedStasheffTerm_eq_zero_of_inner_map_eq_zero
        (Hom := fun _ _ => concentratedAt0 (R := R) (S := S))
        (m := (concentratedAt0CategoryData (R := R) (S := S)).m)
        obj deg x 1 2 (by omega) (by omega)
        (concentratedAt0CategoryData_m_two_left_ne_zero
          (R := R) (S := S)
          (obj := stasheffObjIn obj 1 2 (by omega))
          (deg := stasheffDegIn deg 1 2 (by omega))
          (h0 := by simpa [stasheffDegIn] using h1))

private lemma stasheffSign_zero_deg_0_2 :
    stasheffSign (fun _ : Fin 3 => (0 : ℤ)) 0 2 (by omega) = -1 := by
  norm_num [stasheffSign, stasheffSignParity]
private lemma stasheffSign_zero_deg_1_2 :
    stasheffSign (fun _ : Fin 3 => (0 : ℤ)) 1 2 (by omega) = 1 := by
  norm_num [stasheffSign, stasheffSignParity]


theorem concentratedAt0CategoryData_satisfiesStasheff
    (R : Type u) [CommRing R]
    (S : Type u) [CommRing S] [Algebra R S] :
    @AInfinityCategoryStruct.SatisfiesStasheff ℤ _ R _ (OneObj S)
      (concentratedAt0CategoryData (R := R) (S := S)) := by
  intro n _ obj deg x
  by_cases hn : n = 3
  · subst hn
    by_cases hdeg : deg = fun _ : Fin 3 => (0 : ℤ)
    · subst hdeg
      let xS : ∀ i : Fin 3, ModuleCat.of R S :=
        fun i => by
          simpa [ComposableHomType, concentratedAt0] using x i
      have hterm02 :
          indexedStasheffTerm
            (fun _ _ => concentratedAt0 (R := R) (S := S))
            (concentratedAt0CategoryData (R := R) (S := S)).m
            obj (fun _ : Fin 3 => 0) x 0 2 (by omega) (by omega) =
          (xS 0 * xS 1) * xS 2 := by
        simpa [xS] using
          concentratedAt0CategoryData_stasheffTerm_r0_s2_zero_degrees
            (R := R) (S := S) (obj := obj) (x := xS)
      have hterm12 :
          indexedStasheffTerm
            (fun _ _ => concentratedAt0 (R := R) (S := S))
            (concentratedAt0CategoryData (R := R) (S := S)).m
            obj (fun _ : Fin 3 => 0) x 1 2 (by omega) (by omega) =
          xS 0 * (xS 1 * xS 2) := by
        simpa [xS] using
          concentratedAt0CategoryData_stasheffTerm_r1_s2_zero_degrees
            (R := R) (S := S) (obj := obj) (x := xS)
      have hassoc : (xS 0 * xS 1) * xS 2 = xS 0 * (xS 1 * xS 2) := by
        rw [mul_assoc]
      -- Remaining task: reduce the finite Stasheff sum to the two valid nonzero terms
      -- `(r,s) = (0,2)` and `(1,2)`, then use their signs and `hassoc`.

      unfold indexedStasheffSum;
      rw [ Finset.sum_eq_add ( ⟨ 0, by decide ⟩ ) ( ⟨ 1, by decide ⟩ ) ];
      · rw [ Finset.sum_eq_single ⟨ 2, by decide ⟩, Finset.sum_eq_single ⟨ 2, by decide ⟩ ] <;> simp +decide [ * ];
        · erw [ hterm02, hterm12, stasheffSign_zero_deg_0_2, stasheffSign_zero_deg_1_2 ] ; simp +decide [ hassoc ];
        · intro a ha₁ ha₂ ha₃
          interval_cases a <;> simp +decide only [Fin.isValue] at ha₃ ⊢
          have hterm :
              indexedStasheffTerm
                (fun _ _ => concentratedAt0 (R := R) (S := S))
                (concentratedAt0CategoryData (R := R) (S := S)).m
                obj (fun _ : Fin 3 => 0) x 1 1 (by omega) (by omega) = 0 := by
            exact
              concentratedAt0CategoryData_stasheffTerm_eq_zero_of_s_ne_two
                (R := R) (S := S)
                (obj := obj) (deg := fun _ : Fin 3 => 0) (x := x)
                (r := 1) (s := 1) (by omega) (by omega) (by decide)
          have hsmul :
              stasheffSign (fun _ : Fin 3 => (0 : ℤ)) 1 1 (by omega) •
                indexedStasheffTerm
                  (fun _ _ => concentratedAt0 (R := R) (S := S))
                  (concentratedAt0CategoryData (R := R) (S := S)).m
                  obj (fun _ : Fin 3 => (0 : ℤ)) x 1 1 (by omega) (by omega) = 0 := by
            rw [hterm]
            simp
          simpa [GHom, concentratedAt0CategoryData, concentratedAt0Quiver] using hsmul
        · intro a ha₁ ha₂ ha₃
          interval_cases a <;> simp +decide only [Fin.isValue] at ha₃ ⊢
          · have hterm :
                indexedStasheffTerm
                  (fun _ _ => concentratedAt0 (R := R) (S := S))
                  (concentratedAt0CategoryData (R := R) (S := S)).m
                  obj (fun _ : Fin 3 => 0) x 0 1 (by omega) (by omega) = 0 := by
              exact
                concentratedAt0CategoryData_stasheffTerm_eq_zero_of_s_ne_two
                  (R := R) (S := S)
                  (obj := obj) (deg := fun _ : Fin 3 => 0) (x := x)
                  (r := 0) (s := 1) (by omega) (by omega) (by decide)
            have hsmul :
                stasheffSign (fun _ : Fin 3 => (0 : ℤ)) 0 1 (by omega) •
                  indexedStasheffTerm
                    (fun _ _ => concentratedAt0 (R := R) (S := S))
                    (concentratedAt0CategoryData (R := R) (S := S)).m
                    obj (fun _ : Fin 3 => (0 : ℤ)) x 0 1 (by omega) (by omega) = 0 := by
              rw [hterm]
              simp
            simpa [GHom, concentratedAt0CategoryData, concentratedAt0Quiver] using hsmul
          · have hterm :
                indexedStasheffTerm
                  (fun _ _ => concentratedAt0 (R := R) (S := S))
                  (concentratedAt0CategoryData (R := R) (S := S)).m
                  obj (fun _ : Fin 3 => 0) x 0 3 (by omega) (by omega) = 0 := by
              exact
                concentratedAt0CategoryData_stasheffTerm_eq_zero_of_s_ne_two
                  (R := R) (S := S)
                  (obj := obj) (deg := fun _ : Fin 3 => 0) (x := x)
                  (r := 0) (s := 3) (by omega) (by omega) (by decide)
            have hsmul :
                stasheffSign (fun _ : Fin 3 => (0 : ℤ)) 0 3 (by omega) •
                  indexedStasheffTerm
                    (fun _ _ => concentratedAt0 (R := R) (S := S))
                    (concentratedAt0CategoryData (R := R) (S := S)).m
                    obj (fun _ : Fin 3 => (0 : ℤ)) x 0 3 (by omega) (by omega) = 0 := by
              rw [hterm]
              simp
            simpa [GHom, concentratedAt0CategoryData, concentratedAt0Quiver] using hsmul
      · simp +decide;
      · intro c hc hne; fin_cases c <;> simp +decide only [Fin.isValue, Fin.reduceLast,
        Nat.reduceAdd, range_val, Nat.reduceSub] at hne hc ⊢;
        · rw [Finset.sum_eq_single ⟨ 1, by decide ⟩]
          · have hterm :
                indexedStasheffTerm
                  (fun _ _ => concentratedAt0 (R := R) (S := S))
                  (concentratedAt0CategoryData (R := R) (S := S)).m
                  obj (fun _ : Fin 3 => 0) x 2 1 (by omega) (by omega) = 0 := by
              exact
                concentratedAt0CategoryData_stasheffTerm_eq_zero_of_s_ne_two
                  (R := R) (S := S)
                  (obj := obj) (deg := fun _ : Fin 3 => 0) (x := x)
                  (r := 2) (s := 1) (by omega) (by omega) (by decide)
            have hsmul :
                stasheffSign (fun _ : Fin 3 => (0 : ℤ)) 2 1 (by omega) •
                  indexedStasheffTerm
                    (fun _ _ => concentratedAt0 (R := R) (S := S))
                    (concentratedAt0CategoryData (R := R) (S := S)).m
                    obj (fun _ : Fin 3 => (0 : ℤ)) x 2 1 (by omega) (by omega) = 0 := by
              rw [hterm]
              simp
            simpa [GHom, concentratedAt0CategoryData, concentratedAt0Quiver] using hsmul
          · intro a ha hne
            rcases a with ⟨a, ha'⟩
            have ha1 : a = 1 := by
              have hleft : 1 ≤ a := (Finset.mem_Ico.mp ha').1
              have hright : a < 2 := (Finset.mem_Ico.mp ha').2
              omega
            subst ha1
            exact (hne rfl).elim
          · intro hnotmem
            exfalso
            exact hnotmem (by simp)
        · rfl;
      · simp +decide;
      · simp +decide
    · rw [indexedStasheffSum]
      refine Finset.sum_eq_zero ?_
      intro r hr
      refine Finset.sum_eq_zero ?_
      intro s hs
      have hvalid : ValidStasheffIndices 3 (r : ℕ) (s : ℕ) :=
        validStasheffIndices_of_mem_ranges (n := 3) r.2 s.2
      by_cases hs2 : (s : ℕ) = 2
      · have hr01 : (r : ℕ) = 0 ∨ (r : ℕ) = 1 := by
          omega
        rcases hr01 with hr0 | hr1
        · have hterm :
              indexedStasheffTerm
                (fun _ _ => concentratedAt0 (R := R) (S := S))
                (concentratedAt0CategoryData (R := R) (S := S)).m
                obj deg x 0 2 (by omega) (by omega) = 0 := by
            exact
              concentratedAt0CategoryData_stasheffTerm_r0_s2_eq_zero_of_not_all_zero
                (R := R) (S := S) (obj := obj) (deg := deg) (x := x) hdeg
          have hsmul :
              stasheffSign deg 0 2 (by omega) •
                indexedStasheffTerm
                  (fun _ _ => concentratedAt0 (R := R) (S := S))
                  (concentratedAt0CategoryData (R := R) (S := S)).m
                  obj deg x 0 2 (by omega) (by omega) = 0 := by
            rw [hterm]
            simp
          simpa [hr0, hs2] using hsmul
        · have hterm :
              indexedStasheffTerm
                (fun _ _ => concentratedAt0 (R := R) (S := S))
                (concentratedAt0CategoryData (R := R) (S := S)).m
                obj deg x 1 2 (by omega) (by omega) = 0 := by
            exact
              concentratedAt0CategoryData_stasheffTerm_r1_s2_eq_zero_of_not_all_zero
                (R := R) (S := S) (obj := obj) (deg := deg) (x := x) hdeg
          have hsmul :
              stasheffSign deg 1 2 (by omega) •
                indexedStasheffTerm
                  (fun _ _ => concentratedAt0 (R := R) (S := S))
                  (concentratedAt0CategoryData (R := R) (S := S)).m
                  obj deg x 1 2 (by omega) (by omega) = 0 := by
            rw [hterm]
            simp
          simpa [hr1, hs2] using hsmul
      · have hterm :
            indexedStasheffTerm
              (fun _ _ => concentratedAt0 (R := R) (S := S))
              (concentratedAt0CategoryData (R := R) (S := S)).m
              obj deg x (r : ℕ) (s : ℕ) hvalid.1 hvalid.2 = 0 := by
          exact
            concentratedAt0CategoryData_stasheffTerm_eq_zero_of_s_ne_two
              (R := R) (S := S)
              (obj := obj) (deg := deg) (x := x)
              (r := r) (s := s) hvalid.1 hvalid.2 hs2
        have hsmul :
            stasheffSign deg (r : ℕ) (s : ℕ) hvalid.2 •
              indexedStasheffTerm
                (fun _ _ => concentratedAt0 (R := R) (S := S))
                (concentratedAt0CategoryData (R := R) (S := S)).m
                obj deg x (r : ℕ) (s : ℕ) hvalid.1 hvalid.2 = 0 := by
          rw [hterm]
          simp
        simpa [hvalid] using hsmul
  · rw [indexedStasheffSum]
    refine Finset.sum_eq_zero ?_
    intro r hr
    refine Finset.sum_eq_zero ?_
    intro s hs
    have hvalid : ValidStasheffIndices n (r : ℕ) (s : ℕ) :=
      validStasheffIndices_of_mem_ranges (n := n) r.2 s.2
    have hterm :
        indexedStasheffTerm
          (fun _ _ => concentratedAt0 (R := R) (S := S))
          (concentratedAt0CategoryData (R := R) (S := S)).m
          obj deg x (r : ℕ) (s : ℕ) hvalid.1 hvalid.2 = 0 := by
      exact
        concentratedAt0CategoryData_stasheffTerm_eq_zero_of_ne_three
          (R := R) (S := S)
          (obj := obj) (deg := deg) (x := x)
          (r := r) (s := s) hvalid.1 hvalid.2 hn
    have hsmul :
        stasheffSign deg (r : ℕ) (s : ℕ) hvalid.2 •
          indexedStasheffTerm
            (fun _ _ => concentratedAt0 (R := R) (S := S))
            (concentratedAt0CategoryData (R := R) (S := S)).m
            obj deg x (r : ℕ) (s : ℕ) hvalid.1 hvalid.2 = 0 := by
      rw [hterm]
      simp
    simpa [hvalid] using hsmul

instance concentratedAt0Category
    (R : Type u) [CommRing R]
    (S : Type u) [CommRing S] [Algebra R S] :
    AInfinityCategory (β := ℤ) R (OneObj S) where
  toAInfinityCategoryStruct := concentratedAt0CategoryData (R := R) (S := S)
  satisfiesStasheff := concentratedAt0CategoryData_satisfiesStasheff (R := R) (S := S)


end Examples
end AInfinityTheory
