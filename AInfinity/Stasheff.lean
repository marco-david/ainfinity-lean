module

public import Mathlib
public import AInfinity.Grading

@[expose] public section

open CategoryTheory Finset AInfinityTheory

noncomputable section

namespace AInfinityTheory

universe u v w
variable {β : Type v} [Grading β]
variable {n : ℕ}

/-- Target degree of the `n`-ary operation `m`. -/
abbrev operationTargetDeg
    (deg : Fin n → β) : β :=
  (∑ i, deg i) + shift_ofInt (2 - (n : ℤ))

/-- Target degree of the arity-`n` Stasheff relation. -/
abbrev stasheffTargetDeg
    (deg : Fin n → β) : β :=
  (∑ i, deg i) + shift_ofInt (3 - (n : ℤ))

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

/-- Helper: degree function for the inner portion of the Stasheff composition. -/
def stasheffDegIn
    (deg : Fin n → β)
    (r s : ℕ)
    (hr : r + s ≤ n) : Fin s → β :=
  fun i => deg ⟨r + i.val, by omega⟩

/-- Helper: inner degree (the degree of the result of the inner multilinear map). -/
def stasheffInnerDeg
    (deg : Fin n → β)
    (r s : ℕ)
    (hr : r + s ≤ n) : β :=
  operationTargetDeg (stasheffDegIn deg r s hr)

/-- Helper: the outer degree function. -/
def stasheffDegOut
    (deg : Fin n → β)
    (r s : ℕ)
    (hr : r + s ≤ n) : Fin (n + 1 - s) → β :=
  fun i =>
    if h1 : i.val < r then
      deg ⟨i.val, by omega⟩
    else if _ : i.val = r then
      stasheffInnerDeg deg r s hr
    else
      deg ⟨i.val + s - 1, by omega⟩

/-- Helper: the inner object string. -/
def stasheffObjIn
    {Obj : Type w}
    (obj : Fin (n + 1) → Obj)
    (r s : ℕ)
    (hr : r + s ≤ n) : Fin (s + 1) → Obj :=
  fun i => obj ⟨r + i.val, by omega⟩

/-- Helper: the outer object string obtained by collapsing the inner block. -/
def stasheffObjOut
    {Obj : Type w}
    (obj : Fin (n + 1) → Obj)
    (r s : ℕ)
    (hr : r + s ≤ n) : Fin ((n + 1 - s) + 1) → Obj :=
  fun i =>
    if h1 : i.val ≤ r then
      obj ⟨i.val, by omega⟩
    else
      obj ⟨i.val + s - 1, by omega⟩

private lemma shift_ofInt_combine {n s : ℕ} (hsn : s ≤ n) :
    shift_ofInt (β := β) (2 - (s : ℤ)) + shift_ofInt (2 - ((n + 1 - s : ℕ) : ℤ)) =
    shift_ofInt (3 - (n : ℤ)) := by
  have : 3 - (n : ℤ) = 2 - (s : ℤ) + 2 - ((n + 1 - s : ℕ) : ℤ) := by
    have hle : s ≤ n + 1 := Nat.le_succ_of_le hsn
    rw [Nat.cast_sub hle]
    push_cast
    omega
  rw [this]
  conv =>
    rhs
    arg 1
    rw [Int.add_sub_assoc (2 - (s : ℤ))]
  unfold shift_ofInt
  symm
  apply map_add

lemma validStasheffIndices_of_mem_ranges
    {r s : ℕ}
    (hr : r ∈ Finset.range (n + 1))
    (hs : s ∈ Finset.Ico 1 (n - r + 1)) :
    ValidStasheffIndices n r s := by
  rcases Finset.mem_range.mp hr with hr
  rcases Finset.mem_Ico.mp hs with ⟨hs₁, hs₂⟩
  refine ⟨hs₁, ?_⟩
  omega

/-- Summing the outer degrees recovers the original total degree plus the inner shift. -/
lemma stasheffDegOut_sum_core
    (deg : Fin n → β)
    (r s : ℕ)
    (hr : r + s ≤ n) :
    (∑ i : Fin (n + 1 - s), stasheffDegOut deg r s hr i) =
    (∑ i : Fin n, deg i) + shift_ofInt (2 - (s : ℤ)) := by
  unfold stasheffDegOut
  rw [
    show (Finset.univ : Finset (Fin (n + 1 - s))) =
        Finset.univ.filter (fun i : Fin (n + 1 - s) => i.val < r) ∪
          Finset.univ.filter (fun i : Fin (n + 1 - s) => i.val = r) ∪
          Finset.univ.filter (fun i : Fin (n + 1 - s) => i.val > r) from ?_,
    Finset.sum_union,
    Finset.sum_union
  ]
  · rw [
      show Finset.univ.filter (fun i : Fin (n + 1 - s) => (i : ℕ) < r) =
          Finset.image (fun i : Fin r => ⟨i, by omega⟩) Finset.univ from ?_,
      show Finset.univ.filter (fun i : Fin (n + 1 - s) => (i : ℕ) = r) =
          {⟨r, by omega⟩} from ?_,
      show Finset.univ.filter (fun i : Fin (n + 1 - s) => (i : ℕ) > r) =
          Finset.image
            (fun i : Fin (n - r - s) => ⟨r + 1 + i, by omega⟩)
            Finset.univ from ?_
    ]
    · rw [Finset.sum_image, Finset.sum_image] <;> norm_num
      · rw [
          show (Finset.univ : Finset (Fin n)) =
              Finset.image
                  (fun i : Fin r => ⟨i, by linarith [Fin.is_lt i]⟩)
                  Finset.univ ∪
                Finset.image
                  (fun i : Fin s => ⟨r + i, by linarith [Fin.is_lt i]⟩)
                  Finset.univ ∪
                Finset.image
                  (fun i : Fin (n - r - s) => ⟨r + s + i, by omega⟩)
                  Finset.univ from ?_,
          Finset.sum_union,
          Finset.sum_union
        ]
        · rw [Finset.sum_image, Finset.sum_image, Finset.sum_image] <;> norm_num
          · unfold stasheffInnerDeg
            unfold stasheffDegIn
            ring_nf
            grind
          · exact fun i j h => by simpa [Fin.ext_iff] using h
          · exact fun i j h => by simpa [Fin.ext_iff] using h
          · exact fun i j h => by simpa [Fin.ext_iff] using h
        · norm_num [Finset.disjoint_left]
          grind
        · norm_num [Finset.disjoint_right]
          grind
        · ext ⟨i, hi⟩
          simp only
            [mem_univ, union_assoc, mem_union, mem_image, Fin.mk.injEq, true_and,
              true_iff]
          by_cases hi' : i < r
          · exact Or.inl ⟨⟨i, by linarith⟩, rfl⟩
          · by_cases hi'' : i < r + s
            · exact Or.inr <| Or.inl <|
                ⟨⟨i - r, by omega⟩, by
                  simp +decide [Nat.add_sub_of_le (le_of_not_gt hi')]
                ⟩
            · exact Or.inr <| Or.inr <| ⟨⟨i - (r + s), by omega⟩, by
                norm_num
                omega
              ⟩
      · exact fun i j h => by simpa [Fin.ext_iff] using h
      · exact fun i j h => by simpa [Fin.ext_iff] using h
    · apply Finset.ext
      intro i
      simp only [gt_iff_lt, mem_filter, mem_univ, true_and, mem_image]
      exact
        ⟨
          (fun hi => ⟨⟨i - (r + 1), by omega⟩, by
            erw [Fin.ext_iff]
            norm_num
            omega
          ⟩),
          by
            rintro ⟨a, rfl⟩
            exact
              Nat.lt_of_lt_of_le
                (by simp +arith +decide)
                (Nat.le_add_right _ _)
        ⟩
    · ext ⟨i, hi⟩
      aesop
    · ext ⟨i, hi⟩
      simp only [mem_filter, mem_univ, true_and, mem_image, Fin.mk.injEq]
      exact
        ⟨
          (fun hi' => ⟨⟨i, by omega⟩, rfl⟩),
          fun ⟨a, ha⟩ => by linarith [Fin.is_lt a]
        ⟩
  · exact Finset.disjoint_filter.mpr fun _ _ _ _ => by linarith
  · simp +contextual [Finset.disjoint_left]
    exact fun a ha => ha.elim (fun ha => le_of_lt ha) fun ha => ha.le
  · ext i
    cases lt_trichotomy i.val r <;> aesop

/-- The outer operation has the Stasheff target degree. -/
lemma stasheffDegOut_sum
    (deg : Fin n → β)
    (r s : ℕ)
    (hr : r + s ≤ n) :
    (∑ i : Fin (n + 1 - s), stasheffDegOut deg r s hr i) +
      shift_ofInt (2 - ((n + 1 - s : ℕ) : ℤ)) =
    stasheffTargetDeg deg := by
  rw [stasheffDegOut_sum_core deg r s hr, add_assoc,
      shift_ofInt_combine (by omega : s ≤ n)]

/-- Transporting zero across an equality of `ModuleCat` objects still gives zero. -/
lemma cast_zero_of_module_eq
    {R : Type u}
    [CommRing R]
    {M N : ModuleCat R}
    (h : M = N) :
    cast (congrArg (fun X : ModuleCat R => (X : Type u)) h) (0 : M) = (0 : N) := by
  cases h
  rfl

/-- A transported element of a `ModuleCat` is zero iff the original element was zero. -/
lemma cast_eq_zero_iff_of_module_eq
    {R : Type u}
    [CommRing R]
    {M N : ModuleCat R}
    (h : M = N)
    (x : M) :
    cast (congrArg (fun X : ModuleCat R => (X : Type u)) h) x = (0 : N) ↔ x = 0 := by
  constructor
  · intro hx
    have hcast :
        cast (congrArg (fun X : ModuleCat R => (X : Type u)) h) x =
          cast (congrArg (fun X : ModuleCat R => (X : Type u)) h) (0 : M) := by
      simpa [cast_zero_of_module_eq h] using hx
    exact (cast_inj (congrArg (fun X : ModuleCat R => (X : Type u)) h)).1 hcast
  · intro hx
    simpa [hx] using cast_zero_of_module_eq h

/-- Rewriting the degree function and transporting each input does not change the value of `m`. -/
lemma multilinearFamily_eq_of_deg_eq
    {R : Type u}
    [CommRing R]
    {Obj : Type w}
    (Hom : Obj → Obj → GradedRModule (β := β) (R := R))
    (m : {n : ℕ} → [NeZero n] →
      (obj : Fin (n + 1) → Obj) → (deg : Fin n → β) →
      MultilinearMap R
        (fun i : Fin n => ComposableHomType Hom obj deg i)
        (operationTargetType Hom obj deg))
    {n : ℕ}
    [NeZero n]
    (obj : Fin (n + 1) → Obj)
    {deg deg' : Fin n → β}
    (hdeg : deg = deg')
    (x : ∀ i : Fin n, ComposableHomType Hom obj deg i) :
    m obj deg'
      (fun i =>
        cast
          (congrArg
            (fun d => ((ComposableHomType Hom obj d i : ModuleCat R) : Type u))
            hdeg)
          (x i)) =
      cast
        (congrArg
          (fun d => ((operationTargetType Hom obj d : ModuleCat R) : Type u))
          hdeg)
        (m obj deg x) := by
  cases hdeg
  rfl

/-- Helper: the input tuple for the inner operation in a Stasheff term. -/
def indexedStasheffXIn
    {R : Type u}
    [CommRing R]
    {Obj : Type w}
    (Hom : Obj → Obj → GradedRModule (β := β) (R := R))
    {n : ℕ}
    (obj : Fin (n + 1) → Obj)
    (deg : Fin n → β)
    (x : ∀ i : Fin n, ComposableHomType Hom obj deg i)
    (r s : ℕ)
    (hr : r + s ≤ n) :
    ∀ i : Fin s, ComposableHomType Hom (stasheffObjIn obj r s hr) (stasheffDegIn deg r s hr) i :=
  fun i => x ⟨r + i.val, by omega⟩

omit [Grading β] in
/-- Evaluating the inner input tuple just picks out the corresponding original input. -/
lemma indexedStasheffXIn_apply
    {R : Type u}
    [CommRing R]
    {Obj : Type w}
    (Hom : Obj → Obj → GradedRModule (β := β) (R := R))
    {n : ℕ}
    (obj : Fin (n + 1) → Obj)
    (deg : Fin n → β)
    (x : ∀ i : Fin n, ComposableHomType Hom obj deg i)
    (r s : ℕ)
    (hr : r + s ≤ n)
    (i : Fin s) :
    indexedStasheffXIn Hom obj deg x r s hr i = x ⟨r + i.val, by omega⟩ := by
  simp [indexedStasheffXIn, ComposableHomType, stasheffObjIn, stasheffDegIn]

/-- Helper: the inner value appearing in a Stasheff term. -/
def indexedStasheffInner
    {R : Type u}
    [CommRing R]
    {Obj : Type w}
    (Hom : Obj → Obj → GradedRModule (β := β) (R := R))
    (m : {n : ℕ} → [NeZero n] →
      (obj : Fin (n + 1) → Obj) → (deg : Fin n → β) →
      MultilinearMap R
        (fun i : Fin n => ComposableHomType Hom obj deg i)
        (operationTargetType Hom obj deg))
    {n : ℕ}
    (obj : Fin (n + 1) → Obj)
    (deg : Fin n → β)
    (x : ∀ i : Fin n, ComposableHomType Hom obj deg i)
    (r s : ℕ)
    (hs : 1 ≤ s)
    (hr : r + s ≤ n) :
    operationTargetType Hom (stasheffObjIn obj r s hr) (stasheffDegIn deg r s hr) := by
  letI : NeZero s := ⟨by omega⟩
  exact m (stasheffObjIn obj r s hr) (stasheffDegIn deg r s hr)
    (indexedStasheffXIn Hom obj deg x r s hr)

/-- Helper: the middle index in the outer tuple of a Stasheff term. -/
def indexedStasheffMiddleIndex
    {n : ℕ}
    (r s : ℕ)
    (hr : r + s ≤ n) : Fin (n + 1 - s) :=
  ⟨r, by omega⟩

/-- Helper: the `ModuleCat` equality identifying the middle outer input with the inner output. -/
lemma indexedStasheffMiddleModuleEq
    {R : Type u}
    [CommRing R]
    {Obj : Type w}
    (Hom : Obj → Obj → GradedRModule (β := β) (R := R))
    {n : ℕ}
    (obj : Fin (n + 1) → Obj)
    (deg : Fin n → β)
    (r s : ℕ)
    (hr : r + s ≤ n) :
    operationTargetType Hom (stasheffObjIn obj r s hr) (stasheffDegIn deg r s hr) =
      ComposableHomType Hom (stasheffObjOut obj r s hr) (stasheffDegOut deg r s hr)
        (indexedStasheffMiddleIndex r s hr) := by
  simp [ComposableHomType, operationTargetType, indexedStasheffMiddleIndex,
    stasheffObjIn, stasheffObjOut, stasheffDegOut, stasheffInnerDeg]

/-- Helper: the type equality identifying the middle outer input with the inner output. -/
lemma indexedStasheffMiddleTypeEq
    {R : Type u}
    [CommRing R]
    {Obj : Type w}
    (Hom : Obj → Obj → GradedRModule (β := β) (R := R))
    {n : ℕ}
    (obj : Fin (n + 1) → Obj)
    (deg : Fin n → β)
    (r s : ℕ)
    (hr : r + s ≤ n) :
    ((operationTargetType Hom (stasheffObjIn obj r s hr) (stasheffDegIn deg r s hr) : ModuleCat R) : Type u) =
      ((ComposableHomType Hom (stasheffObjOut obj r s hr) (stasheffDegOut deg r s hr)
        (indexedStasheffMiddleIndex r s hr) : ModuleCat R) : Type u) := by
  exact congrArg (fun M : ModuleCat R => (M : Type u))
    (indexedStasheffMiddleModuleEq Hom obj deg r s hr)

/-- Helper: the input tuple for the outer operation in a Stasheff term. -/
def indexedStasheffXOut
    {R : Type u}
    [CommRing R]
    {Obj : Type w}
    (Hom : Obj → Obj → GradedRModule (β := β) (R := R))
    (m : {n : ℕ} → [NeZero n] →
      (obj : Fin (n + 1) → Obj) → (deg : Fin n → β) →
      MultilinearMap R
        (fun i : Fin n => ComposableHomType Hom obj deg i)
        (operationTargetType Hom obj deg))
    {n : ℕ}
    (obj : Fin (n + 1) → Obj)
    (deg : Fin n → β)
    (x : ∀ i : Fin n, ComposableHomType Hom obj deg i)
    (r s : ℕ)
    (hs : 1 ≤ s)
    (hr : r + s ≤ n) :
    ∀ i : Fin (n + 1 - s),
      ComposableHomType Hom (stasheffObjOut obj r s hr) (stasheffDegOut deg r s hr) i := by
  intro i
  by_cases hlt : i.val < r
  · simpa [ComposableHomType, stasheffObjOut, stasheffDegOut, hlt, Nat.le_of_lt hlt]
      using x ⟨i.val, by omega⟩
  · by_cases heq : i.val = r
    · have hi : i = indexedStasheffMiddleIndex r s hr := by
        apply Fin.ext
        simp [indexedStasheffMiddleIndex, heq]
      subst hi
      exact
        cast (indexedStasheffMiddleTypeEq Hom obj deg r s hr)
          (indexedStasheffInner Hom m obj deg x r s hs hr)
    · have hgt : ¬ i.val ≤ r := by omega
      have hsucc : i.val + s - 1 + 1 = i.val + s := by omega
      simpa [ComposableHomType, stasheffObjOut, stasheffDegOut, hlt, heq, hgt, hsucc]
        using x ⟨i.val + s - 1, by omega⟩

/-- Before the inserted block, the outer input tuple agrees with the original inputs. -/
lemma indexedStasheffXOut_apply_of_lt
    {R : Type u}
    [CommRing R]
    {Obj : Type w}
    (Hom : Obj → Obj → GradedRModule (β := β) (R := R))
    (m : {n : ℕ} → [NeZero n] →
      (obj : Fin (n + 1) → Obj) → (deg : Fin n → β) →
      MultilinearMap R
        (fun i : Fin n => ComposableHomType Hom obj deg i)
        (operationTargetType Hom obj deg))
    {n : ℕ}
    (obj : Fin (n + 1) → Obj)
    (deg : Fin n → β)
    (x : ∀ i : Fin n, ComposableHomType Hom obj deg i)
    (r s : ℕ)
    (hs : 1 ≤ s)
    (hr : r + s ≤ n)
    (i : Fin (n + 1 - s))
    (hlt : i.val < r) :
    indexedStasheffXOut Hom m obj deg x r s hs hr i =
      (by
        simpa [ComposableHomType, stasheffObjOut, stasheffDegOut, hlt, Nat.le_of_lt hlt]
          using x ⟨i.val, by omega⟩) := by
  unfold indexedStasheffXOut
  simp [ComposableHomType, stasheffObjOut, stasheffDegOut, hlt, Nat.le_of_lt hlt]

/-- After the inserted block, the outer input tuple agrees with the shifted original inputs. -/
lemma indexedStasheffXOut_apply_of_gt
    {R : Type u}
    [CommRing R]
    {Obj : Type w}
    (Hom : Obj → Obj → GradedRModule (β := β) (R := R))
    (m : {n : ℕ} → [NeZero n] →
      (obj : Fin (n + 1) → Obj) → (deg : Fin n → β) →
      MultilinearMap R
        (fun i : Fin n => ComposableHomType Hom obj deg i)
        (operationTargetType Hom obj deg))
    {n : ℕ}
    (obj : Fin (n + 1) → Obj)
    (deg : Fin n → β)
    (x : ∀ i : Fin n, ComposableHomType Hom obj deg i)
    (r s : ℕ)
    (hs : 1 ≤ s)
    (hr : r + s ≤ n)
    (i : Fin (n + 1 - s))
    (hgt : r < i.val) :
    indexedStasheffXOut Hom m obj deg x r s hs hr i =
      (by
        have hlt : ¬ i.val < r := by omega
        have heq : i.val ≠ r := by omega
        have hle : ¬ i.val ≤ r := by omega
        have hsucc : i.val + s - 1 + 1 = i.val + s := by omega
        simpa [ComposableHomType, stasheffObjOut, stasheffDegOut, hlt, heq, hle, hsucc]
          using x ⟨i.val + s - 1, by omega⟩) := by
  unfold indexedStasheffXOut
  have hlt : ¬ i.val < r := by omega
  have heq : i.val ≠ r := by omega
  have hle : ¬ i.val ≤ r := by omega
  simp [ComposableHomType, stasheffObjOut, stasheffDegOut, hlt, heq, hle]

/-- Helper: positivity of the outer arity in a Stasheff term. -/
lemma indexedStasheffOuterArity_pos
    {n : ℕ}
    (r s : ℕ)
    (hr : r + s ≤ n) :
    0 < n + 1 - s := by
  omega

/-- Helper: the outer value before transporting to the final Stasheff target. -/
def indexedStasheffOuter
    {R : Type u}
    [CommRing R]
    {Obj : Type w}
    (Hom : Obj → Obj → GradedRModule (β := β) (R := R))
    (m : {n : ℕ} → [NeZero n] →
      (obj : Fin (n + 1) → Obj) → (deg : Fin n → β) →
      MultilinearMap R
        (fun i : Fin n => ComposableHomType Hom obj deg i)
        (operationTargetType Hom obj deg))
    {n : ℕ}
    (obj : Fin (n + 1) → Obj)
    (deg : Fin n → β)
    (x : ∀ i : Fin n, ComposableHomType Hom obj deg i)
    (r s : ℕ)
    (hs : 1 ≤ s)
    (hr : r + s ≤ n) :
    operationTargetType Hom (stasheffObjOut obj r s hr) (stasheffDegOut deg r s hr) := by
  letI : NeZero (n + 1 - s) := ⟨Nat.ne_of_gt (indexedStasheffOuterArity_pos r s hr)⟩
  exact m (stasheffObjOut obj r s hr) (stasheffDegOut deg r s hr)
    (indexedStasheffXOut Hom m obj deg x r s hs hr)

/-- Helper: the `ModuleCat` equality from the outer target to the final Stasheff target. -/
lemma indexedStasheffTargetModuleEq
    {R : Type u}
    [CommRing R]
    {Obj : Type w}
    (Hom : Obj → Obj → GradedRModule (β := β) (R := R))
    {n : ℕ}
    (obj : Fin (n + 1) → Obj)
    (deg : Fin n → β)
    (r s : ℕ)
    (hr : r + s ≤ n) :
    operationTargetType Hom (stasheffObjOut obj r s hr) (stasheffDegOut deg r s hr) =
      Hom (obj 0) (obj (Fin.last n)) (stasheffTargetDeg deg) := by
  have hsource : stasheffObjOut obj r s hr 0 = obj 0 := by
    simp [stasheffObjOut]
  have houterN_pos : 0 < n + 1 - s := by
    omega
  have hlast_gt : ¬ (n + 1 - s) ≤ r := by
    omega
  have htarget :
      stasheffObjOut obj r s hr (Fin.last (n + 1 - s)) = obj (Fin.last n) := by
    simp [stasheffObjOut, Fin.last, hlast_gt]
    congr
    omega
  calc
    operationTargetType Hom (stasheffObjOut obj r s hr) (stasheffDegOut deg r s hr)
        = Hom ((stasheffObjOut obj r s hr) 0)
            ((stasheffObjOut obj r s hr) (Fin.last (n + 1 - s)))
            (operationTargetDeg (stasheffDegOut deg r s hr)) := rfl
    _ = Hom (obj 0) ((stasheffObjOut obj r s hr) (Fin.last (n + 1 - s)))
          (operationTargetDeg (stasheffDegOut deg r s hr)) := by rw [hsource]
    _ = Hom (obj 0) (obj (Fin.last n))
          (operationTargetDeg (stasheffDegOut deg r s hr)) := by rw [htarget]
    _ = Hom (obj 0) (obj (Fin.last n)) (stasheffTargetDeg deg) := by
      exact congrArg (fun d => Hom (obj 0) (obj (Fin.last n)) d) (stasheffDegOut_sum deg r s hr)

/-- Helper: transport from the outer target type to the final Stasheff target type. -/
lemma indexedStasheffTargetEq
    {R : Type u}
    [CommRing R]
    {Obj : Type w}
    (Hom : Obj → Obj → GradedRModule (β := β) (R := R))
    {n : ℕ}
    (obj : Fin (n + 1) → Obj)
    (deg : Fin n → β)
    (r s : ℕ)
    (hr : r + s ≤ n) :
    ((operationTargetType Hom (stasheffObjOut obj r s hr) (stasheffDegOut deg r s hr) : ModuleCat R) : Type u) =
      ((Hom (obj 0) (obj (Fin.last n)) (stasheffTargetDeg deg) : ModuleCat R) : Type u) := by
  exact congrArg (fun M : ModuleCat R => (M : Type u))
    (indexedStasheffTargetModuleEq Hom obj deg r s hr)

/-- A generic Stasheff term builder for object-indexed A∞ operations. -/
def indexedStasheffTerm
    {R : Type u}
    [CommRing R]
    {Obj : Type w}
    (Hom : Obj → Obj → GradedRModule (β := β) (R := R))
    (m : {n : ℕ} → [NeZero n] →
      (obj : Fin (n + 1) → Obj) → (deg : Fin n → β) →
      MultilinearMap R
        (fun i : Fin n => ComposableHomType Hom obj deg i)
        (operationTargetType Hom obj deg))
    {n : ℕ}
    (obj : Fin (n + 1) → Obj)
    (deg : Fin n → β)
    (x : ∀ i : Fin n, ComposableHomType Hom obj deg i)
    (r s : ℕ)
    (hs : 1 ≤ s)
    (hr : r + s ≤ n) :
    Hom (obj 0) (obj (Fin.last n)) (stasheffTargetDeg deg) :=
  cast (indexedStasheffTargetEq Hom obj deg r s hr)
    (indexedStasheffOuter Hom m obj deg x r s hs hr)

/-- The middle outer input is the transported inner output. -/
lemma indexedStasheffXOut_middle_eq
    {R : Type u}
    [CommRing R]
    {Obj : Type w}
    (Hom : Obj → Obj → GradedRModule (β := β) (R := R))
    (m : {n : ℕ} → [NeZero n] →
      (obj : Fin (n + 1) → Obj) → (deg : Fin n → β) →
      MultilinearMap R
        (fun i : Fin n => ComposableHomType Hom obj deg i)
        (operationTargetType Hom obj deg))
    {n : ℕ}
    (obj : Fin (n + 1) → Obj)
    (deg : Fin n → β)
    (x : ∀ i : Fin n, ComposableHomType Hom obj deg i)
    (r s : ℕ)
    (hs : 1 ≤ s)
    (hr : r + s ≤ n) :
    indexedStasheffXOut Hom m obj deg x r s hs hr (indexedStasheffMiddleIndex r s hr) =
      cast
        (congrArg
          (fun M : ModuleCat R => (M : Type u))
          (indexedStasheffMiddleModuleEq Hom obj deg r s hr))
        (indexedStasheffInner Hom m obj deg x r s hs hr) := by
  unfold indexedStasheffXOut
  simp [indexedStasheffMiddleIndex]

/-- The middle outer input vanishes whenever the inner output vanishes. -/
lemma indexedStasheffXOut_middle_eq_zero_of_inner_eq_zero
    {R : Type u}
    [CommRing R]
    {Obj : Type w}
    (Hom : Obj → Obj → GradedRModule (β := β) (R := R))
    (m : {n : ℕ} → [NeZero n] →
      (obj : Fin (n + 1) → Obj) → (deg : Fin n → β) →
      MultilinearMap R
        (fun i : Fin n => ComposableHomType Hom obj deg i)
        (operationTargetType Hom obj deg))
    {n : ℕ}
    (obj : Fin (n + 1) → Obj)
    (deg : Fin n → β)
    (x : ∀ i : Fin n, ComposableHomType Hom obj deg i)
    (r s : ℕ)
    (hs : 1 ≤ s)
    (hr : r + s ≤ n)
    (hinner : indexedStasheffInner Hom m obj deg x r s hs hr = 0) :
    indexedStasheffXOut Hom m obj deg x r s hs hr (indexedStasheffMiddleIndex r s hr) = 0 := by
  rw [indexedStasheffXOut_middle_eq]
  exact
    (cast_eq_zero_iff_of_module_eq
      (indexedStasheffMiddleModuleEq Hom obj deg r s hr)
      (indexedStasheffInner Hom m obj deg x r s hs hr)).2 hinner

/-- The outer value vanishes if the outer multilinear map itself vanishes. -/
lemma indexedStasheffOuter_eq_zero_of_map_eq_zero
    {R : Type u}
    [CommRing R]
    {Obj : Type w}
    (Hom : Obj → Obj → GradedRModule (β := β) (R := R))
    (m : {n : ℕ} → [NeZero n] →
      (obj : Fin (n + 1) → Obj) → (deg : Fin n → β) →
      MultilinearMap R
        (fun i : Fin n => ComposableHomType Hom obj deg i)
        (operationTargetType Hom obj deg))
    {n : ℕ}
    (obj : Fin (n + 1) → Obj)
    (deg : Fin n → β)
    (x : ∀ i : Fin n, ComposableHomType Hom obj deg i)
    (r s : ℕ)
    (hs : 1 ≤ s)
    (hr : r + s ≤ n)
    (hm :
      @m (n + 1 - s) ⟨Nat.ne_of_gt (indexedStasheffOuterArity_pos r s hr)⟩
        (stasheffObjOut obj r s hr) (stasheffDegOut deg r s hr) = 0) :
    indexedStasheffOuter Hom m obj deg x r s hs hr = 0 := by
  simp [indexedStasheffOuter, hm]

/-- The outer value vanishes whenever the inserted inner output vanishes. -/
lemma indexedStasheffOuter_eq_zero_of_inner_eq_zero
    {R : Type u}
    [CommRing R]
    {Obj : Type w}
    (Hom : Obj → Obj → GradedRModule (β := β) (R := R))
    (m : {n : ℕ} → [NeZero n] →
      (obj : Fin (n + 1) → Obj) → (deg : Fin n → β) →
      MultilinearMap R
        (fun i : Fin n => ComposableHomType Hom obj deg i)
        (operationTargetType Hom obj deg))
    {n : ℕ}
    (obj : Fin (n + 1) → Obj)
    (deg : Fin n → β)
    (x : ∀ i : Fin n, ComposableHomType Hom obj deg i)
    (r s : ℕ)
    (hs : 1 ≤ s)
    (hr : r + s ≤ n)
    (hinner : indexedStasheffInner Hom m obj deg x r s hs hr = 0) :
    indexedStasheffOuter Hom m obj deg x r s hs hr = 0 := by
  dsimp [indexedStasheffOuter]
  letI : NeZero (n + 1 - s) := ⟨Nat.ne_of_gt (indexedStasheffOuterArity_pos r s hr)⟩
  exact MultilinearMap.map_coord_zero
    (m (stasheffObjOut obj r s hr) (stasheffDegOut deg r s hr))
    (indexedStasheffMiddleIndex r s hr)
    (indexedStasheffXOut_middle_eq_zero_of_inner_eq_zero Hom m obj deg x r s hs hr hinner)

/-- The final transported Stasheff term vanishes exactly when the outer value vanishes. -/
lemma indexedStasheffTerm_eq_zero_iff_outer_eq_zero
    {R : Type u}
    [CommRing R]
    {Obj : Type w}
    (Hom : Obj → Obj → GradedRModule (β := β) (R := R))
    (m : {n : ℕ} → [NeZero n] →
      (obj : Fin (n + 1) → Obj) → (deg : Fin n → β) →
      MultilinearMap R
        (fun i : Fin n => ComposableHomType Hom obj deg i)
        (operationTargetType Hom obj deg))
    {n : ℕ}
    (obj : Fin (n + 1) → Obj)
    (deg : Fin n → β)
    (x : ∀ i : Fin n, ComposableHomType Hom obj deg i)
    (r s : ℕ)
    (hs : 1 ≤ s)
    (hr : r + s ≤ n) :
    indexedStasheffTerm Hom m obj deg x r s hs hr = 0 ↔
      indexedStasheffOuter Hom m obj deg x r s hs hr = 0 := by
  unfold indexedStasheffTerm
  exact cast_eq_zero_iff_of_module_eq
    (indexedStasheffTargetModuleEq Hom obj deg r s hr)
    (indexedStasheffOuter Hom m obj deg x r s hs hr)

/-- The final Stasheff term vanishes if the outer multilinear map vanishes. -/
lemma indexedStasheffTerm_eq_zero_of_outer_map_eq_zero
    {R : Type u}
    [CommRing R]
    {Obj : Type w}
    (Hom : Obj → Obj → GradedRModule (β := β) (R := R))
    (m : {n : ℕ} → [NeZero n] →
      (obj : Fin (n + 1) → Obj) → (deg : Fin n → β) →
      MultilinearMap R
        (fun i : Fin n => ComposableHomType Hom obj deg i)
        (operationTargetType Hom obj deg))
    {n : ℕ}
    (obj : Fin (n + 1) → Obj)
    (deg : Fin n → β)
    (x : ∀ i : Fin n, ComposableHomType Hom obj deg i)
    (r s : ℕ)
    (hs : 1 ≤ s)
    (hr : r + s ≤ n)
    (hm :
      @m (n + 1 - s) ⟨Nat.ne_of_gt (indexedStasheffOuterArity_pos r s hr)⟩
        (stasheffObjOut obj r s hr) (stasheffDegOut deg r s hr) = 0) :
    indexedStasheffTerm Hom m obj deg x r s hs hr = 0 :=
  (indexedStasheffTerm_eq_zero_iff_outer_eq_zero Hom m obj deg x r s hs hr).2
    (indexedStasheffOuter_eq_zero_of_map_eq_zero Hom m obj deg x r s hs hr hm)

/-- The final Stasheff term vanishes if the inner multilinear map vanishes. -/
lemma indexedStasheffTerm_eq_zero_of_inner_map_eq_zero
    {R : Type u}
    [CommRing R]
    {Obj : Type w}
    (Hom : Obj → Obj → GradedRModule (β := β) (R := R))
    (m : {n : ℕ} → [NeZero n] →
      (obj : Fin (n + 1) → Obj) → (deg : Fin n → β) →
      MultilinearMap R
        (fun i : Fin n => ComposableHomType Hom obj deg i)
        (operationTargetType Hom obj deg))
    {n : ℕ}
    (obj : Fin (n + 1) → Obj)
    (deg : Fin n → β)
    (x : ∀ i : Fin n, ComposableHomType Hom obj deg i)
    (r s : ℕ)
    (hs : 1 ≤ s)
    (hr : r + s ≤ n)
    (hm :
      @m s ⟨by omega⟩ (stasheffObjIn obj r s hr) (stasheffDegIn deg r s hr) = 0) :
    indexedStasheffTerm Hom m obj deg x r s hs hr = 0 := by
  have hinner : indexedStasheffInner Hom m obj deg x r s hs hr = 0 := by
    simp [indexedStasheffInner, hm]
  exact
    (indexedStasheffTerm_eq_zero_iff_outer_eq_zero Hom m obj deg x r s hs hr).2
      (indexedStasheffOuter_eq_zero_of_inner_eq_zero Hom m obj deg x r s hs hr hinner)

/-- The sign parity for the `(r,s)` Stasheff term:
    `sign(deg(r+s)) + ⋯ + sign(deg(n-1)) - (n-r-s)` in `ZMod 2`. -/
def stasheffSignParity
    (deg : Fin n → β)
    (r s : ℕ)
    (hr : r + s ≤ n) : Parity :=
  (∑ i : Fin (n - r - s), Grading.sign (deg ⟨r + s + i.val, by omega⟩)) -
    ((n - r - s : ℕ) : Parity)

/-- The sign `(-1)^(|a_{r+s+1}| + ⋯ + |a_n| - t)` as an integer,
    for a valid Stasheff index pair. -/
def stasheffSign
    (deg : Fin n → β)
    (r s : ℕ)
    (hr : r + s ≤ n) : ℤ :=
  (-1) ^ (stasheffSignParity deg r s hr).val

/-- The full Stasheff sum in arity `n`, with Koszul signs. -/
def indexedStasheffSum
    {R : Type u}
    [CommRing R]
    {Obj : Type w}
    (Hom : Obj → Obj → GradedRModule (β := β) (R := R))
    (m : {n : ℕ} → [NeZero n] →
      (obj : Fin (n + 1) → Obj) → (deg : Fin n → β) →
      MultilinearMap R
        (fun i : Fin n => ComposableHomType Hom obj deg i)
        (operationTargetType Hom obj deg))
    {n : ℕ}
    (obj : Fin (n + 1) → Obj)
    (deg : Fin n → β)
    (x : ∀ i : Fin n, ComposableHomType Hom obj deg i) :
    Hom (obj 0) (obj (Fin.last n)) (stasheffTargetDeg deg) :=
  ∑ r ∈ (Finset.range (n + 1)).attach,
    ∑ s ∈ (Finset.Ico 1 (n - r.1 + 1)).attach,
      let h : ValidStasheffIndices n r.1 s.1 :=
        validStasheffIndices_of_mem_ranges (n := n) r.2 s.2
      (stasheffSign deg r.1 s.1 h.2) •
        (indexedStasheffTerm Hom m obj deg x r.1 s.1 h.1 h.2)

/-- The Stasheff identities for object-indexed A∞ operations. -/
def indexedSatisfiesStasheff
    (β : Type v)
    [Grading β]
    (R : Type u)
    [CommRing R]
    {Obj : Type w}
    (Hom : Obj → Obj → GradedRModule (β := β) (R := R))
    (m : {n : ℕ} → [NeZero n] →
      (obj : Fin (n + 1) → Obj) → (deg : Fin n → β) →
      MultilinearMap R
        (fun i : Fin n => ComposableHomType Hom obj deg i)
        (operationTargetType Hom obj deg)) : Prop :=
  ∀ (n : ℕ) [NeZero n] (obj : Fin (n + 1) → Obj) (deg : Fin n → β)
    (x : ∀ i : Fin n, ComposableHomType Hom obj deg i),
    indexedStasheffSum Hom m obj deg x = 0

end AInfinityTheory
