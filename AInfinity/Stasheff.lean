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

abbrev validStasheffIndices (n r s : ℕ) : Prop :=
  1 ≤ s ∧ r + s ≤ n

/-- The type of the `i`-th morphism in a composable string of objects and degrees. -/
abbrev composableHomType
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
    validStasheffIndices n r s := by
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

/-- A generic Stasheff term builder for object-indexed A∞ operations. -/
def indexedStasheffTerm
    {R : Type u}
    [CommRing R]
    {Obj : Type w}
    (Hom : Obj → Obj → GradedRModule (β := β) (R := R))
    (m : {n : ℕ} → [NeZero n] → (obj : Fin (n + 1) → Obj) → (deg : Fin n → β) →
      MultilinearMap R
        (fun i : Fin n => composableHomType Hom obj deg i)
        (operationTargetType Hom obj deg))
    {n : ℕ}
    (obj : Fin (n + 1) → Obj)
    (deg : Fin n → β)
    (x : ∀ i : Fin n, composableHomType Hom obj deg i)
    (r s : ℕ)
    (hs : 1 ≤ s)
    (hr : r + s ≤ n) :
    Hom (obj 0) (obj (Fin.last n)) (stasheffTargetDeg deg) := by
  let degIn := stasheffDegIn deg r s hr
  let objIn := stasheffObjIn obj r s hr
  let xIn : ∀ i : Fin s, composableHomType Hom objIn degIn i := fun i => by
    simpa [composableHomType, objIn, stasheffObjIn, degIn, stasheffDegIn]
      using x ⟨r + i.val, by omega⟩
  letI : NeZero s := ⟨by omega⟩
  let inner := m (n := s) objIn degIn xIn
  let outerN : ℕ := n + 1 - s
  let degOut := stasheffDegOut deg r s hr
  let objOut := stasheffObjOut obj r s hr
  let xOut : ∀ i : Fin outerN, composableHomType Hom objOut degOut i := by
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
  have houterN : NeZero outerN := ⟨by
    dsimp [outerN]
    omega⟩
  letI := houterN
  let outer := m (n := outerN) objOut degOut xOut
  have hsource : objOut 0 = obj 0 := by
    simp [objOut, stasheffObjOut]
  have hlast_gt : ¬ outerN ≤ r := by
    dsimp [outerN]
    omega
  have htarget : objOut (Fin.last outerN) = obj (Fin.last n) := by
    simp [objOut, stasheffObjOut, Fin.last, hlast_gt]
    congr
    omega
  have hdeg :
      operationTargetType Hom objOut degOut =
        Hom (obj 0) (obj (Fin.last n)) (stasheffTargetDeg deg) := by
    dsimp [operationTargetType]
    rw [hsource, htarget]
    exact congrArg (fun d => Hom (obj 0) (obj (Fin.last n)) d) (stasheffDegOut_sum deg r s hr)
  exact hdeg ▸ outer

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
    (m : {n : ℕ} → [NeZero n] → (obj : Fin (n + 1) → Obj) → (deg : Fin n → β) →
      MultilinearMap R
        (fun i : Fin n => composableHomType Hom obj deg i)
        (operationTargetType Hom obj deg))
    {n : ℕ}
    (obj : Fin (n + 1) → Obj)
    (deg : Fin n → β)
    (x : ∀ i : Fin n, composableHomType Hom obj deg i) :
    Hom (obj 0) (obj (Fin.last n)) (stasheffTargetDeg deg) :=
  Finset.sum ((Finset.range (n + 1)).attach) fun r =>
    Finset.sum ((Finset.Ico 1 (n - r.1 + 1)).attach) fun s =>
      let h : validStasheffIndices n r.1 s.1 :=
        validStasheffIndices_of_mem_ranges (n := n) r.2 s.2
      (stasheffSign deg r.1 s.1 h.2) •
        indexedStasheffTerm Hom m obj deg x r.1 s.1 h.1 h.2

/-- The Stasheff identities for object-indexed A∞ operations. -/
def indexedSatisfiesStasheff
    {R : Type u}
    [CommRing R]
    {Obj : Type w}
    (Hom : Obj → Obj → GradedRModule (β := β) (R := R))
    (m : {n : ℕ} → [NeZero n] → (obj : Fin (n + 1) → Obj) → (deg : Fin n → β) →
      MultilinearMap R
        (fun i : Fin n => composableHomType Hom obj deg i)
        (operationTargetType Hom obj deg)) : Prop :=
  ∀ (n : ℕ) (obj : Fin (n + 1) → Obj) (deg : Fin n → β)
    (x : ∀ i : Fin n, composableHomType Hom obj deg i),
    indexedStasheffSum Hom m obj deg x = 0

end AInfinityTheory
