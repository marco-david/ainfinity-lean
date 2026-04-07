module

public import Mathlib
public import AInfinity.Grading

@[expose] public section

open CategoryTheory Finset AInfinityTheory

noncomputable section

namespace AInfinityTheory

universe u v
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
  (∑ j : Fin s, stasheffDegIn deg r s hr j) + shift_ofInt (2 - (s : ℤ))

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

/-- Generic Stasheff term construction for an A∞-algebra-style operation. -/
def algebraStasheffTerm
    {R : Type u}
    [CommRing R]
    {A : GradedRModule (β := β) (R := R)}
    (m : (n : ℕ) → (deg : Fin n → β) →
      MultilinearMap R (fun i => A (deg i)) (A (operationTargetDeg deg)))
    (n : ℕ)
    (deg : Fin n → β)
    (x : ∀ i, A (deg i))
    (r s : ℕ)
    (hs : 1 ≤ s)
    (hr : r + s ≤ n) :
    A (stasheffTargetDeg deg) := by
  let degIn := stasheffDegIn deg r s hr
  let xIn : ∀ i : Fin s, A (degIn i) := fun i => x ⟨r + i.val, by omega⟩
  let inner := m s degIn xIn
  let outerN := n + 1 - s
  let degOut := stasheffDegOut deg r s hr
  let xOut : ∀ i : Fin outerN, A (degOut i) := by
    intro i
    by_cases hlt : i.val < r
    · simpa [degOut, stasheffDegOut, hlt] using x ⟨i.val, by omega⟩
    · by_cases heq : i.val = r
      · simpa [degOut, stasheffDegOut, hlt, heq] using inner
      · simpa [degOut, stasheffDegOut, hlt, heq] using x ⟨i.val + s - 1, by omega⟩
  let outer := m outerN degOut xOut
  have hdeg : operationTargetDeg degOut = stasheffTargetDeg deg := by
    exact stasheffDegOut_sum deg r s hr
  exact hdeg ▸ outer

end AInfinityTheory
