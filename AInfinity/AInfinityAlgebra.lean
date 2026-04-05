module

public import Mathlib
public import AInfinity.Grading

@[expose] public section

open CategoryTheory Finset AInfinityCategoryTheory

noncomputable section

namespace AInfinityAlgebraTheory

universe u v
variable {β : Type v} [Grading β]
variable {n : ℕ}

abbrev GradedRModule (R : Type u) [CommRing R] :=
  GradedObject β (ModuleCat.{u} R)

/-- Target degree of the `n`-ary operation `m`. -/
abbrev operationTargetDeg
    (deg : Fin n → β) : β :=
  (∑ i, deg i) + shift_ofInt (2 - (n : ℤ))

/-- Target degree of the arity-`n` Stasheff relation. -/
abbrev stasheffTargetDeg
    (deg : Fin n → β) : β :=
  (∑ i, deg i) + shift_ofInt (3 - (n : ℤ))

structure AInfinityAlgData (R : Type u) [CommRing R] (A : GradedRModule (β := β) (R := R)) where
  m :
    (n : ℕ) →
    (deg : Fin n → β) →
    MultilinearMap R (fun i => A (deg i))
      (A (operationTargetDeg deg))

namespace AInfinityAlgData

variable {R : Type u} [CommRing R]
variable {A : GradedRModule (β := β) (R := R)}

section Internal

/-! Internal combinatorics for the Stasheff relation. -/

abbrev validStasheffIndices (n r s : ℕ) : Prop :=
  1 ≤ s ∧ r + s ≤ n

/-- Helper: degree function for the inner portion of the Stasheff composition. -/
def stasheffDegIn
    (deg : Fin n → β)
    (r s : ℕ)
    (hr : r + s ≤ n) : Fin s → β :=
  fun i => deg ⟨r + i.val, by omega⟩

/-- Helper: inner degree (the degree of the result of the inner multilinear map). -/
--  deg[r+1] + ... + deg[r+s] + 2-s
-- in bocklandt, this is the deg of term after we apply b_s, the one in the middle
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
    · -- To prove equality of finite sets, we show each set is a subset of the other.
      apply Finset.ext
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

end Internal


/-- The `(r,s)` summand in the arity-`n` Stasheff relation. -/
def stasheffTerm
  (X : AInfinityAlgData R A)
  (n : ℕ)
  (deg : Fin n → β)
  (x : ∀ i, A (deg i))
  (r s : ℕ)
  (hs : 1 ≤ s)
  (hr : r + s ≤ n) :
  A (stasheffTargetDeg deg) :=
by
  let degIn := stasheffDegIn deg r s hr
  let xIn : ∀ i : Fin s, A (degIn i) := fun i => x ⟨r + i.val, by omega⟩
  let inner := X.m s degIn xIn
  let outerN := n + 1 - s
  let degOut := stasheffDegOut deg r s hr
  let xOut : ∀ i : Fin outerN, A (degOut i) := by
    intro i
    by_cases hlt : i.val < r
    · simpa [degOut, stasheffDegOut, hlt] using x ⟨i.val, by omega⟩
    · by_cases heq : i.val = r
      · simpa [degOut, stasheffDegOut, hlt, heq] using inner
      · simpa [degOut, stasheffDegOut, hlt, heq] using x ⟨i.val + s - 1, by omega⟩
  let outer := X.m outerN degOut xOut
  have hdeg : operationTargetDeg degOut = stasheffTargetDeg deg := by
    exact stasheffDegOut_sum deg r s hr
  exact hdeg ▸ outer


/--
A single summand in the Stasheff sum, returning `0` when the indices are invalid.
This is the object that appears inside the double finite sum.
-/
def stasheffSummand
  (X : AInfinityAlgData (β := β) R A)
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
  (X : AInfinityAlgData (β := β) R A)
  (n : ℕ)
  (deg : Fin n → β)
  (x : ∀ i, A (deg i)) :
  A (stasheffTargetDeg deg) :=
  ∑ r ∈ Finset.range (n + 1),
    ∑ s ∈ Finset.Ico 1 (n - r + 1),
      (stasheffSign deg r s) • (X.stasheffSummand n deg x r s)

/-- The Stasheff identities as a property of the raw A∞ data. -/
def satisfiesStasheff
  (X : AInfinityAlgData (β := β) R A) : Prop :=
  ∀ (n : ℕ) (deg : Fin n → β) (x : ∀ i, A (deg i)),
    X.stasheffSum n deg x = 0

/-- If the indices are valid, the summand is exactly the corresponding term. -/
lemma stasheffSummand_eq_term
  (X : AInfinityAlgData (β := β) R A)
  (n : ℕ)
  (deg : Fin n → β)
  (x : ∀ i, A (deg i))
  (r s : ℕ)
  (h : validStasheffIndices n r s) :
  X.stasheffSummand n deg x r s
    = X.stasheffTerm n deg x r s h.1 h.2 := by
  unfold stasheffSummand; aesop


/-- If the indices are invalid, the summand vanishes. -/
lemma stasheffSummand_eq_zero
  (X : AInfinityAlgData (β := β) R A)
  (n : ℕ)
  (deg : Fin n → β)
  (x : ∀ i, A (deg i))
  (r s : ℕ)
  (h : ¬ validStasheffIndices n r s) :
  X.stasheffSummand n deg x r s = 0 := by
  unfold AInfinityAlgData.stasheffSummand; aesop

--some helper lemmas
lemma stasheffTerm_zero_of_inner_zero
    (X : AInfinityAlgData (β := β) R A)
    (n : ℕ) (deg : Fin n → β) (x : ∀ i, A (deg i))
    (r s : ℕ) (hs : 1 ≤ s) (hr : r + s ≤ n)
    (hm : X.m s (stasheffDegIn deg r s hr) = 0) :
    X.stasheffTerm n deg x r s hs hr = 0 := by
  -- Since the inner multilinear map is zero, the entire inner value is zero.
  have h_inner_zero :
      X.m s (stasheffDegIn deg r s hr) (fun i => x ⟨r + i.val, by omega⟩) = 0 := by
    aesop
  simp +decide [h_inner_zero, AInfinityAlgData.stasheffTerm]
  have h_xOut_zero :
      ∀ (f : ∀ i : Fin (n + 1 - s), A (stasheffDegOut deg r s hr i)),
        f ⟨r, by omega⟩ = 0 →
          X.m (n + 1 - s) (stasheffDegOut deg r s hr) f = 0 := by
    intro f hf_zero
    convert MultilinearMap.map_coord_zero _ _ hf_zero
  grind +locals
lemma stasheffTerm_zero_of_outer_zero
    (X : AInfinityAlgData (β := β) R A)
    (n : ℕ) (deg : Fin n → β) (x : ∀ i, A (deg i))
    (r s : ℕ) (hs : 1 ≤ s) (hr : r + s ≤ n)
    (hm : X.m (n + 1 - s) (stasheffDegOut deg r s hr) = 0) :
    X.stasheffTerm n deg x r s hs hr = 0 := by
  unfold AInfinityAlgData.stasheffTerm
  -- Since the outer multilinear map is zero, applying it to any input gives zero.
  have h_outer_zero_apply :
      ∀ xOut : ∀ i : Fin (n + 1 - s), A (stasheffDegOut deg r s hr i),
        X.m (n + 1 - s) (stasheffDegOut deg r s hr) xOut = 0 := by
    aesop
  grind
lemma stasheffSummand_zero_of_inner_or_outer_zero
    (X : AInfinityAlgData (β := β) R A)
    (n : ℕ) (deg : Fin n → β) (x : ∀ i, A (deg i))
    (r s : ℕ)
    (h : ∀ (_hs : 1 ≤ s) (hr : r + s ≤ n),
          X.m s (stasheffDegIn deg r s hr) = 0 ∨
          X.m (n + 1 - s) (stasheffDegOut deg r s hr) = 0) :
    X.stasheffSummand n deg x r s = 0 := by
  by_cases hrs : validStasheffIndices n r s
  · rw [
      stasheffSummand_eq_term
        (X := X) (n := n) (deg := deg) (x := x) (r := r) (s := s) hrs
    ]
    rcases h hrs.1 hrs.2 with h_inner | h_outer
    · exact
        stasheffTerm_zero_of_inner_zero
          (X := X) (n := n) (deg := deg) (x := x)
          (r := r) (s := s) hrs.1 hrs.2 h_inner
    · exact
        stasheffTerm_zero_of_outer_zero
          (X := X) (n := n) (deg := deg) (x := x)
          (r := r) (s := s) hrs.1 hrs.2 h_outer
  · exact
      stasheffSummand_eq_zero
        (X := X) (n := n) (deg := deg) (x := x) (r := r) (s := s) hrs

end AInfinityAlgData

/-- An A∞-algebra is raw data together with the Stasheff identities. -/
structure AInfinityAlgebra (R : Type u) [CommRing R] (A : GradedRModule (β := β) (R := R))
  extends AInfinityAlgData (β := β) R A where
  stasheff :
    AInfinityAlgData.satisfiesStasheff
      (β := β) toAInfinityAlgData

namespace AInfinityAlgebra

variable {R : Type u} [CommRing R]
variable {A : GradedRModule (β := β) (R := R)}

/-- Re-export the Stasheff identity in a convenient form. -/
lemma stasheff_eq_zero
  (X : AInfinityAlgebra (β := β) R A)
  (n : ℕ)
  (deg : Fin n → β)
  (x : ∀ i, A (deg i)) :
  X.toAInfinityAlgData.stasheffSum n deg x = 0 :=
  X.stasheff n deg x

end AInfinityAlgebra

end AInfinityAlgebraTheory
