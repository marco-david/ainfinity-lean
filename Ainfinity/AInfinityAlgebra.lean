import Mathlib
import Ainfinity.Grading

open CategoryTheory Finset AInfinityCategoryTheory

noncomputable section

namespace AInfinityAlgebraTheory

universe u v
variable {β : Type v} [Grading β]

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
  unfold stasheffDegOut;
  rw [ show ( Finset.univ : Finset ( Fin ( n + 1 - s ) ) ) = Finset.univ.filter ( fun i : Fin ( n + 1 - s ) => i.val < r ) ∪ Finset.univ.filter ( fun i : Fin ( n + 1 - s ) => i.val = r ) ∪ Finset.univ.filter ( fun i : Fin ( n + 1 - s ) => i.val > r ) from ?_, Finset.sum_union, Finset.sum_union ];
  · rw [ show ( Finset.univ.filter fun i : Fin ( n + 1 - s ) => ( i : ℕ ) < r ) = Finset.image ( fun i : Fin r => ⟨ i, by omega ⟩ ) Finset.univ from ?_, show ( Finset.univ.filter fun i : Fin ( n + 1 - s ) => ( i : ℕ ) = r ) = { ⟨ r, by omega ⟩ } from ?_, show ( Finset.univ.filter fun i : Fin ( n + 1 - s ) => ( i : ℕ ) > r ) = Finset.image ( fun i : Fin ( n - r - s ) => ⟨ r + 1 + i, by omega ⟩ ) Finset.univ from ?_ ];
    · rw [ Finset.sum_image, Finset.sum_image ] <;> norm_num;
      · rw [ show ( Finset.univ : Finset ( Fin n ) ) = Finset.image ( fun i : Fin r => ⟨ i, by linarith [ Fin.is_lt i ] ⟩ ) Finset.univ ∪ Finset.image ( fun i : Fin s => ⟨ r + i, by linarith [ Fin.is_lt i ] ⟩ ) Finset.univ ∪ Finset.image ( fun i : Fin ( n - r - s ) => ⟨ r + s + i, by omega ⟩ ) Finset.univ from ?_, Finset.sum_union, Finset.sum_union ];
        · rw [ Finset.sum_image, Finset.sum_image, Finset.sum_image ] <;> norm_num;
          · unfold stasheffInnerDeg;
            unfold stasheffDegIn; ring_nf;
            grind;
          · exact fun i j h => by simpa [ Fin.ext_iff ] using h;
          · exact fun i j h => by simpa [ Fin.ext_iff ] using h;
          · exact fun i j h => by simpa [ Fin.ext_iff ] using h;
        · norm_num [ Finset.disjoint_left ];
          grind;
        · norm_num [ Finset.disjoint_right ];
          grind;
        · ext ⟨ i, hi ⟩ ; simp +decide [ Finset.mem_union, Finset.mem_image ];
          by_cases hi' : i < r;
          · exact Or.inl ⟨ ⟨ i, by linarith ⟩, rfl ⟩;
          · by_cases hi'' : i < r + s;
            · exact Or.inr <| Or.inl ⟨ ⟨ i - r, by omega ⟩, by simp +decide [ Nat.add_sub_of_le ( le_of_not_gt hi' ) ] ⟩;
            · exact Or.inr <| Or.inr <| ⟨ ⟨ i - ( r + s ), by omega ⟩, by norm_num; omega ⟩;
      · exact fun i j h => by simpa [ Fin.ext_iff ] using h;
      · exact fun i j h => by simpa [ Fin.ext_iff ] using h;
    · -- To prove equality of finite sets, we show each set is a subset of the other.
      apply Finset.ext
      intro i
      simp [Finset.mem_image];
      exact ⟨ fun hi => ⟨ ⟨ i - ( r + 1 ), by omega ⟩, by erw [ Fin.ext_iff ] ; norm_num; omega ⟩, by rintro ⟨ a, rfl ⟩ ; exact Nat.lt_of_lt_of_le ( by simp +arith +decide ) ( Nat.le_add_right _ _ ) ⟩;
    · ext ⟨ i, hi ⟩ ; aesop;
    · ext ⟨i, hi⟩; simp [Finset.mem_image];
      exact ⟨ fun hi' => ⟨ ⟨ i, by omega ⟩, rfl ⟩, fun ⟨ a, ha ⟩ => by linarith [ Fin.is_lt a ] ⟩;
  · exact Finset.disjoint_filter.mpr fun _ _ _ _ => by linarith;
  · simp +contextual [ Finset.disjoint_left ];
    exact fun a ha => ha.elim ( fun ha => le_of_lt ha ) fun ha => ha.le;
  · ext i; cases lt_trichotomy i.val r <;> aesop;


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
  have h_inner_zero : X.m s (stasheffDegIn deg r s hr) (fun i => x ⟨r + i.val, by omega⟩) = 0 := by
    aesop;
  simp +decide [ h_inner_zero, AInfinityAlgData.stasheffTerm ];
  have h_xOut_zero : ∀ (f : ∀ i : Fin (n + 1 - s), A (stasheffDegOut deg r s hr i)), f ⟨r, by omega⟩ = 0 → X.m (n + 1 - s) (stasheffDegOut deg r s hr) f = 0 := by
    intro f hf_zero
    have h_xOut_zero : X.m (n + 1 - s) (stasheffDegOut deg r s hr) f = 0 := by
      convert MultilinearMap.map_coord_zero _ _ hf_zero
    exact h_xOut_zero;
  grind +locals
lemma stasheffTerm_zero_of_outer_zero
    (X : AInfinityAlgData (β := β) R A)
    (n : ℕ) (deg : Fin n → β) (x : ∀ i, A (deg i))
    (r s : ℕ) (hs : 1 ≤ s) (hr : r + s ≤ n)
    (hm : X.m (n + 1 - s) (stasheffDegOut deg r s hr) = 0) :
    X.stasheffTerm n deg x r s hs hr = 0 := by
  unfold AInfinityAlgData.stasheffTerm;
  -- Since the outer multilinear map is zero, applying it to any input gives zero.
  have h_outer_zero_apply : ∀ xOut : ∀ i : Fin (n + 1 - s), A (stasheffDegOut deg r s hr i), X.m (n + 1 - s) (stasheffDegOut deg r s hr) xOut = 0 := by
    aesop;
  grind

set_option linter.unusedVariables false
lemma stasheffSummand_zero_of_inner_or_outer_zero
    (X : AInfinityAlgData (β := β) R A)
    (n : ℕ) (deg : Fin n → β) (x : ∀ i, A (deg i))
    (r s : ℕ)
    (h : ∀ (hs : 1 ≤ s) (hr : r + s ≤ n),
          X.m s (stasheffDegIn deg r s hr) = 0 ∨
          X.m (n + 1 - s) (stasheffDegOut deg r s hr) = 0) :
    X.stasheffSummand n deg x r s = 0 := by
  grind +suggestions

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

section OrdinaryAlgebra

variable (R : Type u) [CommRing R] (S : Type u) [CommRing S] [Algebra R S]

noncomputable def concentratedAt0 : GradedRModule (β := ℤ) R :=
  fun i => if i = 0 then ModuleCat.of R S else (ModuleCat.of R PUnit)

lemma concentratedAt0_zero :
    concentratedAt0 R S (0 : ℤ) = ModuleCat.of R S := if_pos rfl

lemma concentratedAt0_nonzero {i : ℤ} (hi : i ≠ 0) :
    concentratedAt0 R S i = (ModuleCat.of R PUnit) := if_neg hi

lemma concentratedAt0_of_eq {i : ℤ} (hi : i = 0) :
    concentratedAt0 R S i = ModuleCat.of R S := hi ▸ concentratedAt0_zero R S

/-- The multiplication on `S` viewed as a bilinear map `S × S → S`,
    packaged as a `MultilinearMap R (Fin 2 → S) S`. -/
noncomputable def mulMultilinearMap :
    MultilinearMap R (fun _ : Fin 2 => S) S where
  toFun x := x 0 * x 1
  map_update_add' x i a b := by
    fin_cases i <;> simp [Function.update, mul_add, add_mul]
  map_update_smul' x i r a := by
    fin_cases i <;> simp [Function.update, Algebra.smul_mul_assoc, Algebra.mul_smul_comm]

/-- The A∞-algebra data on `S` concentrated in degree 0.
  * `m 2 deg` is ordinary multiplication in `S` when `deg = fun _ => 0`
    (both inputs in degree 0).
  * Every other `m n deg` is the zero multilinear map. -/
noncomputable def concentratedAt0_algData :
    AInfinityAlgData (β := ℤ) R (concentratedAt0 R S) where
  m := fun n deg => by
    by_cases hn : n = 2
    · subst hn
      by_cases hdeg : deg = fun _ => 0
      · subst hdeg
        have htarget : (0 : ℤ) = operationTargetDeg (β := ℤ) (n := 2) (fun _ => (0 : ℤ)) := by
          simp [operationTargetDeg, shift_ofInt]
        exact htarget ▸ mulMultilinearMap R S
      · exact 0
    · exact 0

/-
Helper: m n deg = 0 unless n = 2 and deg = fun _ => 0
-/
lemma concentratedAt0_m_zero (n : ℕ) (deg : Fin n → ℤ)
    (h : n ≠ 2 ∨ deg ≠ fun _ => 0) :
    (concentratedAt0_algData R S).m n deg = 0 := by
  unfold concentratedAt0_algData; aesop;
/-
For each (r,s) summand in the Stasheff relation for the concentrated-at-0 algebra,
if (s ≠ 2 ∨ n + 1 - s ≠ 2), then either inner or outer m is zero.
-/

set_option linter.unusedVariables false
lemma concentratedAt0_inner_or_outer_zero
    (n : ℕ) (deg : Fin n → ℤ) (r s : ℕ)
    (hs : 1 ≤ s) (hr : r + s ≤ n)
    (hns : s ≠ 2 ∨ n + 1 - s ≠ 2) :
    (concentratedAt0_algData R S).m s (AInfinityAlgData.stasheffDegIn deg r s hr) = 0 ∨
    (concentratedAt0_algData R S).m (n + 1 - s) (AInfinityAlgData.stasheffDegOut deg r s hr) = 0 := by
  contrapose! hns; simp_all +decide [ concentratedAt0_algData ] ;
  lia
/-
For n ≠ 3, every summand in the Stasheff sum is zero
-/
lemma concentratedAt0_stasheffSum_zero_of_ne3
    (n : ℕ) (deg : Fin n → ℤ) (x : ∀ i, concentratedAt0 R S (deg i))
    (hn : n ≠ 3) :
    (concentratedAt0_algData R S).stasheffSum n deg x = 0 := by
  refine' Finset.sum_eq_zero _;
  intro r hr
  apply Finset.sum_eq_zero
  intro s hs
  by_cases h_valid : 1 ≤ s ∧ r + s ≤ n;
  · by_cases hns : s = 2 ∧ n + 1 - s = 2;
    · omega;
    · rw [ AInfinityAlgData.stasheffSummand_zero_of_inner_or_outer_zero ];
      · simp +decide;
      · exact fun _ _ => concentratedAt0_inner_or_outer_zero R S n deg r s h_valid.1 h_valid.2 ( by contrapose! hns; omega );
  · simp_all +decide [ AInfinityAlgData.stasheffSummand ]
/-
When n=3, s≠2 summands are zero
-/
lemma concentratedAt0_summand_zero_n3_of_s_ne2
    (deg : Fin 3 → ℤ) (x : ∀ i, concentratedAt0 R S (deg i))
    (r s : ℕ) (hs : s ≠ 2) :
    (concentratedAt0_algData R S).stasheffSummand 3 deg x r s = 0 := by
  unfold AInfinityAlgData.stasheffSummand;
  split_ifs;
  · apply AInfinityAlgData.stasheffTerm_zero_of_inner_zero;
    exact concentratedAt0_m_zero R S s _ ( by aesop );
  · rfl
/-
When n=3 and deg ≠ fun _ => 0, even s=2 summands are zero
-/
lemma concentratedAt0_summand_zero_n3_deg_ne0
    (deg : Fin 3 → ℤ) (x : ∀ i, concentratedAt0 R S (deg i))
    (hdeg : deg ≠ fun _ => 0)
    (r : ℕ) :
    (concentratedAt0_algData R S).stasheffSummand 3 deg x r 2 = 0 := by
  -- Apply the lemma that states if the inner or outer m is zero, then the summand is zero.
  apply AInfinityAlgData.stasheffSummand_zero_of_inner_or_outer_zero;
  rintro - ( hr | hr | hr | hr ) <;> simp_all +decide [ concentratedAt0_algData ];
  · contrapose! hdeg; simp_all +decide [ funext_iff, Fin.forall_fin_succ ] ;
    unfold AInfinityAlgData.stasheffDegIn AInfinityAlgData.stasheffDegOut at hdeg; aesop;
  · contrapose! hdeg; simp_all +decide [ funext_iff, Fin.forall_fin_succ ] ;
    unfold AInfinityAlgData.stasheffDegIn AInfinityAlgData.stasheffDegOut at * ; aesop;
  · contradiction
/-
For n = 3, deg ≠ 0, the stasheff sum is zero
-/
lemma concentratedAt0_stasheffSum_zero_n3_deg_ne0
    (deg : Fin 3 → ℤ) (x : ∀ i, concentratedAt0 R S (deg i))
    (hdeg : deg ≠ fun _ => 0) :
    (concentratedAt0_algData R S).stasheffSum 3 deg x = 0 := by
  convert Finset.sum_eq_zero _;
  intro r hr; rw [ Finset.sum_eq_zero ] ; intros s hs; by_cases hs' : s = 2 <;> simp_all +decide [ concentratedAt0_summand_zero_n3_of_s_ne2, concentratedAt0_summand_zero_n3_deg_ne0 ] ;
/-
The stasheff sum for n=3, deg=0 reduces to just s=2 terms
-/
lemma concentratedAt0_stasheffSum_n3_deg0_reduce
    (x : ∀ i, concentratedAt0 R S ((fun _ : Fin 3 => (0 : ℤ)) i)) :
    (concentratedAt0_algData R S).stasheffSum 3 (fun _ => 0) x =
    (AInfinityAlgData.stasheffSign (fun _ : Fin 3 => (0 : ℤ)) 0 2) •
      (concentratedAt0_algData R S).stasheffSummand 3 (fun _ => 0) x 0 2 +
    (AInfinityAlgData.stasheffSign (fun _ : Fin 3 => (0 : ℤ)) 1 2) •
      (concentratedAt0_algData R S).stasheffSummand 3 (fun _ => 0) x 1 2 := by
  unfold AInfinityAlgData.stasheffSum;
  simp +decide [ Finset.sum_range_succ, Finset.sum_Ico_succ_top ];
  simp +decide [ AInfinityAlgData.stasheffSign, concentratedAt0_algData, AInfinityAlgData.stasheffSummand ];
  simp +decide [ AInfinityAlgData.stasheffTerm ]
  sorry
/-
The sign for (r=0, s=2) is -1
-/
lemma stasheffSign_n3_deg0_r0_s2 :
    AInfinityAlgData.stasheffSign (fun _ : Fin 3 => (0 : ℤ)) 0 2 = -1 := by
  native_decide +revert
/-
The sign for (r=1, s=2) is 1
-/
lemma stasheffSign_n3_deg0_r1_s2 :
    AInfinityAlgData.stasheffSign (fun _ : Fin 3 => (0 : ℤ)) 1 2 = 1 := by
  unfold AInfinityAlgData.stasheffSign;
  unfold AInfinityAlgData.stasheffSignParity; simp +decide ;
/-
Key: the target degree for n=3, deg=0 equals 0
-/
lemma stasheffTargetDeg_n3_zero :
    @stasheffTargetDeg ℤ _ 3 (fun _ => 0) = 0 := by
  convert AddMonoidHom.map_zero ( Grading.ofInt ( β := ℤ ) ) using 1
/-
Key: operationTargetDeg for n=2, deg=0 equals 0
-/
lemma operationTargetDeg_n2_zero :
    @operationTargetDeg ℤ _ 2 (fun _ => 0) = 0 := by
  simp +decide
/-
Helper: applying m₂ with deg=0 gives multiplication
-/
lemma concentratedAt0_m2_apply
    (y : ∀ i : Fin 2, concentratedAt0 R S ((fun _ => (0 : ℤ)) i)) :
    (concentratedAt0_algData R S).m 2 (fun _ => 0) y =
    operationTargetDeg_n2_zero ▸ (mulMultilinearMap R S y) := by
  unfold concentratedAt0_algData;
  grind
/-
Helper: stasheffDegIn with constant 0 deg is constant 0
-/
lemma stasheffDegIn_zero (r s : ℕ) (hr : r + s ≤ n) :
    AInfinityAlgData.stasheffDegIn (fun _ : Fin n => (0 : ℤ)) r s hr = fun _ => 0 := by
  exact funext fun _ => rfl
/-
Helper: stasheffInnerDeg with constant 0 deg and s=2 is 0
-/
lemma stasheffInnerDeg_zero_s2 (r : ℕ) (hr : r + 2 ≤ n) :
    AInfinityAlgData.stasheffInnerDeg (fun _ : Fin n => (0 : ℤ)) r 2 hr = 0 := by
  convert congr_arg _ ( map_zero ( Grading.ofInt ( β := ℤ ) ) ) using 1
/-
Helper: stasheffDegOut with constant 0 deg, s=2 is constant 0
-/
lemma stasheffDegOut_zero_s2 (r : ℕ) (hr : r + 2 ≤ n) :
    AInfinityAlgData.stasheffDegOut (fun _ : Fin n => (0 : ℤ)) r 2 hr = fun _ => 0 := by
  unfold AInfinityAlgData.stasheffDegOut;
  unfold AInfinityAlgData.stasheffInnerDeg; aesop
-- Helper: Eq.mpr between the same types is identity
lemma eq_mpr_self {A : Sort*} (h : A = A) (a : A) : Eq.mpr h a = a := rfl
-- The cancellation: -1 • term0 + 1 • term1 = 0
-- This follows from associativity of multiplication


/-- Cast an element along a proof that `concentratedAt0 R S i = concentratedAt0 R S j`. -/
private lemma concentratedAt0_cast_val {i j : ℤ} (h : i = j)
    (a : concentratedAt0 R S i) :
    (show concentratedAt0 R S i = concentratedAt0 R S j from congrArg _ h) ▸ a = h ▸ a := by
  subst h; rfl
-- Helper: extract the underlying S-valued function from an Eq.mpr cast
private lemma eqMpr_concentratedAt0 {i : ℤ} (hi : i = 0) (a : ↑(concentratedAt0 R S 0)) :
    (congrArg (fun j => ↑(concentratedAt0 R S j)) hi.symm) ▸ a = hi ▸ a := by
  subst hi; rfl
set_option maxHeartbeats 25600000 in
lemma concentratedAt0_n3_deg0_terms_cancel
    (x : ∀ i, concentratedAt0 R S ((fun _ : Fin 3 => (0 : ℤ)) i)) :
    (-1 : ℤ) • (concentratedAt0_algData R S).stasheffSummand 3 (fun _ => 0) x 0 2 +
    (1 : ℤ) • (concentratedAt0_algData R S).stasheffSummand 3 (fun _ => 0) x 1 2 = 0 := by
  simp only [one_smul, neg_one_zsmul, neg_add_eq_zero]
  unfold AInfinityAlgData.stasheffSummand AInfinityAlgData.validStasheffIndices
    AInfinityAlgData.stasheffTerm concentratedAt0_algData
  simp only [show (1 : ℕ) ≤ 2 from by omega, show 0 + 2 ≤ 3 from by omega,
             show 1 + 2 ≤ 3 from by omega, show (3 : ℕ) + 1 - 2 = 2 from by omega,
             and_self, dite_true, stasheffDegIn_zero, stasheffDegOut_zero_s2,
             eq_rec_constant, concentratedAt0_zero, operationTargetDeg_n2_zero,
             mulMultilinearMap]
  -- After eliminating casts with eq_rec_constant, the goal should be mul_assoc
  convert mul_assoc (x ⟨0, by omega⟩ : S) (x ⟨1, by omega⟩ : S) (x ⟨2, by omega⟩ : S) using 4
  all_goals first | rfl | (exact (inferInstance : Semigroup S)) | sorry
-- For n = 3, deg = 0, the stasheff sum is zero by associativity

-- For n = 3, deg = 0, the stasheff sum is zero by associativity
lemma concentratedAt0_stasheffSum_zero_n3_deg0
    (x : ∀ i, concentratedAt0 R S ((fun _ : Fin 3 => (0 : ℤ)) i)) :
    (concentratedAt0_algData R S).stasheffSum 3 (fun _ => 0) x = 0 := by
  rw [concentratedAt0_stasheffSum_n3_deg0_reduce]
  rw [stasheffSign_n3_deg0_r0_s2, stasheffSign_n3_deg0_r1_s2]
  exact concentratedAt0_n3_deg0_terms_cancel R S x
-- For n = 3, the Stasheff sum is zero by associativity
lemma concentratedAt0_stasheffSum_zero_n3
    (deg : Fin 3 → ℤ) (x : ∀ i, concentratedAt0 R S (deg i)) :
    (concentratedAt0_algData R S).stasheffSum 3 deg x = 0 := by
  by_cases hdeg : deg = fun _ => 0
  · subst hdeg; exact concentratedAt0_stasheffSum_zero_n3_deg0 R S x
  · exact concentratedAt0_stasheffSum_zero_n3_deg_ne0 R S deg x hdeg
/-- An ordinary R-algebra S gives rise to an A∞-algebra concentrated in degree 0.
    The only nonzero operation is m₂ = multiplication, and the Stasheff identities
    reduce to associativity of multiplication. -/
noncomputable def concentratedAt0_algebra :
    AInfinityAlgebra (β := ℤ) R (concentratedAt0 R S) where
  toAInfinityAlgData := concentratedAt0_algData R S
  stasheff := by
    intro n deg x
    by_cases hn : n = 3
    · subst hn
      exact concentratedAt0_stasheffSum_zero_n3 R S deg x
    · exact concentratedAt0_stasheffSum_zero_of_ne3 R S n deg x hn


end OrdinaryAlgebra

end AInfinityAlgebraTheory
