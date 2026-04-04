import Mathlib
import Ainfinity.Grading
import Ainfinity.AInfinityAlgebra
open CategoryTheory Finset AInfinityCategoryTheory AInfinityAlgebraTheory AInfinityAlgData
noncomputable section
namespace AInfinityMorphismTheory
universe u v w
variable {β_A : Type v} [Grading β_A]
variable {β_B : Type w} [Grading β_B]
/-! ## Target degree functions -/
/-- Target degree of `φ_n` applied to inputs of the given degrees.
    `φ_n` has degree `1 − n`, so the output lives in
    `∑ i, deg_trans(deg i) + ofInt(1 − n)` in `β_B`. -/
abbrev morphismTargetDeg
    (deg_trans : β_A →+ β_B)
    {n : ℕ} (deg : Fin n → β_A) : β_B :=
  (∑ i, deg_trans (deg i)) + shift_ofInt (1 - (n : ℤ))
/-- Target degree of the morphism equation.
    Both sides of the A∞-morphism equation land in
    `∑ i, deg_trans(deg i) + ofInt(2 − n)` in `β_B`. -/
abbrev morphismEqTargetDeg
    (deg_trans : β_A →+ β_B)
    {n : ℕ} (deg : Fin n → β_A) : β_B :=
  (∑ i, deg_trans (deg i)) + shift_ofInt (2 - (n : ℤ))
/-! ## Morphism data -/
/-- The raw data of an A∞-morphism from `(A, β_A)` to `(B, β_B)`.
    * `deg_trans` is a group homomorphism `β_A →+ β_B` translating degrees,
      compatible with the integer embeddings and the sign/parity maps.
    * `phi n` is the `n`-ary component map `φ_n : A^{⊗n} → B` of degree `1 − n`. -/
structure AInfinityMorphismData (R : Type u) [CommRing R]
    (A : GradedRModule (β := β_A) (R := R))
    (B : GradedRModule (β := β_B) (R := R)) where
  /-- Group homomorphism translating degrees from `β_A` to `β_B`. -/
  deg_trans : β_A →+ β_B
  /-- `deg_trans` is compatible with the integer embeddings:
      `deg_trans ∘ ofInt_A = ofInt_B`. -/

  --deg_trans_ofInt : ∀ n : ℤ, deg_trans (@Grading.ofInt β_A _ n) = @Grading.ofInt β_B _ n
  deg_trans_ofInt : ∀ n : ℤ, deg_trans (Grading.ofInt n) = Grading.ofInt n
  /-- `deg_trans` preserves sign/parity:
      `sign_B ∘ deg_trans = sign_A`. -/
  deg_trans_sign : ∀ b : β_A, Grading.sign (deg_trans b) = Grading.sign b
  /-- The `n`-ary component map `φ_n`. -/
  phi :
    (n : ℕ) →
    (deg : Fin n → β_A) →
    MultilinearMap R (fun i => A (deg i))
      (B (morphismTargetDeg deg_trans deg))
namespace AInfinityMorphismData
variable {R : Type u} [CommRing R]
variable {A : GradedRModule (β := β_A) (R := R)}
variable {B : GradedRModule (β := β_B) (R := R)}
/-! ## LHS of the morphism equation
The LHS of the A∞-morphism equation is:
  `∑_{r+s+t=n, s≥1} (-1)^† φ_{r+1+t}(a_1, …, a_r, m^A_s(a_{r+1}, …, a_{r+s}), a_{r+s+1}, …, a_n)`
where `† = |a_{r+s+1}| + ⋯ + |a_n| − t` (the same sign as in the Stasheff relation).
Structurally this is the same as the Stasheff term, except the *outer* operation is `φ`
(mapping `A → B`) rather than `m^A` (mapping `A → A`).
-/
section LHS
/-
PROBLEM
Degree compatibility for the LHS: the target of `φ_{n+1−s}` applied with
    the outer degrees `stasheffDegOut` equals the morphism equation target degree.
PROVIDED SOLUTION
Unfold morphismTargetDeg and morphismEqTargetDeg. The goal becomes showing
(∑ i, F.deg_trans (stasheffDegOut deg r s hr i)) + shift_ofInt (1 - ((n+1-s : ℕ) : ℤ)) = (∑ i, F.deg_trans (deg i)) + shift_ofInt (2 - (n : ℤ)).
Step 1: Rewrite ∑ F.deg_trans(stasheffDegOut i) as F.deg_trans(∑ stasheffDegOut i) using map_sum.
Step 2: Apply stasheffDegOut_sum_core to get ∑ stasheffDegOut = ∑ deg + shift_ofInt(2-s).
Step 3: Use map_add and F.deg_trans_ofInt to transform F.deg_trans(shift_ofInt(2-s)) = shift_ofInt(2-s) in β_B.
Step 4: The goal reduces to showing shift_ofInt(2-s) + shift_ofInt(1-(n+1-s)) = shift_ofInt(2-n), which follows from the fact that ofInt is a group hom and (2-s) + (1-(n+1-s)) = 2-n.
-/
lemma morphismLHS_deg_compat
    (F : AInfinityMorphismData R A B)
    {n : ℕ}
    (deg : Fin n → β_A)
    (r s : ℕ)
    (hr : r + s ≤ n) :
    morphismTargetDeg F.deg_trans (stasheffDegOut deg r s hr) =
    morphismEqTargetDeg F.deg_trans deg := by
  unfold morphismTargetDeg morphismEqTargetDeg;
  rw [ ← map_sum ];
  rw [ show F.deg_trans ( ∑ x : Fin ( n + 1 - s ), stasheffDegOut deg r s hr x ) = F.deg_trans ( ∑ i : Fin n, deg i + shift_ofInt ( 2 - ( s : ℤ ) ) ) by
        exact congr_arg _ ( stasheffDegOut_sum_core deg r s hr ) ];
  rw [ map_add, show F.deg_trans ( shift_ofInt ( 2 - s : ℤ ) ) = shift_ofInt ( 2 - s : ℤ ) from ?_, show ( n + 1 - s : ℕ ) = ( n - s ) + 1 from ?_ ] ; norm_num ; ring;
  · simp +decide [ add_assoc, Nat.cast_sub ( show s ≤ n from by linarith ) ];
    simp +decide [ shift_ofInt ];
  · rw [ Nat.sub_add_comm ( by linarith ) ];
  · exact F.deg_trans_ofInt _
/-- The `(r, s)` summand on the LHS of the morphism equation:
    `φ_{r+1+t}(a_1, …, a_r, m^A_s(a_{r+1}, …, a_{r+s}), a_{r+s+1}, …, a_n)`. -/
def morphismLHSTerm
    (F : AInfinityMorphismData R A B)
    (X_A : AInfinityAlgData (β := β_A) R A)
    (n : ℕ)
    (deg : Fin n → β_A)
    (x : ∀ i, A (deg i))
    (r s : ℕ)
    (hs : 1 ≤ s)
    (hr : r + s ≤ n) :
    B (morphismEqTargetDeg F.deg_trans deg) := by
  -- Inner: apply m^A_s to the (r+1, …, r+s) block
  let degIn := stasheffDegIn deg r s hr
  let xIn : ∀ i : Fin s, A (degIn i) := fun i => x ⟨r + i.val, by omega⟩
  let inner := X_A.m s degIn xIn
  -- Outer: apply φ_{n+1-s} to (a_1, …, a_r, inner, a_{r+s+1}, …, a_n)
  let outerN := n + 1 - s
  let degOut := stasheffDegOut deg r s hr
  let xOut : ∀ i : Fin outerN, A (degOut i) := by
    intro i
    by_cases hlt : i.val < r
    · simpa [degOut, stasheffDegOut, hlt] using x ⟨i.val, by omega⟩
    · by_cases heq : i.val = r
      · simpa [degOut, stasheffDegOut, hlt, heq] using inner
      · simpa [degOut, stasheffDegOut, hlt, heq] using x ⟨i.val + s - 1, by omega⟩
  let outer := F.phi outerN degOut xOut
  -- Cast to the equation target degree
  have hdeg := morphismLHS_deg_compat F deg r s hr
  exact hdeg ▸ outer
/-- LHS summand, returning `0` for invalid indices. -/
def morphismLHSSummand
    (F : AInfinityMorphismData R A B)
    (X_A : AInfinityAlgData (β := β_A) R A)
    (n : ℕ)
    (deg : Fin n → β_A)
    (x : ∀ i, A (deg i))
    (r s : ℕ) :
    B (morphismEqTargetDeg F.deg_trans deg) :=
  if h : validStasheffIndices n r s then
    F.morphismLHSTerm X_A n deg x r s h.1 h.2
  else
    0
/-- The full LHS sum with signs:
    `∑_{r,s} (-1)^† φ_{r+1+t}(…, m^A_s(…), …)`. -/
def morphismLHSSum
    (F : AInfinityMorphismData R A B)
    (X_A : AInfinityAlgData (β := β_A) R A)
    (n : ℕ)
    (deg : Fin n → β_A)
    (x : ∀ i, A (deg i)) :
    B (morphismEqTargetDeg F.deg_trans deg) :=
  ∑ r ∈ Finset.range (n + 1),
    ∑ s ∈ Finset.Ico 1 (n - r + 1),
      (stasheffSign deg r s) • (F.morphismLHSSummand X_A n deg x r s)
end LHS

/-! ## RHS of the morphism equation
The RHS of the A∞-morphism equation is:
  `∑_{k ≥ 1} ∑_{i₁+⋯+iₖ=n} (-1)^‡ m^B_k(φ_{i₁}(block₁), …, φ_{iₖ}(blockₖ))`
where the sum is over all ordered compositions `(i₁, …, iₖ)` of `n` with each `iⱼ ≥ 1`,
and `‡` is the Koszul sign from commuting the `φ`-maps past the inputs:
  `‡ = ∑_{l=2}^{k} (iₗ − 1) · (|a₁| + ⋯ + |a_{s_{l−1}}|)`
where `sₗ = i₁ + ⋯ + iₗ` is the cumulative size up to block `l`.
We use Mathlib's `Composition n` to represent ordered compositions.
-/

section RHS
/-- Degree function for the `l`-th block of a composition applied to `deg`. -/
def compositionBlockDeg
    {n : ℕ}
    (deg : Fin n → β_A)
    (c : Composition n)
    (l : Fin c.length) : Fin (c.blocksFun l) → β_A :=
  fun j => deg (c.embedding l j)
/-- The degree function for the outer `m^B` in the RHS: the `l`-th entry is
    the target degree of `φ_{iₗ}` applied to the `l`-th block. -/
def morphismRHSOuterDeg
    (F : AInfinityMorphismData R A B)
    {n : ℕ}
    (deg : Fin n → β_A)
    (c : Composition n) : Fin c.length → β_B :=
  fun l => morphismTargetDeg F.deg_trans (compositionBlockDeg deg c l)
/-
PROBLEM
Degree compatibility for the RHS: the target of `m^B_{c.length}` with the
    `φ` output degrees equals the morphism equation target degree.
PROVIDED SOLUTION
Unfold all definitions. The goal is:
(∑ l, ((∑ j, F.deg_trans (deg (c.embedding l j))) + shift_ofInt(1 - blocksFun l))) + shift_ofInt(2 - length) = (∑ i, F.deg_trans(deg i)) + shift_ofInt(2-n)
Split the LHS sum: ∑ l (sum_j + shift) = ∑ l sum_j + ∑ l shift.
For ∑ l ∑ j F.deg_trans(deg(c.embedding l j)) = ∑ i F.deg_trans(deg i): this follows because the embeddings c.embedding l partition Fin n. Use Composition.blocks_sum and properties of the embedding to reindex the double sum as a single sum over Fin n.
For ∑ l shift_ofInt(1 - blocksFun l) + shift_ofInt(2 - length): use the fact that ofInt is a group hom to combine, and ∑ l (1 - blocksFun l) = length - n (since ∑ blocksFun = n), so the total shift is ofInt(length - n + 2 - length) = ofInt(2 - n).
-/
lemma morphismRHS_deg_compat
    (F : AInfinityMorphismData R A B)
    {n : ℕ}
    (deg : Fin n → β_A)
    (c : Composition n) :
    operationTargetDeg (β := β_B) (morphismRHSOuterDeg F deg c) =
    morphismEqTargetDeg F.deg_trans deg := by
  -- By Lemma 2, we know that `∑ j, deg_trans(deg(c.embedding l j)) = ∑ i, deg_trans(deg i)` over all `l`.
  have h_sum_deg_trans : ∑ l : Fin c.length, ∑ j : Fin (c.blocksFun l), F.deg_trans (deg (c.embedding l j)) = ∑ i : Fin n, F.deg_trans (deg i) := by
    -- By definition of `c`, we know that the union of the images of the embeddings is exactly `Fin n`.
    have h_union : Finset.image (fun (p : Σ l : Fin c.length, Fin (c.blocksFun l)) => c.embedding p.fst p.snd) Finset.univ = Finset.univ := by
      ext i
      simp [Finset.mem_image];
      obtain ⟨l, hl⟩ : ∃ l : Fin c.length, i ∈ Finset.image (fun j => c.embedding l j) Finset.univ := by
        have h_partition : ∀ i : Fin n, ∃ l : Fin c.length, i ∈ Finset.image (fun j => c.embedding l j) Finset.univ := by
          intro i
          have h_exists_l : ∃ l : Fin c.length, i.val < c.sizeUpTo (l.val + 1) ∧ i.val ≥ c.sizeUpTo l.val := by
            have h_exists_l : ∃ l : ℕ, l ≤ c.length ∧ i.val < c.sizeUpTo l ∧ ∀ k : ℕ, k < l → i.val ≥ c.sizeUpTo k := by
              have h_exists_l : ∃ l : ℕ, l ≤ c.length ∧ i.val < c.sizeUpTo l := by
                use c.length;
                simp +decide [ Composition.sizeUpTo_length ];
              exact ⟨ Nat.find h_exists_l, Nat.find_spec h_exists_l |>.1, Nat.find_spec h_exists_l |>.2, fun k hk => not_lt.1 fun hk' => Nat.find_min h_exists_l hk ⟨ Nat.le_trans ( Nat.le_of_lt hk ) ( Nat.find_spec h_exists_l |>.1 ), hk' ⟩ ⟩;
            obtain ⟨ l, hl₁, hl₂, hl₃ ⟩ := h_exists_l;
            rcases l with ( _ | l ) <;> simp_all +decide;
            exact ⟨ ⟨ l, hl₁ ⟩, hl₂, hl₃ l le_rfl ⟩
          obtain ⟨ l, hl₁, hl₂ ⟩ := h_exists_l; use l; simp_all +decide [ Finset.mem_image, Finset.mem_univ ] ;
          have h_exists_a : ∃ a : Fin (c.blocksFun l), c.embedding l a = i := by
            have h_range : i.val - c.sizeUpTo l.val < c.blocksFun l := by
              rw [ tsub_lt_iff_left ] <;> try linarith! [ Fin.is_lt i ] ;
              convert hl₁ using 1 ; simp +decide [ Composition.sizeUpTo_succ ] ; ring!;
            use ⟨ i.val - c.sizeUpTo l.val, h_range ⟩ ; simp +decide [ Fin.ext_iff] ; omega;
          generalize_proofs at *; (
          exact h_exists_a);
        exact h_partition i;
      grind;
    have h_sum_eq : ∑ i : Fin n, F.deg_trans (deg i) = ∑ p : Σ l : Fin c.length, Fin (c.blocksFun l), F.deg_trans (deg (c.embedding p.fst p.snd)) := by
      conv_lhs => rw [ ← h_union, Finset.sum_image ( Finset.card_image_iff.mp <| by aesop ) ] ;
    rw [ h_sum_eq, Finset.sum_sigma' ];
    rfl;
  -- By Lemma 3, we know that `∑ l, (1 - blocksFun l) = length - n`.
  have h_sum_blocksFun : ∑ l : Fin c.length, (1 - (c.blocksFun l : ℤ)) = (c.length : ℤ) - n := by
    simp +decide;
    norm_cast ; aesop;
  -- Substitute the results from Lemma 2 and Lemma 3 into the expression for the sum of the target degrees.
  have h_sum_target_deg : ∑ l : Fin c.length, morphismTargetDeg F.deg_trans (compositionBlockDeg deg c l) = ∑ i : Fin n, F.deg_trans (deg i) + shift_ofInt (c.length - n : ℤ) := by
    -- Apply the linearity of the sum and the fact that the degree translation is a group homomorphism.
    have h_sum_target_deg : ∑ l : Fin c.length, morphismTargetDeg F.deg_trans (compositionBlockDeg deg c l) = (∑ l : Fin c.length, ∑ j : Fin (c.blocksFun l), F.deg_trans (deg (c.embedding l j))) + (∑ l : Fin c.length, shift_ofInt (1 - (c.blocksFun l : ℤ))) := by
      simp +decide only [morphismTargetDeg, sum_add_distrib];
      rfl;
    convert h_sum_target_deg using 2 ; aesop;
    rw [ ← h_sum_blocksFun ];
    exact map_sum ( Grading.ofInt ) _ _;
  convert congr_arg ( fun x : β_B => x + shift_ofInt ( 2 - ( c.length : ℤ ) ) ) h_sum_target_deg using 1;
  unfold morphismEqTargetDeg; simp +decide [ add_assoc ] ;
  unfold shift_ofInt; simp +decide ;
/-- The RHS term for a composition `c = (i₁, …, iₖ)`:
    `m^B_k(φ_{i₁}(block₁), …, φ_{iₖ}(blockₖ))`. -/
def morphismRHSTerm
    (F : AInfinityMorphismData R A B)
    (X_B : AInfinityAlgData (β := β_B) R B)
    (n : ℕ)
    (deg : Fin n → β_A)
    (x : ∀ i, A (deg i))
    (c : Composition n) :
    B (morphismEqTargetDeg F.deg_trans deg) := by
  -- Apply φ to each block
  let phiOutputDeg := morphismRHSOuterDeg F deg c
  let phiOutputs : ∀ l : Fin c.length, B (phiOutputDeg l) := fun l =>
    F.phi (c.blocksFun l)
      (compositionBlockDeg deg c l)
      (fun j => x (c.embedding l j))
  -- Apply m^B
  let outer := X_B.m c.length phiOutputDeg phiOutputs
  have hdeg := morphismRHS_deg_compat F deg c
  exact hdeg ▸ outer


def morphismRHSSum
    (F : AInfinityMorphismData R A B)
    (X_B : AInfinityAlgData (β := β_B) R B)
    (n : ℕ)
    (deg : Fin n → β_A)
    (x : ∀ i, A (deg i)) :
    B (morphismEqTargetDeg F.deg_trans deg) :=
  ∑ c : Composition n,
    F.morphismRHSTerm X_B n deg x c
end RHS

/-! ## The A∞-morphism equation -/
/-- The A∞-morphism equation as a property of the raw data:
    for every arity `n` and all input elements. -/
def satisfiesMorphismEquation
    (F : AInfinityMorphismData R A B)
    (X_A : AInfinityAlgData (β := β_A) R A)
    (X_B : AInfinityAlgData (β := β_B) R B) : Prop :=
  ∀ (n : ℕ) (deg : Fin n → β_A) (x : ∀ i, A (deg i)),
    F.morphismLHSSum X_A n deg x = F.morphismRHSSum X_B n deg x
end AInfinityMorphismData

/-! ## The A∞-morphism structure -/
/-- An A∞-morphism from `(A, X_A)` to `(B, X_B)` is raw morphism data
    satisfying the A∞-morphism equation. The two A∞-algebras are allowed
    to have different grading groups `β_A` and `β_B`; the group homomorphism
    `deg_trans : β_A →+ β_B` translates degrees. -/
structure AInfinityMorphism (R : Type u) [CommRing R]
    (A : GradedRModule (β := β_A) (R := R))
    (B : GradedRModule (β := β_B) (R := R))
    (X_A : AInfinityAlgData (β := β_A) R A)
    (X_B : AInfinityAlgData (β := β_B) R B)
    extends AInfinityMorphismData (β_A := β_A) (β_B := β_B) R A B where
  morphism_eq :
    AInfinityMorphismData.satisfiesMorphismEquation
      (β_A := β_A) (β_B := β_B) toAInfinityMorphismData X_A X_B
namespace AInfinityMorphism
variable {R : Type u} [CommRing R]
variable {A : GradedRModule (β := β_A) (R := R)}
variable {B : GradedRModule (β := β_B) (R := R)}
variable {X_A : AInfinityAlgData (β := β_A) R A}
variable {X_B : AInfinityAlgData (β := β_B) R B}
/-- Re-export the morphism equation in a convenient form. -/
lemma morphism_eq_holds
    (F : AInfinityMorphism (β_A := β_A) (β_B := β_B) R A B X_A X_B)
    (n : ℕ)
    (deg : Fin n → β_A)
    (x : ∀ i, A (deg i)) :
    F.toAInfinityMorphismData.morphismLHSSum X_A n deg x =
    F.toAInfinityMorphismData.morphismRHSSum X_B n deg x :=
  F.morphism_eq n deg x
end AInfinityMorphism
end AInfinityMorphismTheory
