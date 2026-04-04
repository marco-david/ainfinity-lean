import Mathlib
import Ainfinity.Grading
import Ainfinity.AInfinityAlgebra
open CategoryTheory Finset AInfinityCategoryTheory AInfinityAlgebraTheory AInfinityAlgData
noncomputable section
namespace AInfinityMorphismTheory
universe u v w
variable {β_A : Type v} [Grading β_A]
variable {β_B : Type w} [Grading β_B]

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
/- The LHS of the A∞-morphism equation is:
  `∑_{r+s+t=n, s≥1} (-1)^† φ_{r+1+t}(a_1, …, a_r, m^A_s(a_{r+1}, …, a_{r+s}), a_{r+s+1}, …, a_n)`
where `† = |a_{r+s+1}| + ⋯ + |a_n| − t` (the same sign as in the Stasheff relation).
Structurally this is the same as the Stasheff term, except the *outer* operation is `φ`
(mapping `A → B`) rather than `m^A` (mapping `A → A`).
-/
section LHS
--helper lemmas
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

--helper degree lemmas for the RHS
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


/-! ## Identity morphism -/
section Identity
variable {R : Type u} [CommRing R]
variable {β : Type v} [Grading β]
variable {A : GradedRModule (β := β) (R := R)}
variable {X_A : AInfinityAlgData (β := β) R A}

private lemma id_morphismTargetDeg_eq_one (deg : Fin 1 → β) :
    morphismTargetDeg (AddMonoidHom.id β) deg = deg 0 := by
      simp +decide [ morphismTargetDeg, shift_ofInt ]

/-- The identity A∞-morphism data on `A`.
    `φ_1 = id` and `φ_n = 0` for `n ≠ 1`. -/
def AInfinityMorphismData.idData
    (A : GradedRModule (β := β) (R := R)) :
    AInfinityMorphismData (β_A := β) (β_B := β) R A A where
  deg_trans := AddMonoidHom.id β
  deg_trans_ofInt n := by simp
  deg_trans_sign b := by simp
  phi n deg := by
    by_cases h : n = 1
    · subst h
      exact (id_morphismTargetDeg_eq_one deg) ▸ {
        toFun := fun x => x 0
        map_update_add' := fun m i p q => by
          have hi : i = 0 := Subsingleton.elim i 0
          subst hi; simp [Function.update_self]
        map_update_smul' := fun m i r p => by
          have hi : i = 0 := Subsingleton.elim i 0
          subst hi; simp [Function.update_self]
      }
    · exact 0

/-- The identity morphism data has `φ_n = 0` for `n ≠ 1`. -/
lemma AInfinityMorphismData.idData_phi_eq_zero
    (hn : n ≠ 1) (deg : Fin n → β) :
    (AInfinityMorphismData.idData A).phi n deg = 0 := by
  simp [AInfinityMorphismData.idData, hn]
  rfl

omit [Grading β] in
private lemma cast_zero_eq_zero {B : β → Type*} [∀ d, AddCommMonoid (B d)]
    {d₁ d₂ : β} (h : d₁ = d₂) :
    h ▸ (0 : B d₁) = (0 : B d₂) := by subst h; rfl
omit [Grading β] in
private lemma zero_phi_gives_zero_term {B : β → Type*}
    [∀ d, AddCommMonoid (B d)] [∀ d, Module R (B d)]
    {n : ℕ} {deg_in : Fin n → β} {A : β → Type*}
    [∀ d, AddCommMonoid (A d)] [∀ d, Module R (A d)]
    {d₁ d₂ : β} (h : d₁ = d₂)
    (x : ∀ i, A (deg_in i)) :
    h ▸ ((0 : MultilinearMap R (fun i => A (deg_in i)) (B d₁)) x) = (0 : B d₂) := by
  subst h; simp
/-
PROBLEM
The LHS summand is zero when the outer arity `n+1-s` is not 1.
PROVIDED SOLUTION
Unfold morphismLHSSummand. If the indices are invalid (¬validStasheffIndices), it's already 0. If valid, unfold morphismLHSTerm. The term applies (idData A).phi (n+1-s) as the outer map. Since n+1-s ≠ 1, by idData_phi_eq_zero this phi is the zero multilinear map. Applying the zero multilinear map to anything gives 0, and casting 0 gives 0.
-/
private lemma idData_morphismLHSSummand_eq_zero
    (X : AInfinityAlgData (β := β) R A)
    {n : ℕ} (deg : Fin n → β) (x : ∀ i, A (deg i))
    (r s : ℕ) (hne : n + 1 - s ≠ 1) :
    (AInfinityMorphismData.idData A).morphismLHSSummand X n deg x r s = 0 := by
      unfold AInfinityMorphismData.morphismLHSSummand AInfinityMorphismData.morphismLHSTerm at *; simp_all +decide ;
      intro hp hq;
      have h_zero : (AInfinityMorphismData.idData A).phi (n + 1 - s) (stasheffDegOut deg r s (by omega)) = 0 := by
        grind +locals;
      have h_zero_term : ∀ (x : ∀ i : Fin (n + 1 - s), A (stasheffDegOut deg r s hq i)), (AInfinityMorphismData.idData A).phi (n + 1 - s) (stasheffDegOut deg r s hq) x = 0 := by
        aesop;
      grind
/-
PROBLEM
The RHS term is zero for a composition where some block has size ≠ 1.
PROVIDED SOLUTION
Unfold morphismRHSTerm. The term applies X.m c.length to the phi outputs:
phiOutputs l = (idData A).phi (c.blocksFun l) (compositionBlockDeg deg c l) (fun j => x (c.embedding l j))
By hypothesis, there exists l₀ such that c.blocksFun l₀ ≠ 1. By idData_phi_eq_zero, (idData A).phi (c.blocksFun l₀) = 0. So phiOutputs l₀ = 0 (zero multilinear map applied). Then X.m c.length applied to phiOutputs is zero because one coordinate (l₀) is zero and multilinear maps vanish when any coordinate is zero (MultilinearMap.map_coord_zero). Then the cast (hdeg ▸ ...) preserves zero.
-/
private lemma idData_morphismRHSTerm_eq_zero
    (X : AInfinityAlgData (β := β) R A)
    {n : ℕ} (deg : Fin n → β) (x : ∀ i, A (deg i))
    (c : Composition n) (hc : ∃ l : Fin c.length, c.blocksFun l ≠ 1) :
    (AInfinityMorphismData.idData A).morphismRHSTerm X n deg x c = 0 := by
      unfold AInfinityMorphismData.morphismRHSTerm;
      obtain ⟨l, hl⟩ := hc
      have h_phi_zero : (AInfinityMorphismData.idData A).phi (c.blocksFun l) (AInfinityMorphismData.compositionBlockDeg deg c l) = 0 := by
        exact
          AInfinityMorphismData.idData_phi_eq_zero hl
            (AInfinityMorphismData.compositionBlockDeg deg c l);
      -- Since `phiOutputs l = 0`, the entire term `X.m c.length phiOutputDeg phiOutputs` is zero by the properties of multilinear maps.
      have h_term_zero : ∀ (l : Fin c.length), (AInfinityMorphismData.idData A).phi (c.blocksFun l) (AInfinityMorphismData.compositionBlockDeg deg c l) = 0 → X.m c.length (AInfinityMorphismData.morphismRHSOuterDeg (AInfinityMorphismData.idData A) deg c) (fun l => (AInfinityMorphismData.idData A).phi (c.blocksFun l) (AInfinityMorphismData.compositionBlockDeg deg c l) (fun j => x (c.embedding l j))) = 0 := by
        intro l hl; exact (by
        exact MultilinearMap.map_coord_zero _ l ( by aesop ));
      grind
/-
PROBLEM
When n = 0, the LHS is 0.
PROVIDED SOLUTION
morphismLHSSum sums over r ∈ range 1 and s ∈ Ico 1 (0-r+1). For r=0, Ico 1 (0-0+1) = Ico 1 1 = ∅. So the sum is 0.
-/
private lemma idData_morphismLHSSum_zero
    (X : AInfinityAlgData (β := β) R A)
    (deg : Fin 0 → β) (x : ∀ i, A (deg i)) :
    (AInfinityMorphismData.idData A).morphismLHSSum X 0 deg x = 0 := by
      unfold AInfinityMorphismData.morphismLHSSum; simp +decide [ AInfinityMorphismData.morphismLHSTerm, AInfinityMorphismData.morphismLHSSummand ] ;
/-
PROBLEM
When n = 0, the RHS is 0 (assuming m₀ = 0).
PROVIDED SOLUTION
morphismRHSSum sums over Composition 0. There's exactly one composition of 0: the empty composition with blocks = []. So the sum has one term: morphismRHSTerm for this composition.
morphismRHSTerm unfolds to: let outer = X.m 0 phiOutputDeg phiOutputs; cast ▸ outer. Since X.m 0 is the zero multilinear map (by hm0), outer = 0, and cast of 0 is 0.
Key: use hm0 to show X.m 0 (applied to any deg) is the zero map, hence its application to any input is 0. Then the cast (▸) of 0 is 0.
-/
private lemma idData_morphismRHSSum_zero
    (X : AInfinityAlgData (β := β) R A)
    (hm0 : ∀ (d : Fin 0 → β), X.m 0 d = 0)
    (deg : Fin 0 → β) (x : ∀ i, A (deg i)) :
    (AInfinityMorphismData.idData A).morphismRHSSum X 0 deg x = 0 := by
      unfold AInfinityMorphismData.morphismRHSSum;
      convert hm0 _;
      convert Iff.rfl;
      swap;
      exact fun a ↦ Classical.ofNonempty;
      unfold AInfinityMorphismData.morphismRHSTerm;
      rw [ Finset.sum_eq_single ( Composition.mk [ ] ( by simp +decide ) ( by simp +decide ) ) ] <;> simp +decide [ hm0 ];
      · exact hm0 _ ▸ rfl;
      · rintro ⟨ ⟩; simp +decide
        grind +suggestions
/-
PROBLEM
The stasheff sign for (r=0, s=n) is 1.
PROVIDED SOLUTION
stasheffSign deg 0 n = if 0 + n ≤ n then (-1)^(stasheffSignParity deg 0 n (le_refl n)).val else 1.
Since 0 + n ≤ n, we use the first branch.
stasheffSignParity deg 0 n = (∑ i : Fin (n-0-n), ...) - (n-0-n : ℕ) = (∑ i : Fin 0, ...) - 0 = 0 - 0 = 0.
So stasheffSign = (-1)^0 = 1.
-/
private lemma idData_stasheffSign_zero_n
    {n : ℕ} (hn : n ≠ 0) (deg : Fin n → β) :
    stasheffSign deg 0 n = 1 := by
      unfold stasheffSign stasheffSignParity; norm_num;
      erw [ Finset.sum_eq_zero ] <;> simp +decide;
      exact fun x => False.elim <| hn <| by linarith [ Fin.is_lt x, Nat.sub_add_cancel <| show n ≥ n from le_rfl ] ;
/-
PROBLEM
When n ≥ 1, the LHS has only one nonzero term: (r, s) = (0, n).
PROVIDED SOLUTION
morphismLHSSum = ∑ r ∈ range(n+1), ∑ s ∈ Ico 1 (n-r+1), sign * summand.
By idData_morphismLHSSummand_eq_zero, the summand is 0 whenever n+1-s ≠ 1. So the only possible nonzero term has n+1-s = 1, i.e., s = n. For s = n to be in Ico 1 (n-r+1), we need 1 ≤ n and n < n-r+1, i.e., r < 1, so r = 0.
So the double sum collapses to a single term at (r, s) = (0, n).
Strategy:
1. Use Finset.sum_eq_single 0 for the outer sum (r = 0), showing all other r give 0 inner sums
2. For the inner sum at r = 0, use Finset.sum_eq_single n, showing s ≠ n gives 0 (by idData_morphismLHSSummand_eq_zero since n+1-s ≠ 1)
3. Use idData_stasheffSign_zero_n to show sign = 1, giving 1 • summand = summand
-/
private lemma idData_morphismLHSSum_single
    (X : AInfinityAlgData (β := β) R A)
    {n : ℕ} (hn : n ≠ 0) (deg : Fin n → β) (x : ∀ i, A (deg i)) :
    (AInfinityMorphismData.idData A).morphismLHSSum X n deg x =
    (AInfinityMorphismData.idData A).morphismLHSSummand X n deg x 0 n := by
      convert Finset.sum_eq_single 0 _ _ using 2 <;> simp +decide [ *];
      · rw [ Finset.sum_eq_single n ] <;> simp_all +decide [ AInfinityMorphismData.morphismLHSSummand ];
        · rw [ idData_stasheffSign_zero_n hn ] ; simp +decide [ validStasheffIndices ] ;
        · intro b hb₁ hb₂ hb₃; rw [ show ( AInfinityMorphismData.idData A ).morphismLHSTerm X n deg x 0 b ( by linarith ) ( by linarith ) = 0 from ?_ ] ; simp +decide ;
          convert idData_morphismLHSSummand_eq_zero X deg x 0 b _ using 1;
          · unfold AInfinityMorphismData.morphismLHSSummand; aesop;
          · omega;
      · intro b hb hb';
        convert Finset.sum_eq_zero _ using 2 ; intros ; simp_all +decide ; (
        rw [ idData_morphismLHSSummand_eq_zero ] <;> norm_num
        generalize_proofs at *; (
        omega;));
/-
PROBLEM
A composition where all blocks are 1 is Composition.ones.
PROVIDED SOLUTION
If all blocks of composition c equal 1, then c.blocks = List.replicate c.length 1. Since c is a Composition n and ∑ c.blocks = n, and each block is 1, we have c.length = n. Moreover, c.blocks = List.replicate n 1, which is exactly the definition of Composition.ones n. Use Composition.ext or show blocks equality. The key insight: c.blocks = List.replicate c.length 1 follows from the hypothesis that blocksFun l = 1 for all l, combined with List.ext showing each element is 1. And c.length * 1 = n since sum of all-ones list of length c.length equals c.length = n.
-/
private lemma composition_all_ones_eq_ones
    {n : ℕ} (c : Composition n)
    (h : ∀ l : Fin c.length, c.blocksFun l = 1) :
    c = Composition.ones n := by
      have h_blocks_eq : c.blocks = List.map (fun l : Fin c.length => 1) (List.finRange c.length) := by
        refine' List.ext_get _ _ <;> aesop;
      have h_length : c.length = n := by
        have := c.blocks_sum; aesop;
      aesop
/-
PROBLEM
When n ≥ 1, the RHS has only one nonzero term: c = Composition.ones n.
PROVIDED SOLUTION
morphismRHSSum = ∑ c : Composition n, morphismRHSTerm c.
By idData_morphismRHSTerm_eq_zero, the term is 0 whenever ∃ l, c.blocksFun l ≠ 1.
The only composition where all blocks equal 1 is Composition.ones n (by composition_all_ones_eq_ones). Since n ≠ 0, Composition.ones n exists and has length n.
Use Finset.sum_eq_single (Composition.ones n):
- For c ≠ ones n: there exists l with c.blocksFun l ≠ 1 (since if all were 1, c = ones n), so the term is 0
- The element (ones n) is in Finset.univ
-/
private lemma idData_morphismRHSSum_single
    (X : AInfinityAlgData (β := β) R A)
    {n : ℕ}  (deg : Fin n → β) (x : ∀ i, A (deg i)) :
    (AInfinityMorphismData.idData A).morphismRHSSum X n deg x =
    (AInfinityMorphismData.idData A).morphismRHSTerm X n deg x (Composition.ones n) := by
      convert Finset.sum_eq_single ( Composition.ones n ) _ _ <;> simp +decide ;
      exact fun c hc => idData_morphismRHSTerm_eq_zero X deg x c <| by contrapose! hc; exact composition_all_ones_eq_ones c hc;
/-
PROBLEM
The degree of operationTargetDeg equals morphismEqTargetDeg for the identity.
PROVIDED SOLUTION
Both sides unfold to the same thing: operationTargetDeg deg = (∑ i, deg i) + shift_ofInt (2 - n), and morphismEqTargetDeg (AddMonoidHom.id β) deg = (∑ i, (AddMonoidHom.id β (deg i))) + shift_ofInt (2 - n) = (∑ i, deg i) + shift_ofInt (2 - n). So they're definitionally equal after simp with AddMonoidHom.id_apply.
-/
private lemma id_operationTargetDeg_eq_morphismEqTargetDeg
    (deg : Fin n → β) :
    operationTargetDeg deg = morphismEqTargetDeg (AddMonoidHom.id β) deg := by
      unfold operationTargetDeg morphismEqTargetDeg; simp +decide;
/-- The common value: X.m n deg x cast to the equation target degree. -/
private def idData_common_value
    (X : AInfinityAlgData (β := β) R A)
    {n : ℕ} (deg : Fin n → β) (x : ∀ i, A (deg i)) :
    A (morphismEqTargetDeg (AddMonoidHom.id β) deg) :=
  (id_operationTargetDeg_eq_morphismEqTargetDeg deg) ▸ X.m n deg x


omit [Grading β] in
private lemma cast_multilinear_apply
    {M : Fin k → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    {N : β → Type*} [∀ d, AddCommMonoid (N d)] [∀ d, Module R (N d)]
    {d₁ d₂ : β} (h : d₁ = d₂)
    (f : MultilinearMap R M (N d₁)) (y : ∀ i, M i) :
    (h ▸ f) y = h ▸ (f y) := by subst h; rfl
omit [Grading β] in
private lemma cast_cast
    {N : β → Type*}
    {d₁ d₂ d₃ : β} (h₁ : d₁ = d₂) (h₂ : d₂ = d₃)
    (v : N d₁) :
    h₂ ▸ (h₁ ▸ v) = (h₁.trans h₂) ▸ v := by subst h₁; subst h₂; rfl
omit [Grading β] in
private lemma cast_proof_irrel
    {N : β → Type*}
    {d₁ d₂ : β} (h₁ h₂ : d₁ = d₂)
    (v : N d₁) :
    h₁ ▸ v = h₂ ▸ v := by rfl

/-- `idData.phi 1` applied to inputs equals the first input cast to the target degree. -/
private lemma idData_phi_one_apply
    (deg : Fin 1 → β) (y : ∀ i : Fin 1, A (deg i)) :
    (AInfinityMorphismData.idData A).phi 1 deg y =
    (id_morphismTargetDeg_eq_one deg) ▸ y 0 := by
  unfold AInfinityMorphismData.idData
  simp only
  sorry

omit [Grading β] in
private lemma stasheffDegIn_zero_n_eq
    {n : ℕ} (deg : Fin n → β) (hr : 0 + n ≤ n) :
    stasheffDegIn deg 0 n hr = fun i => deg ⟨i.val, by omega⟩ := by
  funext i; simp [stasheffDegIn]
/-- For the Composition.ones, embedding l 0 gives l (reindexed). -/
private lemma ones_embedding_zero
    {n : ℕ} (l : Fin (Composition.ones n).length) :
    (Composition.ones n).embedding l ⟨0, by simp [Composition.ones, Composition.blocksFun]⟩ =
    ⟨l.val, by have := l.isLt; simp [Composition.ones, Composition.length] at this; exact this⟩ := by
  simp only [Composition.embedding, Composition.ones, Composition.sizeUpTo,
    Composition.blocksFun, Fin.ext_iff, Fin.natAdd, Fin.castLE]
  simp [List.take_replicate, List.sum_replicate]
  have := l.isLt; simp [Composition.ones, Composition.length] at this
  sorry --omega

/-- The surviving LHS and RHS terms are equal. -/
private lemma idData_surviving_terms_eq
    (X : AInfinityAlgData (β := β) R A)
    {n : ℕ} (hn : n ≠ 0) (deg : Fin n → β) (x : ∀ i, A (deg i)) :
    (AInfinityMorphismData.idData A).morphismLHSSummand X n deg x 0 n =
    (AInfinityMorphismData.idData A).morphismRHSTerm X n deg x (Composition.ones n) := by sorry
/-- The LHS equals the RHS for the identity morphism data
    (assuming the algebra is non-curved, i.e., m₀ = 0). -/
private lemma idData_morphismLHSSum_eq
    (X : AInfinityAlgData (β := β) R A)
    (hm0 : ∀ (d : Fin 0 → β), X.m 0 d = 0)
    {n : ℕ} (deg : Fin n → β) (x : ∀ i, A (deg i)) :
    (AInfinityMorphismData.idData A).morphismLHSSum X n deg x =
    (AInfinityMorphismData.idData A).morphismRHSSum X n deg x := by
  by_cases hn : n = 0
  · subst hn; rw [idData_morphismLHSSum_zero, idData_morphismRHSSum_zero X hm0]
  · rw [idData_morphismLHSSum_single X hn, idData_morphismRHSSum_single X,
         idData_surviving_terms_eq X hn]
/-- The identity morphism satisfies the A∞-morphism equation,
    assuming the algebra is non-curved (m₀ = 0).
    This hypothesis is needed because `Composition 0` in Mathlib includes
    the empty composition (length 0), creating a spurious RHS term for `n = 0`
    that equals `m₀` applied to empty inputs. In the standard A∞ literature,
    the RHS sum ranges over compositions with at least one part (`k ≥ 1`),
    making the `n = 0` case trivially `0 = 0`. -/
theorem AInfinityMorphismData.idData_satisfies_morphism_eq
    (X : AInfinityAlgData (β := β) R A)
    (hm0 : ∀ (d : Fin 0 → β), X.m 0 d = 0) :
    (AInfinityMorphismData.idData A).satisfiesMorphismEquation X X :=
  fun n deg x => idData_morphismLHSSum_eq X hm0 deg x
/-- The identity A∞-morphism on `(A, X)`,
    assuming the algebra is non-curved (m₀ = 0). -/
def AInfinityMorphism.id
    (X : AInfinityAlgData (β := β) R A)
    (hm0 : ∀ (d : Fin 0 → β), X.m 0 d = 0) :
    AInfinityMorphism (β_A := β) (β_B := β) R A A X X where
  toAInfinityMorphismData := AInfinityMorphismData.idData A
  morphism_eq := AInfinityMorphismData.idData_satisfies_morphism_eq X hm0
end Identity


end AInfinityMorphismTheory

/-

but need to PROVE that if they are actually Ainf morphisms, then comp is also one

prove composition is associative
define identity moprhism
composition with identity is the same thing


prove lemma 3.6
 -/
