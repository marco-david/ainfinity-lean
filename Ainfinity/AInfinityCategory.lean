module

public import Mathlib
public import Ainfinity.Grading

open CategoryTheory Finset AInfinityAlgebraTheory

noncomputable section

namespace AInfinityCategoryTheory

universe u v w
variable {β : Type v} [Grading β]

abbrev GradedRModule (R : Type u) [CommRing R] :=
  GradedObject β (ModuleCat.{u} R)

/-- Target degree of the `n`-ary operation `m`. -/
abbrev operationTargetDeg
    (deg : Fin n → β) : β :=
  (∑ i, deg i) + shift_ofInt (2 - (n : ℤ))



-- ============================================================
-- Layer 1: just Obj and Hom
-- ============================================================

structure AInfinityCategoryData (R : Type u) [CommRing R] where
  Obj : Type w
  Hom : Obj → Obj → GradedRModule (β := β) (R := R)

-- ============================================================
-- Layer 2: Chain
-- ============================================================

namespace AInfinityCategoryData

variable {R : Type u} [CommRing R]

structure Chain (C : AInfinityCategoryData (β := β) R) where
  n   : ℕ+
  obj : Fin (n + 1) → C.Obj
  deg : Fin n → β

namespace Chain

variable {C : AInfinityCategoryData (β := β) R}

def source (ch : C.Chain) : C.Obj := ch.obj 0

def target (ch : C.Chain) : C.Obj := ch.obj (Fin.last ch.n)

def operationTarget (ch : C.Chain) : ModuleCat R :=
  C.Hom ch.source ch.target (operationTargetDeg ch.deg)

def link (ch : C.Chain) (i : Fin ch.n) : ModuleCat R :=
  C.Hom (ch.obj (Fin.castSucc i)) (ch.obj ((Fin.castSucc i) + 1)) (ch.deg i)

end Chain

end AInfinityCategoryData

-- ============================================================
-- Layer 3: AInfinityCategory with m
-- ============================================================

structure AInfinityPreCategory (R : Type u) [CommRing R]
    extends AInfinityCategoryData (β := β) R where
  m : (ch : toAInfinityCategoryData.Chain) →
      MultilinearMap R
        (fun i : Fin ch.n => ch.link i)
        ch.operationTarget





namespace AInfinityPreCategory

variable {R : Type u} [CommRing R]

section Internal

abbrev validStasheffIndices (n r s : ℕ) : Prop :=
  1 ≤ s ∧ r + s ≤ n

/-- Target degree of the arity-`n` Stasheff relation. -/
abbrev stasheffTargetDeg
    (deg : Fin n → β) : β :=
  (∑ i, deg i) + shift_ofInt (3 - (n : ℤ))


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
            unfold stasheffDegIn; ring;
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
  {β : Type v} [Grading β]
  {R : Type u} [CommRing R]
  (X : AInfinityPreCategory (β := β) R)
  (ch : X.Chain)
  (x : ∀ i : Fin ch.n, ch.link i)
  (r s : ℕ)
  (hs : 1 ≤ s)
  (hr : r + s ≤ ch.n) :
  X.Hom ch.source ch.target (stasheffTargetDeg ch.deg):=
by
  let degIn := stasheffDegIn ch.deg r s hr
  let objIn : Fin (s+1) → X.Obj := fun i => ch.obj ⟨r + i.val, by omega⟩
  let innerch : X.Chain := ⟨⟨s, hs⟩, objIn, degIn⟩



  have test (i : Fin innerch.n) : r + i.val < ch.n := by
    exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt r) hr
  have test2 (i : Fin innerch.n) : innerch.link i = ch.link ⟨r + i.val, test i⟩ := by
    unfold AInfinityCategoryData.Chain.link;
    simp +zetaDelta at *;
    congr!;
    norm_num [ Fin.val_add ];
    rw [ Nat.mod_eq_of_lt ( by linarith [ Fin.is_lt i, show ( i : ℕ ) < s from i.2 ] ) ]
    ring_nf
    sorry





  let xIn : ∀ i : Fin innerch.n, innerch.link i := fun i => by
    rw [test2 i]
    exact x ⟨r + i.val, test i⟩

  let inner := X.m innerch xIn
  let outerN := ch.n + 1 - s
  let degOut := stasheffDegOut ch.deg r s hr

  let objOut : Fin (outerN+1) → X.Obj := fun i =>
    if h1 : i.val ≤ r then
      ch.obj ⟨i.val, by omega⟩
    else if _ : i.val = r+1 then
      ch.obj ⟨r+s, by omega⟩
    else
      ch.obj ⟨i.val + s - 1, by omega⟩

  let outerch : X.Chain := ⟨⟨outerN, by omega⟩, objOut, degOut⟩


  have xOut_link_lt (i : Fin outerN) (h1 : i.val < r) :
      outerch.link i = ch.link ⟨i.val, by omega⟩ := by
        sorry


  have xOut_link_eq (i : Fin outerN) (h2 : i.val = r) :
      outerch.link i = innerch.operationTarget := by
        simp +zetaDelta at *;
        unfold AInfinityCategoryData.Chain.link AInfinityCategoryData.Chain.operationTarget;
        all_goals norm_num [ h2, operationTargetDeg, stasheffInnerDeg, stasheffDegOut ];
        all_goals norm_cast
  have xOut_link_gt (i : Fin outerN) (h1 : ¬ i.val < r) (h2 : ¬ i.val = r) :
      outerch.link i = ch.link ⟨i.val + s - 1, by omega⟩ := by
        simp +decide [ AInfinityCategoryData.Chain.link ];
        congr! 1;
        all_goals norm_num [ outerch, objOut, degOut ];
        any_goals split_ifs ; omega;
        any_goals congr! 1;
        all_goals norm_num [ Fin.ext_iff, Fin.val_add ] at *;
        any_goals rw [ Nat.sub_add_cancel ( by linarith ) ] ; rw [ Nat.mod_eq_of_lt ] ; omega;
        any_goals rw [ stasheffDegOut ] ; simp +decide [*];
        omega

  /-
  xOut i
  if i < r: return x i
  if i = r: return inner
  if i > r return x (i + s -1)
   -/
  let xOut : ∀ i : Fin outerN, outerch.link i := fun i => by
    by_cases h1 : i.val < r
    · exact (xOut_link_lt i h1) ▸ x ⟨i.val, by omega⟩
    · by_cases h2 : i.val = r
      · exact (xOut_link_eq i h2) ▸ inner
      · exact (xOut_link_gt i h1 h2) ▸ x ⟨i.val + s - 1, by omega⟩

  let outer := X.m outerch xOut
  have hdeg : outerch.operationTarget = X.Hom ch.source ch.target (stasheffTargetDeg ch.deg) := by
    convert congr_arg _ ( stasheffDegOut_sum ch.deg r s hr ) using 1;
    congr! 1;
    simp +decide [ AInfinityCategoryData.Chain.target ];
    simp +decide [ outerch, Fin.last ];
    grind
  exact hdeg ▸ outer

end AInfinityPreCategory

end AInfinityCategoryTheory
