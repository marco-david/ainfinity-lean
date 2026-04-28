module

public import Mathlib
public import AInfinity.Grading
public import AInfinity.AInfinityCategory

@[expose] public section

open CategoryTheory AInfinityTheory

noncomputable section

namespace AInfinityTheory

universe u v w x y
variable (β_A : Type v) [Grading β_A]
variable (β_B : Type w) [Grading β_B]

/-- Target degree of `φ_n` applied to inputs of the given degrees.
    `φ_n` has degree `1 − n`, so the output lives in
    `∑ i, deg_trans(deg i) + ofInt(1 − n)` in `β_B`. -/
abbrev functorTargetDeg
    (deg_trans : β_A →+ β_B)
    {n : ℕ} (deg : Fin n → β_A) : β_B :=
  (∑ i, deg_trans (deg i)) + shift_ofInt (1 - (n : ℤ))

/-- Target module of `φ_n` for a chain of objects and input degrees. -/
abbrev functorTargetType
    {R : Type u} [CommRing R]
    {ObjA : Type x} {ObjB : Type y}
    (BHom : ObjB → ObjB → GradedRModule β_B R)
    (objMap : ObjA → ObjB)
    (deg_trans : β_A →+ β_B)
    {n : ℕ}
    (obj : Fin (n + 1) → ObjA)
    (deg : Fin n → β_A) :
    ModuleCat R :=
  (BHom (objMap (obj 0)) (objMap (obj (Fin.last n))))
    (functorTargetDeg β_A β_B deg_trans deg)

/-- Raw data for an A∞ functor between graded `R`-linear quivers. -/
structure AInfinityFunctorData
    (R : Type u) [CommRing R]
    (ObjA : Type x) (ObjB : Type y)
    [RLinearGQuiver β_A R ObjA]
    [RLinearGQuiver β_B R ObjB] where
  /-- The action on objects. -/
  objMap : ObjA → ObjB
  /-- Group homofunctor translating degrees from `β_A` to `β_B`. -/
  deg_trans : β_A →+ β_B
  /-- `deg_trans` is compatible with the integer embeddings. -/
  deg_trans_ofInt : ∀ n : ℤ, deg_trans (Grading.ofInt n) = Grading.ofInt n
  /-- `deg_trans` preserves sign/parity. -/
  deg_trans_sign : ∀ b : β_A, Grading.sign (deg_trans b) = Grading.sign b

  phi :
    {n : ℕ} → [NeZero n] →
    (obj : Fin (n + 1) → ObjA) →
    (deg : Fin n → β_A) →
    MultilinearMap R
      (fun i : Fin n => ComposableHomType (GHom β_A R) obj deg i)
      (functorTargetType β_A β_B (GHom β_B R) objMap deg_trans obj deg)



namespace AInfinityFunctorData

section CompComposition
universe u₁
variable {R : Type u₁} [CommSemiring R]

lemma Composition.embedding_ne_of_ne
    {n : ℕ} (c : Composition n)
    {l l₀ : Fin c.length} (hl : l ≠ l₀)
    (j : Fin (c.blocksFun l)) (j₀ : Fin (c.blocksFun l₀)) :
    (c.embedding l) j ≠ (c.embedding l₀) j₀ := by
  have h_range : Disjoint (Set.range (c.embedding l)) (Set.range (c.embedding l₀)) := by
    exact c.disjoint_range hl
  exact fun h => h_range.le_bot ⟨⟨j, h⟩, ⟨j₀, rfl⟩⟩

lemma Composition.update_comp_ne_block
    {n : ℕ} (c : Composition n)
    {M : Fin n → Type*} [DecidableEq (Fin n)] (m : ∀ i, M i)
    {l₀ : Fin c.length} (j₀ : Fin (c.blocksFun l₀))
    (v : M (c.embedding l₀ j₀))
    {l : Fin c.length} (hl : l ≠ l₀) :
    (fun j => Function.update m (c.embedding l₀ j₀) v (c.embedding l j)) =
      (fun j => m (c.embedding l j)) := by
  exact funext fun j =>
    Function.update_of_ne
      (by
        intro h
        have := Composition.embedding_ne_of_ne c hl j j₀
        aesop)
      _ _

lemma Composition.update_comp_same_block
    {n : ℕ} (c : Composition n)
    {M : Fin n → Type*} [DecidableEq (Fin n)] (m : ∀ i, M i)
    (l₀ : Fin c.length) (j₀ : Fin (c.blocksFun l₀))
    (v : M (c.embedding l₀ j₀)) :
    (fun j => Function.update m (c.embedding l₀ j₀) v (c.embedding l₀ j)) =
      Function.update (fun j => m (c.embedding l₀ j)) j₀ v := by
  ext j
  by_cases h : c.embedding l₀ j = c.embedding l₀ j₀
  · simp +decide [h, Function.update]
    have := (c.embedding l₀).injective h
    aesop
  · aesop

lemma Composition.compComposition_outer_update
    {n : ℕ} (c : Composition n)
    {M : Fin n → Type*} {N : Fin c.length → Type*}
    [∀ i, AddCommMonoid (M i)] [∀ l, AddCommMonoid (N l)]
    [∀ i, Module R (M i)] [∀ l, Module R (N l)]
    [DecidableEq (Fin n)]
    (f : (l : Fin c.length) → MultilinearMap R (fun j => M (c.embedding l j)) (N l))
    (m : ∀ i, M i) (l₀ : Fin c.length) (j₀ : Fin (c.blocksFun l₀))
    (v : M (c.embedding l₀ j₀)) :
    (fun l => f l (fun j => Function.update m (c.embedding l₀ j₀) v (c.embedding l j))) =
    Function.update
      (fun l => f l (fun j => m (c.embedding l j)))
      l₀
      (f l₀ (Function.update (fun j => m (c.embedding l₀ j)) j₀ v)) := by
  ext l
  by_cases hl : l = l₀
  · have := Composition.update_comp_same_block c m l₀ j₀ v
    aesop
  · rw [Function.update_of_ne hl]
    have := Composition.update_comp_ne_block c m j₀ v hl
    rw [this]

/-- Multi-composition of multilinear maps along a composition `c` of `n`. -/
def MultilinearMap.compComposition
    {n : ℕ} (c : Composition n)
    {M : Fin n → Type*} {N : Fin c.length → Type*} {P : Type*}
    [∀ i, AddCommMonoid (M i)] [∀ l, AddCommMonoid (N l)] [AddCommMonoid P]
    [∀ i, Module R (M i)] [∀ l, Module R (N l)] [Module R P]
    (g : MultilinearMap R N P)
    (f : (l : Fin c.length) → MultilinearMap R (fun j => M (c.embedding l j)) (N l)) :
    MultilinearMap R M P where
  toFun x := g (fun l => f l (fun j => x (c.embedding l j)))
  map_update_add' m i p q := by
    obtain ⟨l₀, j₀, rfl⟩ : ∃ l : Fin c.length, ∃ j : Fin (c.blocksFun l),
        c.embedding l j = i :=
      ⟨c.index i, c.invEmbedding i, c.embedding_comp_inv i⟩
    have h := Composition.compComposition_outer_update c f m l₀ j₀
    have lhs : g (fun l => f l (fun j => Function.update m _ (p + q) (c.embedding l j)))
      = g (Function.update (fun l => f l (fun j => m (c.embedding l j))) l₀
          (f l₀ (Function.update (fun j => m (c.embedding l₀ j)) j₀ (p + q)))) := by
      congr 1
      exact h (p + q)
    have rhs₁ : g (fun l => f l (fun j => Function.update m _ p (c.embedding l j)))
      = g (Function.update (fun l => f l (fun j => m (c.embedding l j))) l₀
          (f l₀ (Function.update (fun j => m (c.embedding l₀ j)) j₀ p))) := by
      congr 1
      exact h p
    have rhs₂ : g (fun l => f l (fun j => Function.update m _ q (c.embedding l j)))
      = g (Function.update (fun l => f l (fun j => m (c.embedding l j))) l₀
          (f l₀ (Function.update (fun j => m (c.embedding l₀ j)) j₀ q))) := by
      congr 1
      exact h q
    rw [lhs, rhs₁, rhs₂, (f l₀).map_update_add, g.map_update_add]
  map_update_smul' m i a p := by
    obtain ⟨l₀, j₀, rfl⟩ : ∃ l : Fin c.length, ∃ j : Fin (c.blocksFun l),
        c.embedding l j = i :=
      ⟨c.index i, c.invEmbedding i, c.embedding_comp_inv i⟩
    have h := Composition.compComposition_outer_update c f m l₀ j₀
    have lhs : g (fun l => f l (fun j => Function.update m _ (a • p) (c.embedding l j)))
      = g (Function.update (fun l => f l (fun j => m (c.embedding l j))) l₀
          (f l₀ (Function.update (fun j => m (c.embedding l₀ j)) j₀ (a • p)))) := by
      congr 1
      exact h (a • p)
    have rhs : g (fun l => f l (fun j => Function.update m _ p (c.embedding l j)))
      = g (Function.update (fun l => f l (fun j => m (c.embedding l j))) l₀
          (f l₀ (Function.update (fun j => m (c.embedding l₀ j)) j₀ p))) := by
      congr 1
      exact h p
    rw [lhs, rhs, (f l₀).map_update_smul, g.map_update_smul]
end CompComposition

variable {R : Type u} [CommRing R]
variable {ObjA : Type x} {ObjB : Type y}

/-- Target degree of the functor equation.
    Both sides of the A∞-functor equation land in
    `∑ i, deg_trans(deg i) + ofInt(2 − n)` in `β_B`. -/
abbrev functorEqTargetDeg
    (deg_trans : β_A →+ β_B)
    {n : ℕ} (deg : Fin n → β_A) : β_B :=
  (∑ i, deg_trans (deg i)) + shift_ofInt (2 - (n : ℤ))

abbrev functorEqTargetType
    {R : Type u} [CommRing R]
    {ObjA : Type x} {ObjB : Type y}
    (BHom : ObjB → ObjB → GradedRModule (β := β_B) (R := R))
    (objMap : ObjA → ObjB)
    (deg_trans : β_A →+ β_B)
    {n : ℕ}
    (obj : Fin (n + 1) → ObjA)
    (deg : Fin n → β_A) :
    ModuleCat R :=
  (BHom (objMap (obj 0)) (objMap (obj (Fin.last n))))
    (functorEqTargetDeg β_A β_B deg_trans deg)


/- The LHS of the A∞-functor equation is:
  `∑_{r+s+t=n, s≥1} (-1)^† φ_{r+1+t}(a_1, …, a_r, m^A_s(a_{r+1}, …, a_{r+s}), a_{r+s+1}, …, a_n)`
where `† = |a_{r+s+1}| + ⋯ + |a_n| − t` (the same sign as in the Stasheff relation).
Structurally this is the same as the Stasheff term, except the *outer* operation is `φ`
(mapping `A → B`) rather than `m^A` (mapping `A → A`).
-/
section LHS


--helper lemma for computing the degree of the LHS term
lemma LHS_compatible_deg
    {n : ℕ}
    (deg_trans : β_A →+ β_B)
    (deg_trans_ofInt : ∀ k : ℤ, deg_trans (Grading.ofInt k) = Grading.ofInt k)
    (deg : Fin n → β_A)
    (r s : ℕ)
    (hr : r + s ≤ n) :
    functorTargetDeg β_A β_B deg_trans (stasheffDegOut deg r s hr) =
    functorEqTargetDeg β_A β_B deg_trans deg := by
      unfold functorTargetDeg functorEqTargetDeg;
      convert congr_arg ( fun x : β_A => deg_trans x + shift_ofInt ( 1 - ( n + 1 - s : ℤ ) ) ) ( stasheffDegOut_sum_core deg r s hr ) using 1;
      · simp +decide [ Nat.cast_sub ( by linarith : s ≤ n + 1 ) ];
      · simp +decide [ shift_ofInt, deg_trans_ofInt ];
        abel1

def functorLHSTerm
    (AHom : ObjA → ObjA → GradedRModule (β := β_A) (R := R))
    (BHom : ObjB → ObjB → GradedRModule (β := β_B) (R := R))
    (objMap : ObjA → ObjB)
    (deg_trans : β_A →+ β_B)
    (deg_trans_ofInt : ∀ n : ℤ, deg_trans (Grading.ofInt n) = Grading.ofInt n)
    (phi :
      {n : ℕ} → [NeZero n] →
      (obj : Fin (n + 1) → ObjA) →
      (deg : Fin n → β_A) →
      MultilinearMap R
        (fun i : Fin n => ComposableHomType AHom obj deg i)
        (functorTargetType β_A β_B BHom objMap deg_trans obj deg))
    (m_A :
      {n : ℕ} → [NeZero n] →
      (obj : Fin (n + 1) → ObjA) →
      (deg : Fin n → β_A) →
      MultilinearMap R
        (fun i : Fin n => ComposableHomType AHom obj deg i)
        (operationTargetType AHom obj deg))
    {n : ℕ}
    (obj : Fin (n + 1) → ObjA)
    (deg : Fin n → β_A)
    (x : ∀ i : Fin n, ComposableHomType AHom obj deg i)
    (r s : ℕ)
    (hs : 1 ≤ s)
    (hr : r + s ≤ n) :
    functorEqTargetType β_A β_B BHom objMap deg_trans obj deg := by
  -- Outer: apply φ_{n+1-s} to (a_1, …, a_r, inner, a_{r+s+1}, …, a_n)
  let outerN := n + 1 - s
  let degOut := stasheffDegOut deg r s hr
  let objOut := stasheffObjOut obj r s hr
  let xOut : ∀ i : Fin outerN, ComposableHomType AHom objOut degOut i :=
    indexedStasheffXOut AHom m_A obj deg x r s hs hr
  have houterN : 0 < outerN := by
    dsimp [outerN]
    exact indexedStasheffOuterArity_pos r s hr
  letI : NeZero outerN := ⟨Nat.ne_of_gt houterN⟩
  let outer := phi objOut degOut xOut

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
      functorTargetType β_A β_B BHom objMap deg_trans objOut degOut =
        functorEqTargetType β_A β_B BHom objMap deg_trans obj deg := by
    dsimp [functorTargetType, functorEqTargetType]
    rw [hsource, htarget]
    exact congrArg _ (LHS_compatible_deg β_A β_B deg_trans deg_trans_ofInt deg r s hr)

  exact hdeg ▸ outer



def functorLHSSum
    (AHom : ObjA → ObjA → GradedRModule (β := β_A) (R := R))
    (BHom : ObjB → ObjB → GradedRModule (β := β_B) (R := R))
    (objMap : ObjA → ObjB)
    (deg_trans : β_A →+ β_B)
    (deg_trans_ofInt : ∀ n : ℤ, deg_trans (Grading.ofInt n) = Grading.ofInt n)
    (phi :
      {n : ℕ} → [NeZero n] →
      (obj : Fin (n + 1) → ObjA) →
      (deg : Fin n → β_A) →
      MultilinearMap R
        (fun i : Fin n => ComposableHomType AHom obj deg i)
        (functorTargetType β_A β_B BHom objMap deg_trans obj deg))
    (m_A :
      {n : ℕ} → [NeZero n] →
      (obj : Fin (n + 1) → ObjA) →
      (deg : Fin n → β_A) →
      MultilinearMap R
        (fun i : Fin n => ComposableHomType AHom obj deg i)
        (operationTargetType AHom obj deg))
    {n : ℕ}
    (obj : Fin (n + 1) → ObjA)
    (deg : Fin n → β_A)
    (x : ∀ i : Fin n, ComposableHomType AHom obj deg i) :
    functorEqTargetType β_A β_B BHom objMap deg_trans obj deg :=
  ∑ r ∈ (Finset.range (n + 1)).attach,
    ∑ s ∈ (Finset.Ico 1 (n - r.1 + 1)).attach,
      let h : ValidStasheffIndices n r.1 s.1 :=
        validStasheffIndices_of_mem_ranges (n := n) r.2 s.2
      (stasheffSign deg r.1 s.1 h.2) •
        (functorLHSTerm β_A β_B AHom BHom objMap deg_trans deg_trans_ofInt phi m_A
          obj deg x r.1 s.1 h.1 h.2)

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
/-- Object string for the `l`-th block of a composition applied to `obj`. -/
def compositionBlockObj
    {n : ℕ}
    (obj : Fin (n + 1) → ObjA)
    (c : Composition n)
    (l : Fin c.length) : Fin ((c.blocksFun l) + 1) → ObjA :=
  fun i => obj ⟨c.sizeUpTo (l : ℕ) + i.val, by
    have hi : i.val ≤ c.blocksFun l := Nat.lt_succ_iff.mp i.2
    have h₁ : c.sizeUpTo (l : ℕ) + i.val ≤ c.sizeUpTo (l : ℕ) + c.blocksFun l :=
      Nat.add_le_add_left hi _
    have h₂ : c.sizeUpTo (l : ℕ) + c.blocksFun l = c.sizeUpTo ((l : ℕ) + 1) := by
      simpa using (c.sizeUpTo_succ' l).symm
    have h₃ : c.sizeUpTo ((l : ℕ) + 1) ≤ c.sizeUpTo c.length :=
      c.monotone_sizeUpTo (Nat.succ_le_of_lt l.2)
    have h₄ : c.sizeUpTo c.length = n := c.sizeUpTo_length
    exact Nat.lt_succ_of_le <| by
      rw [h₂] at h₁
      rw [h₄] at h₃
      exact le_trans h₁ h₃⟩

--TODO: rename this to like idk. but composition referse to composition block, dotn want to confuse with composition of functors
 /-- Object string obtained by applying `objMap` to the boundary objects of a composition. -/
def functorCompositionOuterObj
    {n : ℕ}
    (objMap : ObjA → ObjB)
    (obj : Fin (n + 1) → ObjA)
    (c : Composition n) : Fin (c.length + 1) → ObjB :=
  fun l => objMap (obj (c.boundary l))

/-- Degrees of the outputs of the functor components on the blocks of a composition. -/
def functorCompositionOuterDeg
    (deg_trans : β_A →+ β_B)
    {n : ℕ}
    (deg : Fin n → β_A)
    (c : Composition n) : Fin c.length → β_B :=
  fun l => functorTargetDeg β_A β_B deg_trans (compositionBlockDeg β_A deg c l)

--helper degree lemma for the RHS
lemma RHS_compatible_deg
    (deg_trans : β_A →+ β_B)
    {n : ℕ}
    (deg : Fin n → β_A)
    (c : Composition n) :
    operationTargetDeg (β := β_B) (functorCompositionOuterDeg β_A β_B deg_trans deg c) =
    functorEqTargetDeg β_A β_B deg_trans deg := by
  have h_sum_deg_trans :
      ∑ l : Fin c.length, ∑ j : Fin (c.blocksFun l), deg_trans (deg (c.embedding l j)) =
        ∑ i : Fin n, deg_trans (deg i) := by
    have h_union :
        Finset.image
            (fun (p : Σ l : Fin c.length, Fin (c.blocksFun l)) => c.embedding p.fst p.snd)
            Finset.univ =
          Finset.univ := by
      ext i
      simp [Finset.mem_image]
      obtain ⟨l, hl⟩ : ∃ l : Fin c.length, i ∈ Finset.image (fun j => c.embedding l j) Finset.univ := by
        have h_partition :
            ∀ i : Fin n, ∃ l : Fin c.length, i ∈ Finset.image (fun j => c.embedding l j) Finset.univ := by
          intro i
          have h_exists_l :
              ∃ l : Fin c.length, i.val < c.sizeUpTo (l.val + 1) ∧ i.val ≥ c.sizeUpTo l.val := by
            have h_exists_l :
                ∃ l : ℕ, l ≤ c.length ∧ i.val < c.sizeUpTo l ∧
                  ∀ k : ℕ, k < l → i.val ≥ c.sizeUpTo k := by
              have h_exists_l : ∃ l : ℕ, l ≤ c.length ∧ i.val < c.sizeUpTo l := by
                use c.length
                simp +decide [Composition.sizeUpTo_length]
              exact ⟨Nat.find h_exists_l, Nat.find_spec h_exists_l |>.1,
                Nat.find_spec h_exists_l |>.2,
                fun k hk => not_lt.1 fun hk' =>
                  Nat.find_min h_exists_l hk
                    ⟨Nat.le_trans (Nat.le_of_lt hk) (Nat.find_spec h_exists_l |>.1), hk'⟩⟩
            obtain ⟨l, hl₁, hl₂, hl₃⟩ := h_exists_l
            rcases l with (_ | l) <;> simp_all +decide
            exact ⟨⟨l, hl₁⟩, hl₂, hl₃ l le_rfl⟩
          obtain ⟨l, hl₁, hl₂⟩ := h_exists_l
          use l
          simp_all +decide [Finset.mem_image, Finset.mem_univ]
          have h_exists_a : ∃ a : Fin (c.blocksFun l), c.embedding l a = i := by
            have h_range : i.val - c.sizeUpTo l.val < c.blocksFun l := by
              rw [tsub_lt_iff_left] <;> try linarith! [Fin.is_lt i]
              convert hl₁ using 1
              simp +decide [Composition.sizeUpTo_succ]
              ring!
            use ⟨i.val - c.sizeUpTo l.val, h_range⟩
            simp +decide [Fin.ext_iff]
            omega
          generalize_proofs at *
          exact h_exists_a
        exact h_partition i
      grind
    have h_sum_eq :
        ∑ i : Fin n, deg_trans (deg i) =
          ∑ p : Σ l : Fin c.length, Fin (c.blocksFun l), deg_trans (deg (c.embedding p.fst p.snd)) := by
      conv_lhs => rw [← h_union, Finset.sum_image (Finset.card_image_iff.mp <| by aesop)]
    rw [h_sum_eq, Finset.sum_sigma']
    rfl
  have h_sum_blocksFun : ∑ l : Fin c.length, (1 - (c.blocksFun l : ℤ)) = (c.length : ℤ) - n := by
    simp +decide
    norm_cast
    aesop
  have h_sum_target_deg :
      ∑ l : Fin c.length, functorTargetDeg β_A β_B deg_trans (compositionBlockDeg β_A deg c l) =
        ∑ i : Fin n, deg_trans (deg i) + shift_ofInt (c.length - n : ℤ) := by
    have h_sum_target_deg :
        ∑ l : Fin c.length, functorTargetDeg β_A β_B deg_trans (compositionBlockDeg β_A deg c l) =
          (∑ l : Fin c.length, ∑ j : Fin (c.blocksFun l), deg_trans (deg (c.embedding l j))) +
            (∑ l : Fin c.length, shift_ofInt (1 - (c.blocksFun l : ℤ))) := by
      simp +decide [functorTargetDeg, compositionBlockDeg, Finset.sum_add_distrib]
    convert h_sum_target_deg using 2
    · aesop
    · rw [← h_sum_blocksFun]
      exact map_sum (Grading.ofInt) _ _
  convert congr_arg (fun x : β_B => x + shift_ofInt (2 - (c.length : ℤ))) h_sum_target_deg using 1
  unfold functorEqTargetDeg
  simp +decide [add_assoc]
  unfold shift_ofInt
  simp +decide

/-- The RHS term for a composition `c = (i₁, …, iₖ)` as a multilinear map
    in the original inputs, with codomain transported to the final functor-equation target. -/
def functorRHSTermMap
    (AHom : ObjA → ObjA → GradedRModule (β := β_A) (R := R))
    (BHom : ObjB → ObjB → GradedRModule (β := β_B) (R := R))
    (objMap : ObjA → ObjB)
    (deg_trans : β_A →+ β_B)
    (phi :
      {n : ℕ} → [NeZero n] →
      (obj : Fin (n + 1) → ObjA) →
      (deg : Fin n → β_A) →
      MultilinearMap R
        (fun i : Fin n => ComposableHomType AHom obj deg i)
        (functorTargetType β_A β_B BHom objMap deg_trans obj deg))
    (m_B :
      {n : ℕ} → [NeZero n] →
      (obj : Fin (n + 1) → ObjB) →
      (deg : Fin n → β_B) →
      MultilinearMap R
        (fun i : Fin n => ComposableHomType BHom obj deg i)
        (operationTargetType BHom obj deg))
    {n : ℕ} [NeZero n]
    (obj : Fin (n + 1) → ObjA)
    (deg : Fin n → β_A)
    (c : Composition n) :
    MultilinearMap R
      (fun i : Fin n => ComposableHomType AHom obj deg i)
      (functorEqTargetType β_A β_B BHom objMap deg_trans obj deg) := by
  let outerDeg := functorCompositionOuterDeg β_A β_B deg_trans deg c
  let outerObj := functorCompositionOuterObj objMap obj c
  have houter : 0 < c.length := c.length_pos_of_pos (Nat.pos_of_ne_zero (NeZero.ne n))
  letI : NeZero c.length := ⟨Nat.ne_of_gt houter⟩
  have hsource : outerObj 0 = objMap (obj 0) := by
    simp [outerObj, functorCompositionOuterObj]
  have htarget : outerObj (Fin.last c.length) = objMap (obj (Fin.last n)) := by
    simp [outerObj, functorCompositionOuterObj]
  have hdeg :
      operationTargetType BHom outerObj
          (functorCompositionOuterDeg β_A β_B deg_trans deg c) =
        functorEqTargetType β_A β_B BHom objMap deg_trans obj deg := by
    dsimp [operationTargetType, functorEqTargetType]
    rw [hsource, htarget]
    exact congrArg _ (RHS_compatible_deg β_A β_B deg_trans deg c)
  refine hdeg ▸ ?_
  exact MultilinearMap.compComposition c (m_B outerObj outerDeg) (fun l => by
    let blockDeg := compositionBlockDeg β_A deg c l
    let blockObj := compositionBlockObj obj c l
    letI : NeZero (c.blocksFun l) := ⟨by
      have hpos : 0 < c.blocksFun l := c.one_le_blocksFun l
      exact Nat.ne_of_gt hpos⟩
    let blockPhi := phi blockObj blockDeg
    have hblock :
        functorTargetType β_A β_B BHom objMap deg_trans blockObj blockDeg =
          ComposableHomType BHom outerObj outerDeg l := by
      dsimp [functorTargetType, ComposableHomType, outerObj, functorCompositionOuterObj,
        outerDeg, functorCompositionOuterDeg, blockObj, compositionBlockObj, blockDeg,
        compositionBlockDeg]
      congr
      simpa using (c.sizeUpTo_succ' l).symm
    exact hblock ▸ blockPhi)

/-- The RHS term for a composition `c = (i₁, …, iₖ)`:
    `m^B_k(φ_{i₁}(block₁), …, φ_{iₖ}(blockₖ))`. -/
def functorRHSTerm
    (AHom : ObjA → ObjA → GradedRModule (β := β_A) (R := R))
    (BHom : ObjB → ObjB → GradedRModule (β := β_B) (R := R))
    (objMap : ObjA → ObjB)
    (deg_trans : β_A →+ β_B)
    (phi :
      {n : ℕ} → [NeZero n] →
      (obj : Fin (n + 1) → ObjA) →
      (deg : Fin n → β_A) →
      MultilinearMap R
        (fun i : Fin n => ComposableHomType AHom obj deg i)
        (functorTargetType β_A β_B BHom objMap deg_trans obj deg))
    (m_B :
      {n : ℕ} → [NeZero n] →
      (obj : Fin (n + 1) → ObjB) →
      (deg : Fin n → β_B) →
      MultilinearMap R
        (fun i : Fin n => ComposableHomType BHom obj deg i)
        (operationTargetType BHom obj deg))
    {n : ℕ} [NeZero n]
    (obj : Fin (n + 1) → ObjA)
    (deg : Fin n → β_A)
    (x : ∀ i : Fin n, ComposableHomType AHom obj deg i)
    (c : Composition n) :
    functorEqTargetType β_A β_B BHom objMap deg_trans obj deg := by
  exact functorRHSTermMap β_A β_B AHom BHom objMap deg_trans phi m_B obj deg c x

def functorRHSSum
    (AHom : ObjA → ObjA → GradedRModule (β := β_A) (R := R))
    (BHom : ObjB → ObjB → GradedRModule (β := β_B) (R := R))
    (objMap : ObjA → ObjB)
    (deg_trans : β_A →+ β_B)
    (phi :
      {n : ℕ} → [NeZero n] →
      (obj : Fin (n + 1) → ObjA) →
      (deg : Fin n → β_A) →
      MultilinearMap R
        (fun i : Fin n => ComposableHomType AHom obj deg i)
        (functorTargetType β_A β_B BHom objMap deg_trans obj deg))
    (m_B :
      {n : ℕ} → [NeZero n] →
      (obj : Fin (n + 1) → ObjB) →
      (deg : Fin n → β_B) →
      MultilinearMap R
        (fun i : Fin n => ComposableHomType BHom obj deg i)
        (operationTargetType BHom obj deg))
    {n : ℕ} [NeZero n]
    (obj : Fin (n + 1) → ObjA)
    (deg : Fin n → β_A)
    (x : ∀ i : Fin n, ComposableHomType AHom obj deg i) :
    functorEqTargetType β_A β_B BHom objMap deg_trans obj deg :=
  ∑ c : Composition n,
    functorRHSTerm β_A β_B AHom BHom objMap deg_trans phi m_B obj deg x c
end RHS


/-- The A∞ functor equations as a property of raw functor data between raw A∞ category
    structures. -/
def SatisfiesFunctorEquations
    (R : Type u) [CommRing R]
    (ObjA : Type x) (ObjB : Type y)
    [AInfinityCategoryStruct β_A R ObjA]
    [AInfinityCategoryStruct β_B R ObjB]
    (F : AInfinityFunctorData (β_A := β_A) (β_B := β_B) R ObjA ObjB) : Prop :=
  ∀ (n : ℕ) [NeZero n] (obj : Fin (n + 1) → ObjA) (deg : Fin n → β_A)
    (x : ∀ i : Fin n, ComposableHomType (GHom β_A R) obj deg i),
    functorLHSSum β_A β_B
      (GHom β_A R) (GHom β_B R)
      F.objMap F.deg_trans F.deg_trans_ofInt F.phi
      (AInfinityCategoryStruct.m (β := β_A) (R := R) (Obj := ObjA))
      obj deg x =
    functorRHSSum β_A β_B
      (GHom β_A R) (GHom β_B R)
      F.objMap F.deg_trans F.phi
      (AInfinityCategoryStruct.m (β := β_B) (R := R) (Obj := ObjB))
      obj deg x


end AInfinityFunctorData

/-- An A∞ functor between A∞ categories is raw functor data satisfying the functor
    equations. -/
structure AInfinityFunctor
    (R : Type u) [CommRing R]
    (ObjA : Type x) (ObjB : Type y)
    [AInfinityCategory β_A R ObjA]
    [AInfinityCategory β_B R ObjB]
    extends AInfinityFunctorData (β_A := β_A) (β_B := β_B) R ObjA ObjB where
  satisfiesFunctorEquations :
    AInfinityFunctorData.SatisfiesFunctorEquations
      (β_A := β_A) (β_B := β_B) R ObjA ObjB toAInfinityFunctorData

end AInfinityTheory
