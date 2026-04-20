module

public import Mathlib
public import AInfinity.Grading
public import AInfinity.AInfinityFunctor

@[expose] public section

open CategoryTheory AInfinityTheory AInfinityCategoryTheory AInfinityFunctorTheory

noncomputable section

/-! ## General multi-composition of multilinear maps along a composition -/
section CompComposition
universe u₁
variable {R : Type u₁} [CommSemiring R]

--Helper lemmas
lemma Composition.embedding_ne_of_ne
    {n : ℕ} (c : Composition n)
    {l l₀ : Fin c.length} (hl : l ≠ l₀)
    (j : Fin (c.blocksFun l)) (j₀ : Fin (c.blocksFun l₀)) :
    (c.embedding l) j ≠ (c.embedding l₀) j₀ := by
  have h_range : Disjoint (Set.range (c.embedding l)) (Set.range (c.embedding l₀)) := by
    exact c.disjoint_range hl
  exact fun h => h_range.le_bot ⟨ ⟨ j, h ⟩, ⟨ j₀, rfl ⟩ ⟩
lemma Composition.update_comp_ne_block
    {n : ℕ} (c : Composition n)
    {M : Fin n → Type*} [DecidableEq (Fin n)] (m : ∀ i, M i)
    {l₀ : Fin c.length} (j₀ : Fin (c.blocksFun l₀))
    (v : M (c.embedding l₀ j₀))
    {l : Fin c.length} (hl : l ≠ l₀) :
    (fun j => Function.update m (c.embedding l₀ j₀) v (c.embedding l j)) =
      (fun j => m (c.embedding l j)) := by
  exact funext fun j => Function.update_of_ne ( by intro h; have := Composition.embedding_ne_of_ne c hl j j₀; aesop ) _ _;
lemma Composition.update_comp_same_block
    {n : ℕ} (c : Composition n)
    {M : Fin n → Type*} [DecidableEq (Fin n)] (m : ∀ i, M i)
    (l₀ : Fin c.length) (j₀ : Fin (c.blocksFun l₀))
    (v : M (c.embedding l₀ j₀)) :
    (fun j => Function.update m (c.embedding l₀ j₀) v (c.embedding l₀ j)) =
      Function.update (fun j => m (c.embedding l₀ j)) j₀ v := by
  ext j; exact (by
  by_cases h : ( c.embedding l₀ ) j = ( c.embedding l₀ ) j₀ <;> simp +decide [ h, Function.update ];
  · have := c.embedding l₀ |>.injective h; aesop;
  · aesop);
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
  ext l;
  by_cases hl : l = l₀;
  · have := Composition.update_comp_same_block c m l₀ j₀ v;
    aesop;
  · rw [ Function.update_of_ne hl ];
    have := Composition.update_comp_ne_block c m j₀ v hl;
    rw [ this ]

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

  --Below is just proof of multilinearity
  map_update_add' m i p q := by
    obtain ⟨l₀, j₀, rfl⟩ : ∃ l : Fin c.length, ∃ j : Fin (c.blocksFun l),
        c.embedding l j = i :=
      ⟨c.index i, c.invEmbedding i, c.embedding_comp_inv i⟩
    have h := c.compComposition_outer_update f m l₀ j₀
    -- Step 1: rewrite LHS
    have lhs : g (fun l => f l (fun j => Function.update m _ (p + q) (c.embedding l j)))
      = g (Function.update (fun l => f l (fun j => m (c.embedding l j))) l₀
          (f l₀ (Function.update (fun j => m (c.embedding l₀ j)) j₀ (p + q)))) := by
      congr 1; exact h (p + q)
    -- Step 2: rewrite RHS terms
    have rhs1 : g (fun l => f l (fun j => Function.update m _ p (c.embedding l j)))
      = g (Function.update (fun l => f l (fun j => m (c.embedding l j))) l₀
          (f l₀ (Function.update (fun j => m (c.embedding l₀ j)) j₀ p))) := by
      congr 1; exact h p
    have rhs2 : g (fun l => f l (fun j => Function.update m _ q (c.embedding l j)))
      = g (Function.update (fun l => f l (fun j => m (c.embedding l j))) l₀
          (f l₀ (Function.update (fun j => m (c.embedding l₀ j)) j₀ q))) := by
      congr 1; exact h q
    rw [lhs, rhs1, rhs2, (f l₀).map_update_add, g.map_update_add]
  map_update_smul' m i a p := by
    obtain ⟨l₀, j₀, rfl⟩ : ∃ l : Fin c.length, ∃ j : Fin (c.blocksFun l),
        c.embedding l j = i :=
      ⟨c.index i, c.invEmbedding i, c.embedding_comp_inv i⟩
    have h := c.compComposition_outer_update f m l₀ j₀
    have lhs : g (fun l => f l (fun j => Function.update m _ (a • p) (c.embedding l j)))
      = g (Function.update (fun l => f l (fun j => m (c.embedding l j))) l₀
          (f l₀ (Function.update (fun j => m (c.embedding l₀ j)) j₀ (a • p)))) := by
      congr 1; exact h (a • p)
    have rhs : g (fun l => f l (fun j => Function.update m _ p (c.embedding l j)))
      = g (Function.update (fun l => f l (fun j => m (c.embedding l j))) l₀
          (f l₀ (Function.update (fun j => m (c.embedding l₀ j)) j₀ p))) := by
      congr 1; exact h p
    rw [lhs, rhs, (f l₀).map_update_smul, g.map_update_smul]
end CompComposition


/-! ## A∞ functor composition -/
namespace AInfinityCompositionTheory
universe u v w x y z
variable {β_A : Type v} [Grading β_A]
variable {β_B : Type w} [Grading β_B]
variable {β_C : Type x} [Grading β_C]
variable {R : Type u} [CommRing R]
variable {ObjA : Type y} {ObjB : Type z} {ObjC : Type x}
variable [QA : RLinearGQuiver β_A R ObjA]
variable [QB : RLinearGQuiver β_B R ObjB]
variable [QC : RLinearGQuiver β_C R ObjC]

/-- The composed object map `ObjA → ObjC`. -/
def compObjMap
    (F : @AInfinityFunctorData β_A _ β_B _ R _ ObjA ObjB QA QB)
    (G : @AInfinityFunctorData β_B _ β_C _ R _ ObjB ObjC QB QC) :
    ObjA → ObjC :=
  G.F ∘ F.F

/-- The composed degree translation `β_A →+ β_C`. -/
def compDegTrans
    (F : @AInfinityFunctorData β_A _ β_B _ R _ ObjA ObjB QA QB)
    (G : @AInfinityFunctorData β_B _ β_C _ R _ ObjB ObjC QB QC) :
    β_A →+ β_C :=
  G.deg_trans.comp F.deg_trans

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

/-- Object string for the outer functor in the composition term. -/
def functorRHSOuterObj
    {n : ℕ}
    (F : ObjA → ObjB)
    (obj : Fin (n + 1) → ObjA)
    (c : Composition n) : Fin (c.length + 1) → ObjB :=
  fun l => F (obj (c.boundary l))

/-- Degrees of the inner `F`-blocks, viewed as the inputs to the outer functor. -/
def functorRHSOuterDeg
    (deg_trans : β_A →+ β_B)
    {n : ℕ}
    (deg : Fin n → β_A)
    (c : Composition n) : Fin c.length → β_B :=
  fun l => functorTargetDeg β_A β_B deg_trans (compositionBlockDeg deg c l)

-- Degree compatibility helper lemma
lemma comp_deg_compat
    (F : @AInfinityFunctorData β_A _ β_B _ R _ ObjA ObjB QA QB)
    (G : @AInfinityFunctorData β_B _ β_C _ R _ ObjB ObjC QB QC)
    {n : ℕ} (deg : Fin n → β_A) (c : Composition n) :
    functorTargetDeg β_B β_C G.deg_trans
        (functorRHSOuterDeg F.deg_trans deg c) =
      functorTargetDeg β_A β_C (compDegTrans F G) deg := by
  -- Apply the degree compatibility condition to simplify the expression.
  have h_deg_comp :
      ∀ l : Fin c.length,
        G.deg_trans
            (functorTargetDeg β_A β_B F.deg_trans
              (compositionBlockDeg deg c l)) =
          functorTargetDeg β_A β_C (compDegTrans F G)
            (compositionBlockDeg deg c l) := by
    intro l
    simp [functorTargetDeg, compDegTrans]
    exact G.deg_trans_ofInt _;
  -- Apply the degree compatibility condition to each term in the sum.
  have h_sum_deg_comp :
      ∑ l : Fin c.length,
        G.deg_trans
          (functorTargetDeg β_A β_B F.deg_trans
            (compositionBlockDeg deg c l)) =
        ∑ i : Fin n, (compDegTrans F G) (deg i) +
          ∑ l : Fin c.length, shift_ofInt (1 - (c.blocksFun l : ℤ)) := by
    rw [ Finset.sum_congr rfl fun l _ => h_deg_comp l ];
    unfold functorTargetDeg
    simp +decide [ Finset.sum_add_distrib ]
    have h_sum_deg_comp :
        ∑ x : Fin c.length, ∑ i : Fin (c.blocksFun x),
          (compDegTrans F G) (deg (c.embedding x i)) =
        ∑ i : Fin n, (compDegTrans F G) (deg i) := by
      have h_sum_deg_comp : Finset.biUnion (Finset.univ : Finset (Fin c.length)) (fun l => Finset.image (fun j => c.embedding l j) Finset.univ) = Finset.univ := by
        ext i; simp [Finset.mem_biUnion, Finset.mem_image];
        exact ⟨ c.index i, c.invEmbedding i, c.embedding_comp_inv i ⟩;
      have h_sum_deg_comp : ∑ x : Fin c.length, ∑ i : Fin (c.blocksFun x), (compDegTrans F G) (deg (c.embedding x i)) = ∑ i ∈ Finset.biUnion (Finset.univ : Finset (Fin c.length)) (fun l => Finset.image (fun j => c.embedding l j) Finset.univ), (compDegTrans F G) (deg i) := by
        rw [ Finset.sum_biUnion ];
        · simp +decide [ Finset.sum_image, Function.Injective ];
        · intros l hl l' hl' hll'; simp_all +decide [ Finset.disjoint_left ] ;
          exact fun a x hx => hll' <| by have := Composition.embedding_ne_of_ne c hll' a x; aesop;
      aesop;
    exact h_sum_deg_comp;
  unfold functorRHSOuterDeg functorTargetDeg
  rw [h_sum_deg_comp]
  have h_shift_sum : ∑ l : Fin c.length, (1 - (c.blocksFun l : ℤ)) + (1 - (c.length : ℤ)) = 1 - (n : ℤ) := by
    simp +decide [ Finset.sum_sub_distrib];
    exact_mod_cast c.sum_blocksFun
  generalize_proofs at *; (
  simp +decide [ ← h_shift_sum, add_assoc, shift_ofInt ];
  simp +decide [ ← map_nsmul ])

/-- The multilinear map for a single composition term (before degree cast). -/
def compTermMultilinearMapRaw
    (F : @AInfinityFunctorData β_A _ β_B _ R _ ObjA ObjB QA QB)
    (G : @AInfinityFunctorData β_B _ β_C _ R _ ObjB ObjC QB QC)
    {n : ℕ} [NeZero n]
    (obj : Fin (n + 1) → ObjA) (deg : Fin n → β_A) (c : Composition n) :
    MultilinearMap R
      (fun i : Fin n => composableHomType (GHom β_A R) obj deg i)
      (functorTargetType β_B β_C (GHom β_C R) G.F G.deg_trans
        (functorRHSOuterObj F.F obj c)
        (functorRHSOuterDeg F.deg_trans deg c)) := by
  let outerObj := functorRHSOuterObj F.F obj c
  let outerDeg := functorRHSOuterDeg F.deg_trans deg c
  have houter : 0 < c.length := c.length_pos_of_pos (Nat.pos_of_ne_zero (NeZero.ne n))
  letI : NeZero c.length := ⟨Nat.ne_of_gt houter⟩
  exact (G.phi outerObj outerDeg).compComposition c (fun l => by
    let blockDeg := compositionBlockDeg deg c l
    let blockObj := compositionBlockObj obj c l
    letI : NeZero (c.blocksFun l) := ⟨Nat.ne_of_gt (c.one_le_blocksFun l)⟩
    let blockPhi := F.phi blockObj blockDeg
    have hdeg :
        functorTargetType β_A β_B (GHom β_B R) F.F F.deg_trans blockObj blockDeg =
          composableHomType (GHom β_B R) outerObj outerDeg l := by
      dsimp [functorTargetType, composableHomType, outerObj,
        functorRHSOuterObj, outerDeg, functorRHSOuterDeg, blockObj,
        compositionBlockObj, blockDeg, compositionBlockDeg]
      congr
      simpa using (c.sizeUpTo_succ' l).symm
    exact hdeg ▸ blockPhi)

/-- The multilinear map for a single composition term (cast to composed target degree). -/
def compTermMultilinearMap
    (F : @AInfinityFunctorData β_A _ β_B _ R _ ObjA ObjB QA QB)
    (G : @AInfinityFunctorData β_B _ β_C _ R _ ObjB ObjC QB QC)
    {n : ℕ} [NeZero n]
    (obj : Fin (n + 1) → ObjA) (deg : Fin n → β_A) (c : Composition n) :
    MultilinearMap R
      (fun i : Fin n => composableHomType (GHom β_A R) obj deg i)
      (functorTargetType β_A β_C (GHom β_C R) (compObjMap F G) (compDegTrans F G) obj deg) := by
  let outerObj := functorRHSOuterObj F.F obj c
  have hsource : outerObj 0 = F.F (obj 0) := by
    simp [outerObj, functorRHSOuterObj]
  have htarget : outerObj (Fin.last c.length) = F.F (obj (Fin.last n)) := by
    simp [outerObj, functorRHSOuterObj]
  have htargetType :
      functorTargetType β_B β_C (GHom β_C R) G.F G.deg_trans outerObj
        (functorRHSOuterDeg F.deg_trans deg c) =
      functorTargetType β_A β_C (GHom β_C R) (compObjMap F G) (compDegTrans F G) obj deg := by
    dsimp [functorTargetType, compObjMap]
    rw [hsource, htarget]
    exact congrArg
      ((GHom β_C R) (G.F (F.F (obj 0))) (G.F (F.F (obj (Fin.last n)))))
      (comp_deg_compat F G deg c)
  exact htargetType ▸ compTermMultilinearMapRaw F G obj deg c

/-- The `n`-th component of the composition: sum over all compositions of `n`. -/
def compPhi
    (F : @AInfinityFunctorData β_A _ β_B _ R _ ObjA ObjB QA QB)
    (G : @AInfinityFunctorData β_B _ β_C _ R _ ObjB ObjC QB QC)
    (n : ℕ) [NeZero n]
    (obj : Fin (n + 1) → ObjA) (deg : Fin n → β_A) :
    MultilinearMap R
      (fun i : Fin n => composableHomType (GHom β_A R) obj deg i)
      (functorTargetType β_A β_C (GHom β_C R) (compObjMap F G) (compDegTrans F G) obj deg) :=
  ∑ c : Composition n, compTermMultilinearMap F G obj deg c


end AInfinityCompositionTheory

namespace AInfinityFunctorTheory
namespace AInfinityFunctorData

universe u v w x y z

variable {β_A : Type v} [Grading β_A]
variable {β_B : Type w} [Grading β_B]
variable {β_C : Type x} [Grading β_C]
variable {R : Type u} [CommRing R]
variable {ObjA : Type y} {ObjB : Type z} {ObjC : Type x}
variable [QA : RLinearGQuiver β_A R ObjA]
variable [QB : RLinearGQuiver β_B R ObjB]
variable [QC : RLinearGQuiver β_C R ObjC]

def comp
    (F : @AInfinityFunctorData β_A _ β_B _ R _ ObjA ObjB QA QB)
    (G : @AInfinityFunctorData β_B _ β_C _ R _ ObjB ObjC QB QC) :
    AInfinityFunctorData (β_A := β_A) (β_B := β_C) R ObjA ObjC where
  F := AInfinityCompositionTheory.compObjMap F G
  deg_trans := AInfinityCompositionTheory.compDegTrans F G
  deg_trans_ofInt n := by
    simp [AInfinityCompositionTheory.compDegTrans, AddMonoidHom.comp_apply,
          F.deg_trans_ofInt, G.deg_trans_ofInt]
  deg_trans_sign b := by
    simp [AInfinityCompositionTheory.compDegTrans, AddMonoidHom.comp_apply,
          F.deg_trans_sign, G.deg_trans_sign]
  phi := by
    intro n _ obj deg
    exact AInfinityCompositionTheory.compPhi F G n obj deg



end AInfinityFunctorData
end AInfinityFunctorTheory
