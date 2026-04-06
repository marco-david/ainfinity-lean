import Mathlib
import Ainfinity.AInfinityMorphism
open CategoryTheory Finset AInfinityCategoryTheory AInfinityAlgebraTheory AInfinityAlgData
open AInfinityMorphismTheory AInfinityMorphismData

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


/-! ## A∞ morphism composition -/
namespace AInfinityCompositionTheory
universe u v w x
variable {β_A : Type v} [Grading β_A]
variable {β_B : Type w} [Grading β_B]
variable {β_C : Type x} [Grading β_C]
variable {β_D : Type x} [Grading β_D]
variable {R : Type u} [CommRing R]
variable {A : GradedRModule (β := β_A) (R := R)}
variable {B : GradedRModule (β := β_B) (R := R)}
variable {C : GradedRModule (β := β_C) (R := R)}
variable {D : GradedRModule (β := β_D) (R := R)}

/-- The composed degree translation `β_A →+ β_C`. -/
def compDegTrans
    (F : AInfinityMorphismData R A B)
    (G : AInfinityMorphismData R B C) : β_A →+ β_C :=
  G.deg_trans.comp F.deg_trans

-- Degree compatibility helper lemma
lemma comp_deg_compat
    (F : AInfinityMorphismData R A B)
    (G : AInfinityMorphismData R B C)
    {n : ℕ} (deg : Fin n → β_A) (c : Composition n) :
    morphismTargetDeg G.deg_trans (morphismRHSOuterDeg F deg c) =
    morphismTargetDeg (compDegTrans F G) deg := by
  -- Apply the degree compatibility condition to simplify the expression.
  have h_deg_comp : ∀ (l : Fin c.length), G.deg_trans (morphismTargetDeg F.deg_trans (compositionBlockDeg deg c l)) = morphismTargetDeg (compDegTrans F G) (compositionBlockDeg deg c l) := by
    intro l
    simp [morphismTargetDeg, compDegTrans];
    exact G.deg_trans_ofInt _;
  -- Apply the degree compatibility condition to each term in the sum.
  have h_sum_deg_comp : ∑ l : Fin c.length, G.deg_trans (morphismTargetDeg F.deg_trans (compositionBlockDeg deg c l)) = ∑ i : Fin n, (compDegTrans F G) (deg i) + ∑ l : Fin c.length, shift_ofInt (1 - (c.blocksFun l : ℤ)) := by
    rw [ Finset.sum_congr rfl fun l _ => h_deg_comp l ];
    unfold morphismTargetDeg; simp +decide [ Finset.sum_add_distrib ] ;
    have h_sum_deg_comp : ∑ x : Fin c.length, ∑ i : Fin (c.blocksFun x), (compDegTrans F G) (deg (c.embedding x i)) = ∑ i : Fin n, (compDegTrans F G) (deg i) := by
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
  convert congr_arg ( fun x => x + shift_ofInt ( 1 - ( c.length : ℤ ) ) ) h_sum_deg_comp using 1 ; simp +decide [ morphismTargetDeg ] ; ring_nf!;
  have h_shift_sum : ∑ l : Fin c.length, (1 - (c.blocksFun l : ℤ)) + (1 - (c.length : ℤ)) = 1 - (n : ℤ) := by
    simp +decide [ Finset.sum_sub_distrib];
    exact_mod_cast c.sum_blocksFun
  generalize_proofs at *; (
  simp +decide [ ← h_shift_sum, add_assoc, shift_ofInt ];
  simp +decide [ ← map_nsmul ])

/-- The multilinear map for a single composition term (before degree cast). -/
def compTermMultilinearMapRaw
    (F : AInfinityMorphismData R A B)
    (G : AInfinityMorphismData R B C)
    {n : ℕ} (deg : Fin n → β_A) (c : Composition n) :
    MultilinearMap R (fun i => A (deg i))
      (C (morphismTargetDeg G.deg_trans (morphismRHSOuterDeg F deg c))) :=
  (G.phi c.length (morphismRHSOuterDeg F deg c)).compComposition c
    (fun l => F.phi (c.blocksFun l) (compositionBlockDeg deg c l))

/-- The multilinear map for a single composition term (cast to composed target degree). -/
def compTermMultilinearMap
    (F : AInfinityMorphismData R A B)
    (G : AInfinityMorphismData R B C)
    {n : ℕ} (deg : Fin n → β_A) (c : Composition n) :
    MultilinearMap R (fun i => A (deg i))
      (C (morphismTargetDeg (compDegTrans F G) deg)) :=
  comp_deg_compat F G deg c ▸ compTermMultilinearMapRaw F G deg c
/-- The `n`-th component of the composition: sum over all compositions of `n`. -/
def compPhi
    (F : AInfinityMorphismData R A B)
    (G : AInfinityMorphismData R B C)
    (n : ℕ) (deg : Fin n → β_A) :
    MultilinearMap R (fun i => A (deg i))
      (C (morphismTargetDeg (compDegTrans F G) deg)) :=
  ∑ c : Composition n, compTermMultilinearMap F G deg c


end AInfinityCompositionTheory

namespace AInfinityMorphismTheory
namespace AInfinityMorphismData

variable {β_A : Type v} [Grading β_A]
variable {β_B : Type w} [Grading β_B]
variable {β_C : Type x} [Grading β_C]
variable {β_D : Type y} [Grading β_D]
variable {R : Type u} [CommRing R]
variable {A : GradedRModule (β := β_A) (R := R)}
variable {B : GradedRModule (β := β_B) (R := R)}
variable {C : GradedRModule (β := β_C) (R := R)}
variable {D : GradedRModule (β := β_D) (R := R)}

def comp
    (F : AInfinityMorphismData (β_A := β_A) (β_B := β_B) R A B)
    (G : AInfinityMorphismData (β_A := β_B) (β_B := β_C) R B C) :
    AInfinityMorphismData (β_A := β_A) (β_B := β_C) R A C where
  deg_trans := AInfinityCompositionTheory.compDegTrans F G
  deg_trans_ofInt n := by
    simp [AInfinityCompositionTheory.compDegTrans, AddMonoidHom.comp_apply,
          F.deg_trans_ofInt, G.deg_trans_ofInt]
  deg_trans_sign b := by
    simp [AInfinityCompositionTheory.compDegTrans, AddMonoidHom.comp_apply,
          F.deg_trans_sign, G.deg_trans_sign]
  phi := fun n deg => AInfinityCompositionTheory.compPhi F G n deg


theorem ext_iff {F G : AInfinityMorphismData (β_A := β_A) (β_B := β_B) R A B} :
    F = G ↔ (F.deg_trans = G.deg_trans ∧ HEq F.phi G.phi) := by
  constructor
  · rintro rfl; exact ⟨rfl, heq_of_eq rfl⟩
  · rcases F with ⟨dt1, dto1, dts1, phi1⟩
    rcases G with ⟨dt2, dto2, dts2, phi2⟩
    simp only [mk.injEq]
    exact id
open AInfinityCompositionTheory in

lemma eq_mpr_sum {β : Type*} [AddCommGroup β] (M : β → Type*)
    [∀ b, AddCommMonoid (M b)] {a b : β} (h : a = b)
    {α : Type*} (s : Finset α) (f : α → M a) :
    (h ▸ (∑ i ∈ s, f i) : M b) = ∑ i ∈ s, (h ▸ f i : M b) := by
  subst h; rfl
/-- Transport (`▸`) on a multilinear map commutes with application. -/
lemma eq_mpr_multilinearMap_apply' {β : Type*} [AddCommGroup β]
    {R : Type*} [CommSemiring R]
    {ι : Type*} {N : ι → Type*} [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]
    (M : β → Type*) [∀ b, AddCommMonoid (M b)] [∀ b, Module R (M b)]
    {a b : β} (h : a = b)
    (f : MultilinearMap R N (M a)) (x : ∀ i, N i) :
    ((h ▸ f : MultilinearMap R N (M b)) x : M b) = (h ▸ (f x) : M b) := by
  subst h; rfl
/-- The phi components of `(F.comp G).comp H` and `F.comp (G.comp H)` are equal.
    This is the core content of associativity: both compute the same triple composition
    `H ∘ G ∘ F` by summing over all 2-level decompositions of compositions,
    just organized differently. -/
theorem comp_phi_eq
    (F : AInfinityMorphismData (β_A := β_A) (β_B := β_B) R A B)
    (G : AInfinityMorphismData (β_A := β_B) (β_B := β_C) R B C)
    (H : AInfinityMorphismData (β_A := β_C) (β_B := β_D) R C D) :
    ((F.comp G).comp H).phi = (F.comp (G.comp H)).phi := by
  sorry

theorem comp_assoc
    (F : AInfinityMorphismData (β_A := β_A) (β_B := β_B) R A B)
    (G : AInfinityMorphismData (β_A := β_B) (β_B := β_C) R B C)
    (H : AInfinityMorphismData (β_A := β_C) (β_B := β_D) R C D) :
    (F.comp G).comp H = F.comp (G.comp H) := by
  rw [ext_iff]
  exact ⟨rfl, heq_of_eq (comp_phi_eq F G H)⟩

end AInfinityMorphismData
end AInfinityMorphismTheory
