module

public import Mathlib
public import AInfinity.Grading
public import AInfinity.AInfinityFunctor

@[expose] public section

open CategoryTheory AInfinityTheory

noncomputable section

namespace AInfinityTheory

universe u v w x y z t

variable (β_A : Type v) [Grading β_A]
variable (β_B : Type w) [Grading β_B]
variable (β_C : Type x) [Grading β_C]

namespace AInfinityFunctorData

variable {R : Type u} [CommRing R]
variable {ObjA : Type y} {ObjB : Type z} {ObjC : Type t}

/-! ## Raw A∞ functor composition -/

/-- Applying the outer degree translation to the block outputs of `F`
recovers the target degree of the composite component. -/
lemma comp_compatible_deg
    (F_deg_trans : β_A →+ β_B)
    (G_deg_trans : β_B →+ β_C)
    (G_deg_trans_ofInt : ∀ n : ℤ, G_deg_trans (Grading.ofInt n) = Grading.ofInt n)
    {n : ℕ}
    (deg : Fin n → β_A)
    (c : Composition n) :
    functorTargetDeg β_B β_C G_deg_trans
        (functorCompositionOuterDeg β_A β_B F_deg_trans deg c) =
      functorTargetDeg β_A β_C (G_deg_trans.comp F_deg_trans) deg := by
  have h_deg_comp :
      ∀ l : Fin c.length,
        G_deg_trans
            (functorTargetDeg β_A β_B F_deg_trans
              (compositionBlockDeg β_A deg c l)) =
          functorTargetDeg β_A β_C (G_deg_trans.comp F_deg_trans)
            (compositionBlockDeg β_A deg c l) := by
    intro l
    simp [functorTargetDeg, shift_ofInt, AddMonoidHom.comp_apply, G_deg_trans_ofInt]
  have h_sum_deg_comp :
      ∑ l : Fin c.length,
        G_deg_trans
          (functorTargetDeg β_A β_B F_deg_trans
            (compositionBlockDeg β_A deg c l)) =
        ∑ i : Fin n, (G_deg_trans.comp F_deg_trans) (deg i) +
          ∑ l : Fin c.length, shift_ofInt (1 - (c.blocksFun l : ℤ)) := by
    rw [Finset.sum_congr rfl fun l _ => h_deg_comp l]
    unfold functorTargetDeg
    simp +decide [Finset.sum_add_distrib]
    have h_sum_deg_comp :
        ∑ x : Fin c.length, ∑ i : Fin (c.blocksFun x),
          (G_deg_trans.comp F_deg_trans) (deg (c.embedding x i)) =
        ∑ i : Fin n, (G_deg_trans.comp F_deg_trans) (deg i) := by
      have h_sum_deg_comp :
          Finset.biUnion (Finset.univ : Finset (Fin c.length))
            (fun l => Finset.image (fun j => c.embedding l j) Finset.univ) =
          Finset.univ := by
        ext i
        simp [Finset.mem_biUnion, Finset.mem_image]
        exact ⟨c.index i, c.invEmbedding i, c.embedding_comp_inv i⟩
      have h_sum_deg_comp :
          ∑ x : Fin c.length, ∑ i : Fin (c.blocksFun x),
            (G_deg_trans.comp F_deg_trans) (deg (c.embedding x i)) =
          ∑ i ∈ Finset.biUnion (Finset.univ : Finset (Fin c.length))
              (fun l => Finset.image (fun j => c.embedding l j) Finset.univ),
            (G_deg_trans.comp F_deg_trans) (deg i) := by
        rw [Finset.sum_biUnion]
        · simp +decide [Finset.sum_image, Function.Injective]
        · intro l hl l' hl' hll'
          simp_all +decide [Finset.disjoint_left]
          exact fun a x hx => hll' <| by
            have := Composition.embedding_ne_of_ne c hll' a x
            aesop
      aesop
    exact h_sum_deg_comp
  unfold functorCompositionOuterDeg functorTargetDeg
  rw [h_sum_deg_comp]
  have h_shift_sum :
      ∑ l : Fin c.length, (1 - (c.blocksFun l : ℤ)) + (1 - (c.length : ℤ)) =
        1 - (n : ℤ) := by
    simp +decide [Finset.sum_sub_distrib]
    exact_mod_cast c.sum_blocksFun
  generalize_proofs at *
  simp +decide [← h_shift_sum, add_assoc, shift_ofInt]
  simp +decide [← map_nsmul]

/-- Transport from the outer target of a composition term to the target of the
composite functor component. -/
lemma comp_term_target_module_eq
    (CHom : ObjC → ObjC → GradedRModule (β := β_C) (R := R))
    (F_objMap : ObjA → ObjB)
    (F_deg_trans : β_A →+ β_B)
    (G_objMap : ObjB → ObjC)
    (G_deg_trans : β_B →+ β_C)
    (G_deg_trans_ofInt : ∀ n : ℤ, G_deg_trans (Grading.ofInt n) = Grading.ofInt n)
    {n : ℕ}
    (obj : Fin (n + 1) → ObjA)
    (deg : Fin n → β_A)
    (c : Composition n) :
    functorTargetType β_B β_C CHom G_objMap G_deg_trans
        (functorCompositionOuterObj F_objMap obj c)
        (functorCompositionOuterDeg β_A β_B F_deg_trans deg c) =
      functorTargetType β_A β_C CHom (G_objMap ∘ F_objMap)
        (G_deg_trans.comp F_deg_trans) obj deg := by
  have hsource : functorCompositionOuterObj F_objMap obj c 0 = F_objMap (obj 0) := by
    simp [functorCompositionOuterObj]
  have htarget :
      functorCompositionOuterObj F_objMap obj c (Fin.last c.length) = F_objMap (obj (Fin.last n)) := by
    simp [functorCompositionOuterObj]
  dsimp [functorTargetType]
  rw [hsource, htarget]
  exact congrArg
    (CHom (G_objMap (F_objMap (obj 0)))
      (G_objMap (F_objMap (obj (Fin.last n)))))
    (comp_compatible_deg β_A β_B β_C
      F_deg_trans G_deg_trans G_deg_trans_ofInt deg c)

/-- Transport from an `F`-block output to the corresponding input of the outer
`G`-component in a composition term. -/
lemma comp_term_block_module_eq
    (BHom : ObjB → ObjB → GradedRModule (β := β_B) (R := R))
    (F_objMap : ObjA → ObjB)
    (F_deg_trans : β_A →+ β_B)
    {n : ℕ}
    (obj : Fin (n + 1) → ObjA)
    (deg : Fin n → β_A)
    (c : Composition n)
    (l : Fin c.length) :
    functorTargetType β_A β_B BHom F_objMap F_deg_trans
        (compositionBlockObj obj c l) (compositionBlockDeg β_A deg c l) =
      ComposableHomType BHom
        (functorCompositionOuterObj F_objMap obj c)
        (functorCompositionOuterDeg β_A β_B F_deg_trans deg c) l := by
  dsimp [functorTargetType, ComposableHomType, functorCompositionOuterObj,
    functorCompositionOuterDeg, compositionBlockObj, compositionBlockDeg]
  congr
  simpa using (c.sizeUpTo_succ' l).symm

/-- The `l`-th block map used in a single composition term. -/
def compTermBlock
    (AHom : ObjA → ObjA → GradedRModule (β := β_A) (R := R))
    (BHom : ObjB → ObjB → GradedRModule (β := β_B) (R := R))
    (F_objMap : ObjA → ObjB)
    (F_deg_trans : β_A →+ β_B)
    (F_phi :
      {n : ℕ} → [NeZero n] →
      (obj : Fin (n + 1) → ObjA) →
      (deg : Fin n → β_A) →
      MultilinearMap R
        (fun i : Fin n => ComposableHomType AHom obj deg i)
        (functorTargetType β_A β_B BHom F_objMap F_deg_trans obj deg))
    {n : ℕ}
    (obj : Fin (n + 1) → ObjA)
    (deg : Fin n → β_A)
    (c : Composition n)
    (l : Fin c.length) :
    MultilinearMap R
      (fun j => ComposableHomType AHom obj deg (c.embedding l j))
      (ComposableHomType BHom
        (functorCompositionOuterObj F_objMap obj c)
        (functorCompositionOuterDeg β_A β_B F_deg_trans deg c) l) :=
  letI : NeZero (c.blocksFun l) := ⟨Nat.ne_of_gt (c.one_le_blocksFun l)⟩
  cast
    (congrArg
      (fun M : ModuleCat R =>
        MultilinearMap R
          (fun j => ComposableHomType AHom obj deg (c.embedding l j))
          M)
      (comp_term_block_module_eq β_A β_B
        BHom F_objMap F_deg_trans obj deg c l))
    (F_phi (compositionBlockObj obj c l) (compositionBlockDeg β_A deg c l))

/-- The multilinear map for a single functor-composition term. -/
def compTermMultilinearMap
    (AHom : ObjA → ObjA → GradedRModule (β := β_A) (R := R))
    (BHom : ObjB → ObjB → GradedRModule (β := β_B) (R := R))
    (CHom : ObjC → ObjC → GradedRModule (β := β_C) (R := R))
    (F_objMap : ObjA → ObjB)
    (F_deg_trans : β_A →+ β_B)
    (F_phi :
      {n : ℕ} → [NeZero n] →
      (obj : Fin (n + 1) → ObjA) →
      (deg : Fin n → β_A) →
      MultilinearMap R
        (fun i : Fin n => ComposableHomType AHom obj deg i)
        (functorTargetType β_A β_B BHom F_objMap F_deg_trans obj deg))
    (G_objMap : ObjB → ObjC)
    (G_deg_trans : β_B →+ β_C)
    (G_deg_trans_ofInt : ∀ n : ℤ, G_deg_trans (Grading.ofInt n) = Grading.ofInt n)
    (G_phi :
      {n : ℕ} → [NeZero n] →
      (obj : Fin (n + 1) → ObjB) →
      (deg : Fin n → β_B) →
      MultilinearMap R
        (fun i : Fin n => ComposableHomType BHom obj deg i)
        (functorTargetType β_B β_C CHom G_objMap G_deg_trans obj deg))
    {n : ℕ} [NeZero n]
    (obj : Fin (n + 1) → ObjA)
    (deg : Fin n → β_A)
    (c : Composition n) :
    MultilinearMap R
      (fun i : Fin n => ComposableHomType AHom obj deg i)
      (functorTargetType β_A β_C CHom (G_objMap ∘ F_objMap)
        (G_deg_trans.comp F_deg_trans) obj deg) :=
  letI : NeZero c.length := ⟨Nat.ne_of_gt (c.length_pos_of_pos (Nat.pos_of_ne_zero (NeZero.ne n)))⟩
  cast
    (congrArg
      (fun M : ModuleCat R =>
        MultilinearMap R
          (fun i : Fin n => ComposableHomType AHom obj deg i)
          M)
      (comp_term_target_module_eq β_A β_B β_C
        CHom F_objMap F_deg_trans G_objMap G_deg_trans G_deg_trans_ofInt obj deg c))
    (MultilinearMap.compComposition c
      (G_phi
        (functorCompositionOuterObj F_objMap obj c)
        (functorCompositionOuterDeg β_A β_B F_deg_trans deg c))
      (compTermBlock β_A β_B
        AHom BHom F_objMap F_deg_trans F_phi obj deg c))

/-- The raw `n`-th component of the composite functor, obtained by summing the
composition terms over all ordered compositions of `n`. -/
def compPhi
    (AHom : ObjA → ObjA → GradedRModule (β := β_A) (R := R))
    (BHom : ObjB → ObjB → GradedRModule (β := β_B) (R := R))
    (CHom : ObjC → ObjC → GradedRModule (β := β_C) (R := R))
    (F_objMap : ObjA → ObjB)
    (F_deg_trans : β_A →+ β_B)
    (F_phi :
      {n : ℕ} → [NeZero n] →
      (obj : Fin (n + 1) → ObjA) →
      (deg : Fin n → β_A) →
      MultilinearMap R
        (fun i : Fin n => ComposableHomType AHom obj deg i)
        (functorTargetType β_A β_B BHom F_objMap F_deg_trans obj deg))
    (G_objMap : ObjB → ObjC)
    (G_deg_trans : β_B →+ β_C)
    (G_deg_trans_ofInt : ∀ n : ℤ, G_deg_trans (Grading.ofInt n) = Grading.ofInt n)
    (G_phi :
      {n : ℕ} → [NeZero n] →
      (obj : Fin (n + 1) → ObjB) →
      (deg : Fin n → β_B) →
      MultilinearMap R
        (fun i : Fin n => ComposableHomType BHom obj deg i)
        (functorTargetType β_B β_C CHom G_objMap G_deg_trans obj deg))
    {n : ℕ} [NeZero n]
    (obj : Fin (n + 1) → ObjA)
    (deg : Fin n → β_A) :
    MultilinearMap R
      (fun i : Fin n => ComposableHomType AHom obj deg i)
      (functorTargetType β_A β_C CHom (G_objMap ∘ F_objMap)
        (G_deg_trans.comp F_deg_trans) obj deg) :=
  ∑ c : Composition n,
    compTermMultilinearMap β_A β_B β_C
      AHom BHom CHom
      F_objMap F_deg_trans F_phi
      G_objMap G_deg_trans G_deg_trans_ofInt G_phi
      obj deg c

section StructureComposition

variable [RLinearGQuiver β_A R ObjA]
variable [RLinearGQuiver β_B R ObjB]
variable [RLinearGQuiver β_C R ObjC]

end StructureComposition

end AInfinityFunctorData

/-- Composition of raw `A∞` functor data, written in mathlib order so
`G.comp F` is the composite `G ∘ F`. -/
protected abbrev AInfinityFunctorData.comp
    {β_A : Type v} [Grading β_A]
    {β_B : Type w} [Grading β_B]
    {β_C : Type x} [Grading β_C]
    {R : Type u} [CommRing R]
    {ObjA : Type y} {ObjB : Type z} {ObjC : Type t}
    [RLinearGQuiver β_A R ObjA]
    [RLinearGQuiver β_B R ObjB]
    [RLinearGQuiver β_C R ObjC]
    (G : AInfinityFunctorData (β_A := β_B) (β_B := β_C) R ObjB ObjC)
    (F : AInfinityFunctorData (β_A := β_A) (β_B := β_B) R ObjA ObjB) :
    AInfinityFunctorData (β_A := β_A) (β_B := β_C) R ObjA ObjC where
  objMap := G.objMap ∘ F.objMap
  deg_trans := G.deg_trans.comp F.deg_trans
  deg_trans_ofInt := fun n => by
    simp [AddMonoidHom.comp_apply, F.deg_trans_ofInt, G.deg_trans_ofInt]
  deg_trans_sign := fun b => by
    simp [AddMonoidHom.comp_apply, F.deg_trans_sign, G.deg_trans_sign]
  phi := fun obj deg =>
    AInfinityFunctorData.compPhi β_A β_B β_C
      (GHom β_A R) (GHom β_B R) (GHom β_C R)
      F.objMap F.deg_trans F.phi
      G.objMap G.deg_trans G.deg_trans_ofInt G.phi
      obj deg

/-! ## Basic properties of functor composition -/

namespace AInfinityFunctorData

section BasicProperties

variable {β_A : Type v} [Grading β_A]
variable {β_B : Type w} [Grading β_B]
variable {β_C : Type x} [Grading β_C]
variable {β_D : Type*} [Grading β_D]
variable {R : Type u} [CommRing R]
variable {ObjA : Type y} {ObjB : Type z} {ObjC : Type t} {ObjD : Type*}
variable [RLinearGQuiver β_A R ObjA]
variable [RLinearGQuiver β_B R ObjB]
variable [RLinearGQuiver β_C R ObjC]
variable [RLinearGQuiver β_D R ObjD]

/-- The left-bracketed `phi`-field after unfolding only the outermost composition.

This is the starting point for the associativity proof on the `phi`-field:
the proof should next expand `(G.comp F).phi` blockwise and then reindex the
resulting nested finite sum. -/
private abbrev compAssocLeftPhiExpanded
    (F : AInfinityFunctorData (β_A := β_A) (β_B := β_B) R ObjA ObjB)
    (G : AInfinityFunctorData (β_A := β_B) (β_B := β_C) R ObjB ObjC)
    (H : AInfinityFunctorData (β_A := β_C) (β_B := β_D) R ObjC ObjD) :
    {n : ℕ} → [NeZero n] →
      (obj : Fin (n + 1) → ObjA) →
      (deg : Fin n → β_A) →
      MultilinearMap R
        (fun i : Fin n => ComposableHomType (GHom β_A R) obj deg i)
        (functorTargetType β_A β_D (GHom β_D R)
          (H.objMap ∘ (G.comp F).objMap)
          (H.deg_trans.comp (G.comp F).deg_trans)
          obj deg) :=
  fun {n : ℕ} [_inst : NeZero n]
      (obj : Fin (n + 1) → ObjA)
      (deg : Fin n → β_A) =>
    compPhi β_A β_C β_D
      (GHom β_A R) (GHom β_C R) (GHom β_D R)
      (G.comp F).objMap
      (G.comp F).deg_trans
      (G.comp F).phi
      H.objMap
      H.deg_trans
      H.deg_trans_ofInt
      H.phi
      obj deg

/-- The right-bracketed `phi`-field after unfolding only the outermost composition.

This is the comparison target for the left-bracketed expansion.  After the
outermost unfolding, the proof should expand `(H.comp G).phi` inside each block
and compare the resulting doubly-indexed sum with the left-hand expansion. -/
private abbrev compAssocRightPhiExpanded
    (F : AInfinityFunctorData (β_A := β_A) (β_B := β_B) R ObjA ObjB)
    (G : AInfinityFunctorData (β_A := β_B) (β_B := β_C) R ObjB ObjC)
    (H : AInfinityFunctorData (β_A := β_C) (β_B := β_D) R ObjC ObjD) :
    {n : ℕ} → [NeZero n] →
      (obj : Fin (n + 1) → ObjA) →
      (deg : Fin n → β_A) →
      MultilinearMap R
        (fun i : Fin n => ComposableHomType (GHom β_A R) obj deg i)
        (functorTargetType β_A β_D (GHom β_D R)
          ((H.comp G).objMap ∘ F.objMap)
          ((H.comp G).deg_trans.comp F.deg_trans)
          obj deg) :=
  fun {n : ℕ} [_inst : NeZero n]
      (obj : Fin (n + 1) → ObjA)
      (deg : Fin n → β_A) =>
    compPhi β_A β_B β_D
      (GHom β_A R) (GHom β_B R) (GHom β_D R)
      F.objMap
      F.deg_trans
      F.phi
      (H.comp G).objMap
      (H.comp G).deg_trans
      (H.comp G).deg_trans_ofInt
      (H.comp G).phi
      obj deg

/-- First field of `comp_assoc`.

This should be proved by unfolding `AInfinityFunctorData.comp`,
then reducing to associativity of ordinary function composition. -/
private lemma comp_assoc_objMap
    (F : AInfinityFunctorData (β_A := β_A) (β_B := β_B) R ObjA ObjB)
    (G : AInfinityFunctorData (β_A := β_B) (β_B := β_C) R ObjB ObjC)
    (H : AInfinityFunctorData (β_A := β_C) (β_B := β_D) R ObjC ObjD) :
    (H.comp (G.comp F)).objMap = ((H.comp G).comp F).objMap := by
  sorry

/-- Second field of `comp_assoc`.

This is the degree-translation analogue of `comp_assoc_objMap`; the proof should
again just unfold the definitions and use associativity of `AddMonoidHom.comp`. -/
private lemma comp_assoc_deg_trans
    (F : AInfinityFunctorData (β_A := β_A) (β_B := β_B) R ObjA ObjB)
    (G : AInfinityFunctorData (β_A := β_B) (β_B := β_C) R ObjB ObjC)
    (H : AInfinityFunctorData (β_A := β_C) (β_B := β_D) R ObjC ObjD) :
    (H.comp (G.comp F)).deg_trans = ((H.comp G).comp F).deg_trans := by
  sorry

/-- Transport lemma for the `deg_trans_ofInt` field in `comp_assoc`.

This proof should use `comp_assoc_deg_trans` first, then reduce the remaining
goal to extensionality on `ℤ` followed by the defining formulas for `comp`. -/
private lemma comp_assoc_deg_trans_ofInt
    (F : AInfinityFunctorData (β_A := β_A) (β_B := β_B) R ObjA ObjB)
    (G : AInfinityFunctorData (β_A := β_B) (β_B := β_C) R ObjB ObjC)
    (H : AInfinityFunctorData (β_A := β_C) (β_B := β_D) R ObjC ObjD) :
    HEq (H.comp (G.comp F)).deg_trans_ofInt (((H.comp G).comp F).deg_trans_ofInt) := by
  sorry

/-- Transport lemma for the `deg_trans_sign` field in `comp_assoc`.

This should follow the same pattern as `comp_assoc_deg_trans_ofInt`: first use
`comp_assoc_deg_trans`, then prove pointwise equality of the parity formulas. -/
private lemma comp_assoc_deg_trans_sign
    (F : AInfinityFunctorData (β_A := β_A) (β_B := β_B) R ObjA ObjB)
    (G : AInfinityFunctorData (β_A := β_B) (β_B := β_C) R ObjB ObjC)
    (H : AInfinityFunctorData (β_A := β_C) (β_B := β_D) R ObjC ObjD) :
    HEq (H.comp (G.comp F)).deg_trans_sign (((H.comp G).comp F).deg_trans_sign) := by
  sorry

/-- Unfold the outermost composition on the left-hand side.

This lemma should be essentially definitional.  It is separated out so that the
actual combinatorial proof can work directly with `compAssocLeftPhiExpanded`. -/
private lemma comp_assoc_phi_expand_left
    (F : AInfinityFunctorData (β_A := β_A) (β_B := β_B) R ObjA ObjB)
    (G : AInfinityFunctorData (β_A := β_B) (β_B := β_C) R ObjB ObjC)
    (H : AInfinityFunctorData (β_A := β_C) (β_B := β_D) R ObjC ObjD)
    {n : ℕ} [NeZero n]
    (obj : Fin (n + 1) → ObjA)
    (deg : Fin n → β_A) :
    (H.comp (G.comp F)).phi obj deg = compAssocLeftPhiExpanded F G H obj deg := by
  sorry

/-- Unfold the outermost composition on the right-hand side.

This is the right-bracketed analogue of `comp_assoc_phi_expand_left`, and it
should also be essentially definitional after unfolding `comp`. -/
private lemma comp_assoc_phi_expand_right
    (F : AInfinityFunctorData (β_A := β_A) (β_B := β_B) R ObjA ObjB)
    (G : AInfinityFunctorData (β_A := β_B) (β_B := β_C) R ObjB ObjC)
    (H : AInfinityFunctorData (β_A := β_C) (β_B := β_D) R ObjC ObjD)
    {n : ℕ} [NeZero n]
    (obj : Fin (n + 1) → ObjA)
    (deg : Fin n → β_A) :
    ((H.comp G).comp F).phi obj deg = compAssocRightPhiExpanded F G H obj deg := by
  sorry

/-- Core combinatorial reindexing step for associativity of the `phi`-field.

Suggested proof structure for the agent that fills this in:
1. Expand `compAssocLeftPhiExpanded` into a nested sum indexed by an outer
   composition of `n` together with a composition of each outer block.
2. Expand `compAssocRightPhiExpanded` into a nested sum indexed by a
   composition of `n` together with a composition of the resulting block list.
3. Build the bijection between those two indexing types.
4. Show the corresponding summands agree term-by-term.

The final `comp_assoc_phi` lemma below should use this lemma together with the
two one-step unfolding lemmas, and not re-do any of the bookkeeping. -/
private lemma comp_assoc_phi_reindex
    (F : AInfinityFunctorData (β_A := β_A) (β_B := β_B) R ObjA ObjB)
    (G : AInfinityFunctorData (β_A := β_B) (β_B := β_C) R ObjB ObjC)
    (H : AInfinityFunctorData (β_A := β_C) (β_B := β_D) R ObjC ObjD)
    {n : ℕ} [NeZero n]
    (obj : Fin (n + 1) → ObjA)
    (deg : Fin n → β_A) :
    compAssocLeftPhiExpanded F G H obj deg =
      compAssocRightPhiExpanded F G H obj deg := by
  sorry

/-- Agreement of the `phi`-fields for the two bracketings of triple composition.

This should be proved only by chaining
`comp_assoc_phi_expand_left`, `comp_assoc_phi_reindex`, and
`comp_assoc_phi_expand_right`. -/
private lemma comp_assoc_phi
    (F : AInfinityFunctorData (β_A := β_A) (β_B := β_B) R ObjA ObjB)
    (G : AInfinityFunctorData (β_A := β_B) (β_B := β_C) R ObjB ObjC)
    (H : AInfinityFunctorData (β_A := β_C) (β_B := β_D) R ObjC ObjD)
    {n : ℕ} [NeZero n]
    (obj : Fin (n + 1) → ObjA)
    (deg : Fin n → β_A) :
    (H.comp (G.comp F)).phi obj deg = ((H.comp G).comp F).phi obj deg := by
  -- Suggested proof:
  -- 1. Rewrite the left-hand side using `comp_assoc_phi_expand_left`.
  -- 2. Apply `comp_assoc_phi_reindex` to identify the two expanded formulas.
  -- 3. Rewrite back to the right-hand side using `comp_assoc_phi_expand_right`.
  --
  -- Depending on how the reindexing lemma is proved, a small transport/cast
  -- lemma may be useful here to align the codomains of the two expanded maps.
  sorry

/-- Raw `A∞` functor composition is associative. -/
theorem comp_assoc
    (F : AInfinityFunctorData (β_A := β_A) (β_B := β_B) R ObjA ObjB)
    (G : AInfinityFunctorData (β_A := β_B) (β_B := β_C) R ObjB ObjC)
    (H : AInfinityFunctorData (β_A := β_C) (β_B := β_D) R ObjC ObjD) :
    H.comp (G.comp F) = (H.comp G).comp F := by
  -- Final proof plan:
  -- 1. Use the structure extensionality theorem for `AInfinityFunctorData`.
  -- 2. Solve the `objMap` and `deg_trans` fields with
  --      `comp_assoc_objMap` and `comp_assoc_deg_trans`.
  -- 3. Solve the dependent proof fields with
  --      `comp_assoc_deg_trans_ofInt`, `comp_assoc_deg_trans_sign`,
  --      and `comp_assoc_phi`.
  --
  -- Keeping the final assembly as a separate `sorry` makes it easy for a
  -- proving agent to focus on the structure equality only after the helper
  -- lemmas above have been filled in.
  sorry

end BasicProperties
end AInfinityFunctorData

namespace AInfinityFunctor

section BasicProperties

variable {β_A : Type v} [Grading β_A]
variable {β_B : Type w} [Grading β_B]
variable {β_C : Type x} [Grading β_C]
variable {R : Type u} [CommRing R]
variable {ObjA : Type y} {ObjB : Type z} {ObjC : Type t}
variable [AInfinityCategory β_A R ObjA]
variable [AInfinityCategory β_B R ObjB]
variable [AInfinityCategory β_C R ObjC]

/-- The composition of two `A∞` functors again satisfies the functor equations. -/
theorem comp_satisfies_functor_equations
    (F : AInfinityFunctor (β_A := β_A) (β_B := β_B) R ObjA ObjB)
    (G : AInfinityFunctor (β_A := β_B) (β_B := β_C) R ObjB ObjC) :
    AInfinityFunctorData.SatisfiesFunctorEquations
      (β_A := β_A) (β_B := β_C) R ObjA ObjC
      (G.toAInfinityFunctorData.comp F.toAInfinityFunctorData) := by
  sorry

end BasicProperties
end AInfinityFunctor

/-- Composition of `A∞` functors, written in mathlib order so
`G.comp F` is the composite `G ∘ F`. -/
protected abbrev AInfinityFunctor.comp
    {β_A : Type v} [Grading β_A]
    {β_B : Type w} [Grading β_B]
    {β_C : Type x} [Grading β_C]
    {R : Type u} [CommRing R]
    {ObjA : Type y} {ObjB : Type z} {ObjC : Type t}
    [AInfinityCategory β_A R ObjA]
    [AInfinityCategory β_B R ObjB]
    [AInfinityCategory β_C R ObjC]
    (G : AInfinityFunctor (β_A := β_B) (β_B := β_C) R ObjB ObjC)
    (F : AInfinityFunctor (β_A := β_A) (β_B := β_B) R ObjA ObjB) :
    AInfinityFunctor (β_A := β_A) (β_B := β_C) R ObjA ObjC where
  toAInfinityFunctorData := G.toAInfinityFunctorData.comp F.toAInfinityFunctorData
  satisfiesFunctorEquations := AInfinityFunctor.comp_satisfies_functor_equations F G

end AInfinityTheory
