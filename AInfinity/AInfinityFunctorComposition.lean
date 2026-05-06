module

public import Mathlib
public import AInfinity.Grading
public import AInfinity.AInfinityFunctor

@[expose] public section

open CategoryTheory AInfinityTheory

noncomputable section

namespace AInfinityTheory

universe u v w x y z t

variable (β_A : Type v) [GradingIndex β_A]
variable (β_B : Type w) [GradingIndex β_B]
variable (β_C : Type x) [GradingIndex β_C]

namespace AInfinityFunctorData

variable {R : Type u} [CommRing R]
variable {ObjA : Type y} {ObjB : Type z} {ObjC : Type t}

/-! ## Raw A∞ functor composition -/

/-- Applying the outer degree translation to the block outputs of `F`
recovers the target degree of the composite component. -/
lemma comp_compatible_deg
    (F_deg_trans : β_A →+ β_B)
    (G_deg_trans : β_B →+ β_C)
    (G_deg_trans_ofInt : ∀ n : ℤ, G_deg_trans (GradingIndex.ofInt n) = GradingIndex.ofInt n)
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
    simp? +decide [Finset.sum_add_distrib]
    have h_sum_deg_comp :
        ∑ x : Fin c.length, ∑ i : Fin (c.blocksFun x),
          (G_deg_trans.comp F_deg_trans) (deg (c.embedding x i)) =
        ∑ i : Fin n, (G_deg_trans.comp F_deg_trans) (deg i) := by
      have h_sum_deg_comp :
          Finset.biUnion (Finset.univ : Finset (Fin c.length))
            (fun l => Finset.image (fun j => c.embedding l j) Finset.univ) =
          Finset.univ := by
        ext i
        simp? [Finset.mem_biUnion, Finset.mem_image]
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
    simp? +decide [Finset.sum_sub_distrib]
    exact_mod_cast c.sum_blocksFun
  generalize_proofs at *
  simp? +decide [← h_shift_sum, add_assoc, shift_ofInt]
  simp +decide [← map_nsmul]

/-- Transport from the outer target of a composition term to the target of the
composite functor component. -/
lemma comp_term_target_module_eq
    (CHom : ObjC → ObjC → GradedRModule (β := β_C) (R := R))
    (F_objMap : ObjA → ObjB)
    (F_deg_trans : β_A →+ β_B)
    (G_objMap : ObjB → ObjC)
    (G_deg_trans : β_B →+ β_C)
    (G_deg_trans_ofInt : ∀ n : ℤ, G_deg_trans (GradingIndex.ofInt n) = GradingIndex.ofInt n)
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
    (G_deg_trans_ofInt : ∀ n : ℤ, G_deg_trans (GradingIndex.ofInt n) = GradingIndex.ofInt n)
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
    (G_deg_trans_ofInt : ∀ n : ℤ, G_deg_trans (GradingIndex.ofInt n) = GradingIndex.ofInt n)
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
    {β_A : Type v} [GradingIndex β_A]
    {β_B : Type w} [GradingIndex β_B]
    {β_C : Type x} [GradingIndex β_C]
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

variable {β_A : Type v} [GradingIndex β_A]
variable {β_B : Type w} [GradingIndex β_B]
variable {β_C : Type x} [GradingIndex β_C]
variable {β_D : Type*} [GradingIndex β_D]
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
  rfl

/-- Second field of `comp_assoc`.

This is the degree-translation analogue of `comp_assoc_objMap`; the proof should
again just unfold the definitions and use associativity of `AddMonoidHom.comp`. -/
private lemma comp_assoc_deg_trans
    (F : AInfinityFunctorData (β_A := β_A) (β_B := β_B) R ObjA ObjB)
    (G : AInfinityFunctorData (β_A := β_B) (β_B := β_C) R ObjB ObjC)
    (H : AInfinityFunctorData (β_A := β_C) (β_B := β_D) R ObjC ObjD) :
    (H.comp (G.comp F)).deg_trans = ((H.comp G).comp F).deg_trans := by
  rfl

/-- Transport lemma for the `deg_trans_ofInt` field in `comp_assoc`.

This proof should use `comp_assoc_deg_trans` first, then reduce the remaining
goal to extensionality on `ℤ` followed by the defining formulas for `comp`. -/
private lemma comp_assoc_deg_trans_ofInt
    (F : AInfinityFunctorData (β_A := β_A) (β_B := β_B) R ObjA ObjB)
    (G : AInfinityFunctorData (β_A := β_B) (β_B := β_C) R ObjB ObjC)
    (H : AInfinityFunctorData (β_A := β_C) (β_B := β_D) R ObjC ObjD) :
    HEq (H.comp (G.comp F)).deg_trans_ofInt (((H.comp G).comp F).deg_trans_ofInt) := by
  rfl

/-- Transport lemma for the `deg_trans_sign` field in `comp_assoc`.

This should follow the same pattern as `comp_assoc_deg_trans_ofInt`: first use
`comp_assoc_deg_trans`, then prove pointwise equality of the parity formulas. -/
private lemma comp_assoc_deg_trans_sign
    (F : AInfinityFunctorData (β_A := β_A) (β_B := β_B) R ObjA ObjB)
    (G : AInfinityFunctorData (β_A := β_B) (β_B := β_C) R ObjB ObjC)
    (H : AInfinityFunctorData (β_A := β_C) (β_B := β_D) R ObjC ObjD) :
    HEq (H.comp (G.comp F)).deg_trans_sign (((H.comp G).comp F).deg_trans_sign) := by
  rfl

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
  rfl

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
  rfl

/-- Applying a multilinear map transported along a codomain equality transports
the resulting value along the same equality. -/
private lemma multilinearMap_cast_apply
    {ι : Type*} [DecidableEq ι] [Fintype ι]
    {M₁ : ι → Type u} [∀ i, AddCommMonoid (M₁ i)] [∀ i, Module R (M₁ i)]
    {M₂ M₂' : ModuleCat.{u} R}
    (h : M₂ = M₂')
    (f : MultilinearMap R M₁ M₂)
    (x : ∀ i, M₁ i) :
    (cast (congrArg (fun M : ModuleCat R => MultilinearMap R M₁ M) h) f) x =
      cast (congrArg (fun M : ModuleCat R => (M : Type u)) h) (f x) := by
  subst h
  rfl

/-- Transporting a finite sum across an equality of `ModuleCat` objects is the
same as summing the transported terms. -/
private lemma cast_sum_of_module_eq
    {M N : ModuleCat.{u} R}
    (h : M = N)
    {α : Type*} [Fintype α]
    (f : α → M) :
    cast (congrArg (fun X : ModuleCat R => (X : Type u)) h) (∑ a, f a) =
      ∑ a, cast (congrArg (fun X : ModuleCat R => (X : Type u)) h) (f a) := by
  subst h
  rfl

/-- Transporting a finite sum of multilinear maps across a codomain equality is
the same as summing the transported multilinear maps. -/
private lemma cast_multilinearMap_sum
    {ι : Type*} [DecidableEq ι] [Fintype ι]
    {M₁ : ι → Type u} [∀ i, AddCommMonoid (M₁ i)] [∀ i, Module R (M₁ i)]
    {M₂ M₂' : ModuleCat.{u} R}
    (h : M₂ = M₂')
    {α : Type*} [Fintype α]
    (f : α → MultilinearMap R M₁ M₂) :
    cast (congrArg (fun M : ModuleCat R => MultilinearMap R M₁ M) h) (∑ a, f a) =
      ∑ a, cast (congrArg (fun M : ModuleCat R => MultilinearMap R M₁ M) h) (f a) := by
  subst h
  rfl

/-- Transport a functor component across equal arities, objects, degrees, and
inputs.

This is the dependent congruence principle needed when reindexing nested
composition terms: once the arity, object string, degree string, and input
tuple have been identified, the corresponding `phi` values are heterogeneously
equal. -/
private lemma phi_heq_of_arity_eq
    (F : AInfinityFunctorData (β_A := β_A) (β_B := β_B) R ObjA ObjB)
    {n₁ n₂ : ℕ} {inst₁ : NeZero n₁} {inst₂ : NeZero n₂}
    (hn : n₁ = n₂)
    {O₁ : Fin (n₁ + 1) → ObjA} {O₂ : Fin (n₂ + 1) → ObjA}
    {D₁ : Fin n₁ → β_A} {D₂ : Fin n₂ → β_A}
    (hO : HEq O₁ O₂) (hD : HEq D₁ D₂)
    (X₁ : ∀ i, ComposableHomType (GHom β_A R) O₁ D₁ i)
    (X₂ : ∀ i, ComposableHomType (GHom β_A R) O₂ D₂ i)
    (hX : HEq X₁ X₂) :
    HEq (@AInfinityFunctorData.phi β_A _ β_B _ R _ ObjA ObjB _ _ F n₁ inst₁ O₁ D₁ X₁)
      (@AInfinityFunctorData.phi β_A _ β_B _ R _ ObjA ObjB _ _ F n₂ inst₂ O₂ D₂ X₂) := by
  cases inst₁
  cases inst₂
  aesop

/-- Transport `functorTargetDeg` across equal arities and heterogeneously equal
degree strings. -/
private lemma functorTargetDeg_heq_of_arity_eq
    (deg_trans : β_A →+ β_B)
    {n₁ n₂ : ℕ}
    (hn : n₁ = n₂)
    {D₁ : Fin n₁ → β_A} {D₂ : Fin n₂ → β_A}
    (hD : HEq D₁ D₂) :
    HEq (functorTargetDeg β_A β_B deg_trans D₁)
      (functorTargetDeg β_A β_B deg_trans D₂) := by
  subst hn
  have hD' := eq_of_heq hD
  subst hD'
  rfl

/-- Boundary positions agree when a block of `a.gather b` is viewed as the
corresponding consecutive family of blocks of `a`. -/
private lemma comp_assoc_sizeUpTo_boundary_eq
    {n : ℕ}
    (a : Composition n)
    (b : Composition a.length)
    (j : Fin b.length)
    (q : Fin (b.blocksFun j + 1)) :
    a.sizeUpTo (b.sizeUpTo j.val + q.val) =
      (a.gather b).sizeUpTo j.val +
        (a.sigmaCompositionAux b
          ⟨j.val, (Composition.length_gather a b).symm ▸ j.2⟩).sizeUpTo q.val := by
  by_cases hq : q.val < b.blocksFun j
  · simpa using
      Composition.sizeUpTo_sizeUpTo_add a b (i := j.val) (j := q.val) j.2 hq
  · have hqeq : q.val = b.blocksFun j := by omega
    rw [hqeq]
    have hleft :
        a.sizeUpTo (b.sizeUpTo j.val + b.blocksFun j) =
          (a.gather b).sizeUpTo (j.val + 1) := by
      rw [← b.sizeUpTo_succ' j]
      by_cases hnext : j.val + 1 < b.length
      · have h :=
          Composition.sizeUpTo_sizeUpTo_add a b (i := j.val + 1) (j := 0) hnext
            (show 0 < b.blocksFun ⟨j.val + 1, hnext⟩ from
              lt_of_lt_of_le Nat.zero_lt_one (b.one_le_blocksFun ⟨j.val + 1, hnext⟩))
        simpa using h
      · have hend : j.val + 1 = b.length := by omega
        have hglen : (a.gather b).length = b.length := Composition.length_gather a b
        rw [hend, b.sizeUpTo_length, a.sizeUpTo_length, ← hglen,
          (a.gather b).sizeUpTo_length]
    have hsigma :
        (a.sigmaCompositionAux b
          ⟨j.val, (Composition.length_gather a b).symm ▸ j.2⟩).sizeUpTo
            (b.blocksFun j) =
          (a.gather b).blocksFun
            ⟨j.val, (Composition.length_gather a b).symm ▸ j.2⟩ := by
      rw [← Composition.length_sigmaCompositionAux a b j]
      exact (a.sigmaCompositionAux b
        ⟨j.val, (Composition.length_gather a b).symm ▸ j.2⟩).sizeUpTo_length
    rw [hsigma]
    rw [← (a.gather b).sizeUpTo_succ'
      ⟨j.val, (Composition.length_gather a b).symm ▸ j.2⟩]
    exact hleft

/-- Nested embeddings through `sigmaCompositionAux` recover the original
embedding through `a`. -/
private lemma comp_assoc_embedding_eq
    {n : ℕ}
    (a : Composition n)
    (b : Composition a.length)
    (j : Fin b.length)
    {p : Fin
      (a.sigmaCompositionAux b
        ⟨j.val, (Composition.length_gather a b).symm ▸ j.2⟩).length}
    {q : Fin (b.blocksFun j)}
    (hpq : HEq p q)
    {r : Fin
      ((a.sigmaCompositionAux b
        ⟨j.val, (Composition.length_gather a b).symm ▸ j.2⟩).blocksFun p)}
    {s : Fin (a.blocksFun (b.embedding j q))}
    (hrs : HEq r s) :
    (a.gather b).embedding
        ⟨j.val, (Composition.length_gather a b).symm ▸ j.2⟩
        ((a.sigmaCompositionAux b
          ⟨j.val, (Composition.length_gather a b).symm ▸ j.2⟩).embedding p r) =
      a.embedding (b.embedding j q) s := by
  have hdom :
      (a.sigmaCompositionAux b
        ⟨j.val, (Composition.length_gather a b).symm ▸ j.2⟩).length =
        b.blocksFun j :=
    Composition.length_sigmaCompositionAux a b j
  have hpval : p.val = q.val := (Fin.heq_ext_iff hdom).mp hpq
  have hp :
      p =
        ⟨q.val, (Composition.length_sigmaCompositionAux a b j).symm ▸ q.2⟩ :=
    Fin.ext hpval
  subst p
  have hblocks :
      (a.sigmaCompositionAux b
        ⟨j.val, (Composition.length_gather a b).symm ▸ j.2⟩).blocksFun
          ⟨q.val, (Composition.length_sigmaCompositionAux a b j).symm ▸ q.2⟩ =
        a.blocksFun (b.embedding j q) :=
    Composition.blocksFun_sigmaCompositionAux a b j q
  have hrsval : r.val = s.val := (Fin.heq_ext_iff hblocks).mp hrs
  apply Fin.ext
  have hsize :=
    Composition.sizeUpTo_sizeUpTo_add a b (i := j.val) (j := q.val) j.2 q.2
  simp [Composition.coe_embedding, hsize, hrsval, Nat.add_assoc]

/-- The object string for the `j`-th block after gathering agrees with the
object string obtained by first applying the outer object string for `a` and
then taking the `j`-th block of `b`. -/
private lemma comp_assoc_inner_outer_obj_heq
    {n : ℕ}
    (F_objMap : ObjA → ObjB)
    (obj : Fin (n + 1) → ObjA)
    (a : Composition n)
    (b : Composition a.length)
    (j : Fin b.length) :
    HEq
      (functorCompositionOuterObj F_objMap
        (compositionBlockObj obj (a.gather b)
          ⟨j.val, (Composition.length_gather a b).symm ▸ j.2⟩)
        (a.sigmaCompositionAux b
          ⟨j.val, (Composition.length_gather a b).symm ▸ j.2⟩))
      (compositionBlockObj (functorCompositionOuterObj F_objMap obj a) b j) := by
  have hlen :
      (a.sigmaCompositionAux b
        ⟨j.val, (Composition.length_gather a b).symm ▸ j.2⟩).length + 1 =
        b.blocksFun j + 1 := by
    rw [Composition.length_sigmaCompositionAux a b j]
  apply Function.hfunext (congrArg Fin hlen)
  intro p q hpq
  apply heq_of_eq
  have hpval : p.val = q.val := (Fin.heq_ext_iff hlen).mp hpq
  dsimp [functorCompositionOuterObj, compositionBlockObj]
  apply congrArg F_objMap
  apply congrArg obj
  apply Fin.ext
  dsimp [Composition.boundary]
  rw [hpval]
  exact (comp_assoc_sizeUpTo_boundary_eq a b j q).symm

/-- The degree string for the `j`-th gathered block agrees with the block of
the degree string produced by the first composition `a`. -/
private lemma comp_assoc_inner_outer_deg_heq
    {n : ℕ}
    (F_deg_trans : β_A →+ β_B)
    (deg : Fin n → β_A)
    (a : Composition n)
    (b : Composition a.length)
    (j : Fin b.length) :
    HEq
      (functorCompositionOuterDeg β_A β_B F_deg_trans
        (compositionBlockDeg β_A deg (a.gather b)
          ⟨j.val, (Composition.length_gather a b).symm ▸ j.2⟩)
        (a.sigmaCompositionAux b
          ⟨j.val, (Composition.length_gather a b).symm ▸ j.2⟩))
      (compositionBlockDeg β_B
        (functorCompositionOuterDeg β_A β_B F_deg_trans deg a) b j) := by
  have hdom :
      (a.sigmaCompositionAux b
        ⟨j.val, (Composition.length_gather a b).symm ▸ j.2⟩).length =
        b.blocksFun j :=
    Composition.length_sigmaCompositionAux a b j
  apply Function.hfunext (congrArg Fin hdom)
  intro p q hpq
  have hpval : p.val = q.val := (Fin.heq_ext_iff hdom).mp hpq
  have hp :
      p =
        ⟨q.val, (Composition.length_sigmaCompositionAux a b j).symm ▸ q.2⟩ :=
    Fin.ext hpval
  subst p
  have hblocks :
      (a.sigmaCompositionAux b
        ⟨j.val, (Composition.length_gather a b).symm ▸ j.2⟩).blocksFun
          ⟨q.val, (Composition.length_sigmaCompositionAux a b j).symm ▸ q.2⟩ =
        a.blocksFun (b.embedding j q) :=
    Composition.blocksFun_sigmaCompositionAux a b j q
  refine functorTargetDeg_heq_of_arity_eq F_deg_trans hblocks ?_
  apply Function.hfunext (congrArg Fin hblocks)
  intro r s hrs
  apply heq_of_eq
  apply congrArg deg
  exact comp_assoc_embedding_eq a b j hpq hrs

/-- Multi-composition is additive in the outer multilinear map. -/
private lemma compComposition_sum_outer
    {S : Type*} [CommSemiring S]
    {n : ℕ} (c : Composition n)
    {M : Fin n → Type*} {N : Fin c.length → Type*} {P : Type*}
    [∀ i, AddCommMonoid (M i)] [∀ l, AddCommMonoid (N l)] [AddCommMonoid P]
    [∀ i, Module S (M i)] [∀ l, Module S (N l)] [Module S P]
    {α : Type*} [Fintype α]
    (g : α → MultilinearMap S N P)
    (f : (l : Fin c.length) → MultilinearMap S (fun j => M (c.embedding l j)) (N l)) :
    MultilinearMap.compComposition c (∑ a, g a) f =
      ∑ a, MultilinearMap.compComposition c (g a) f := by
  ext x
  simp [MultilinearMap.compComposition]

/-- Multi-composition expands over finite sums in every inner block. -/
private lemma compComposition_sum_inner
    {S : Type*} [CommSemiring S]
    {n : ℕ} (c : Composition n)
    {M : Fin n → Type*} {N : Fin c.length → Type*} {P : Type*}
    [∀ i, AddCommMonoid (M i)] [∀ l, AddCommMonoid (N l)] [AddCommMonoid P]
    [∀ i, Module S (M i)] [∀ l, Module S (N l)] [Module S P]
    (g : MultilinearMap S N P)
    {α : Fin c.length → Type*} [∀ l, Fintype (α l)]
    (f :
      (l : Fin c.length) → α l →
        MultilinearMap S (fun j => M (c.embedding l j)) (N l)) :
    MultilinearMap.compComposition c g (fun l => ∑ a, f l a) =
      ∑ choice : (l : Fin c.length) → α l,
        MultilinearMap.compComposition c g (fun l => f l (choice l)) := by
  ext x
  simp [MultilinearMap.compComposition, MultilinearMap.map_sum]

/-- Indexing data for the fully expanded left bracketing.

An element consists of the outer `H`-composition of the original inputs together
with, for each outer block, the inner composition used to expand `(G.comp F)`. -/
private abbrev compAssocLeftIndex (n : ℕ) : Type :=
  Σ c : Composition n, (l : Fin c.length) → Composition (c.blocksFun l)

/-- Indexing data for the fully expanded right bracketing.

An element consists of the first `F`-composition of the original inputs together
with the composition used to expand `(H.comp G)` on the resulting list. -/
private abbrev compAssocRightIndex (n : ℕ) : Type :=
  Σ c : Composition n, Composition c.length

/-- The selected expansion of a single `(G.comp F)` block inside the left
bracketing. -/
private def compAssocLeftIndexedBlock
    (F : AInfinityFunctorData (β_A := β_A) (β_B := β_B) R ObjA ObjB)
    (G : AInfinityFunctorData (β_A := β_B) (β_B := β_C) R ObjB ObjC)
    {n : ℕ} [NeZero n]
    (obj : Fin (n + 1) → ObjA)
    (deg : Fin n → β_A)
    (c : Composition n)
    (l : Fin c.length)
    (d : Composition (c.blocksFun l)) :
    MultilinearMap R
      (fun j => ComposableHomType (GHom β_A R) obj deg (c.embedding l j))
      (ComposableHomType (GHom β_C R)
        (functorCompositionOuterObj (G.comp F).objMap obj c)
        (functorCompositionOuterDeg β_A β_C (G.comp F).deg_trans deg c) l) := by
  letI : NeZero (c.blocksFun l) :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one (c.one_le_blocksFun l))⟩
  exact
    cast
      (congrArg
        (fun M : ModuleCat R =>
          MultilinearMap R
            (fun j => ComposableHomType (GHom β_A R) obj deg (c.embedding l j))
            M)
        (comp_term_block_module_eq β_A β_C
          (GHom β_C R) (G.comp F).objMap (G.comp F).deg_trans obj deg c l))
      (compTermMultilinearMap β_A β_B β_C
        (GHom β_A R) (GHom β_B R) (GHom β_C R)
        F.objMap F.deg_trans F.phi
        G.objMap G.deg_trans G.deg_trans_ofInt G.phi
        (compositionBlockObj obj c l) (compositionBlockDeg β_A deg c l) d)

/-- The selected summand in the fully expanded left bracketing.

This is the term obtained by choosing one outer `H`-composition and one
expansion of `(G.comp F)` inside every outer block. -/
private def compAssocLeftIndexedTerm
    (F : AInfinityFunctorData (β_A := β_A) (β_B := β_B) R ObjA ObjB)
    (G : AInfinityFunctorData (β_A := β_B) (β_B := β_C) R ObjB ObjC)
    (H : AInfinityFunctorData (β_A := β_C) (β_B := β_D) R ObjC ObjD)
    {n : ℕ} [NeZero n]
    (obj : Fin (n + 1) → ObjA)
    (deg : Fin n → β_A)
    (I : compAssocLeftIndex n) :
    MultilinearMap R
      (fun i : Fin n => ComposableHomType (GHom β_A R) obj deg i)
      (functorTargetType β_A β_D (GHom β_D R)
        (H.objMap ∘ (G.comp F).objMap)
        (H.deg_trans.comp (G.comp F).deg_trans)
        obj deg) := by
  classical
  rcases I with ⟨c, d⟩
  letI : NeZero c.length :=
    ⟨Nat.ne_of_gt (c.length_pos_of_pos (Nat.pos_of_ne_zero (NeZero.ne n)))⟩
  exact
    cast
      (congrArg
        (fun M : ModuleCat R =>
          MultilinearMap R
            (fun i : Fin n => ComposableHomType (GHom β_A R) obj deg i)
            M)
        (comp_term_target_module_eq β_A β_C β_D
          (GHom β_D R) (G.comp F).objMap (G.comp F).deg_trans
          H.objMap H.deg_trans H.deg_trans_ofInt obj deg c))
      (MultilinearMap.compComposition c
        (H.phi
          (functorCompositionOuterObj (G.comp F).objMap obj c)
          (functorCompositionOuterDeg β_A β_C (G.comp F).deg_trans deg c))
        (fun l => compAssocLeftIndexedBlock F G obj deg c l (d l)))

/-- The selected summand in the fully expanded right bracketing.

This is the term obtained by choosing the first `F`-composition of the original
inputs and one expansion of `(H.comp G)` on the list of resulting `F`-outputs. -/
private def compAssocRightIndexedTerm
    (F : AInfinityFunctorData (β_A := β_A) (β_B := β_B) R ObjA ObjB)
    (G : AInfinityFunctorData (β_A := β_B) (β_B := β_C) R ObjB ObjC)
    (H : AInfinityFunctorData (β_A := β_C) (β_B := β_D) R ObjC ObjD)
    {n : ℕ} [NeZero n]
    (obj : Fin (n + 1) → ObjA)
    (deg : Fin n → β_A)
    (I : compAssocRightIndex n) :
    MultilinearMap R
      (fun i : Fin n => ComposableHomType (GHom β_A R) obj deg i)
      (functorTargetType β_A β_D (GHom β_D R)
        ((H.comp G).objMap ∘ F.objMap)
        ((H.comp G).deg_trans.comp F.deg_trans)
        obj deg) := by
  classical
  rcases I with ⟨c, d⟩
  letI : NeZero c.length :=
    ⟨Nat.ne_of_gt (c.length_pos_of_pos (Nat.pos_of_ne_zero (NeZero.ne n)))⟩
  exact
    cast
      (congrArg
        (fun M : ModuleCat R =>
          MultilinearMap R
            (fun i : Fin n => ComposableHomType (GHom β_A R) obj deg i)
            M)
        (comp_term_target_module_eq β_A β_B β_D
          (GHom β_D R) F.objMap F.deg_trans
          (H.comp G).objMap (H.comp G).deg_trans (H.comp G).deg_trans_ofInt
          obj deg c))
      (MultilinearMap.compComposition c
        (compTermMultilinearMap β_B β_C β_D
          (GHom β_B R) (GHom β_C R) (GHom β_D R)
          G.objMap G.deg_trans G.phi
          H.objMap H.deg_trans H.deg_trans_ofInt H.phi
          (functorCompositionOuterObj F.objMap obj c)
          (functorCompositionOuterDeg β_A β_B F.deg_trans deg c)
          d)
        (compTermBlock β_A β_B
          (GHom β_A R) (GHom β_B R)
          F.objMap F.deg_trans F.phi obj deg c))

/-- The combinatorial bijection between the two ways of recording a two-level
refinement of an ordered composition. -/
private noncomputable def compAssocIndexEquiv (n : ℕ) :
    compAssocLeftIndex n ≃ compAssocRightIndex n :=
  (Composition.sigmaEquivSigmaPi n).symm

/-- Expanding a single `(G.comp F)` block gives the sum over compositions of
that block. -/
private lemma comp_assoc_left_block_indexed_sum
    (F : AInfinityFunctorData (β_A := β_A) (β_B := β_B) R ObjA ObjB)
    (G : AInfinityFunctorData (β_A := β_B) (β_B := β_C) R ObjB ObjC)
    {n : ℕ} [NeZero n]
    (obj : Fin (n + 1) → ObjA)
    (deg : Fin n → β_A)
    (c : Composition n)
    (l : Fin c.length) :
    compTermBlock β_A β_C
      (GHom β_A R) (GHom β_C R)
      (G.comp F).objMap (G.comp F).deg_trans (G.comp F).phi
      obj deg c l =
      ∑ d : Composition (c.blocksFun l),
        compAssocLeftIndexedBlock F G obj deg c l d := by
  classical
  letI : NeZero (c.blocksFun l) := ⟨Nat.ne_of_gt (c.one_le_blocksFun l)⟩
  unfold compAssocLeftIndexedBlock compTermBlock
  simp only [AInfinityFunctorData.comp, compPhi]
  exact cast_multilinearMap_sum
    (h := comp_term_block_module_eq β_A β_C
      (GHom β_C R) (G.objMap ∘ F.objMap) (G.deg_trans.comp F.deg_trans) obj deg c l)
    (f := fun d : Composition (c.blocksFun l) =>
      compTermMultilinearMap β_A β_B β_C
        (GHom β_A R) (GHom β_B R) (GHom β_C R)
        F.objMap F.deg_trans F.phi
        G.objMap G.deg_trans G.deg_trans_ofInt G.phi
        (compositionBlockObj obj c l) (compositionBlockDeg β_A deg c l) d)

/-- For a fixed outer `H`-composition, expanding every `(G.comp F)` block
gives the sum over a choice of inner composition in each block. -/
private lemma comp_assoc_left_outer_term_indexed_sum
    (F : AInfinityFunctorData (β_A := β_A) (β_B := β_B) R ObjA ObjB)
    (G : AInfinityFunctorData (β_A := β_B) (β_B := β_C) R ObjB ObjC)
    (H : AInfinityFunctorData (β_A := β_C) (β_B := β_D) R ObjC ObjD)
    {n : ℕ} [NeZero n]
    (obj : Fin (n + 1) → ObjA)
    (deg : Fin n → β_A)
    (c : Composition n) :
    compTermMultilinearMap β_A β_C β_D
      (GHom β_A R) (GHom β_C R) (GHom β_D R)
      (G.comp F).objMap (G.comp F).deg_trans (G.comp F).phi
      H.objMap H.deg_trans H.deg_trans_ofInt H.phi
      obj deg c =
      ∑ d : (l : Fin c.length) → Composition (c.blocksFun l),
        compAssocLeftIndexedTerm F G H obj deg ⟨c, d⟩ := by
  classical
  unfold compAssocLeftIndexedTerm compTermMultilinearMap
  rw [show
      compTermBlock β_A β_C
        (GHom β_A R) (GHom β_C R)
        (G.comp F).objMap (G.comp F).deg_trans (G.comp F).phi
        obj deg c =
        (fun l => ∑ d : Composition (c.blocksFun l),
          compAssocLeftIndexedBlock F G obj deg c l d) from
    funext fun l => comp_assoc_left_block_indexed_sum F G obj deg c l]
  rw [compComposition_sum_inner]
  rw [cast_multilinearMap_sum]
  · exact comp_term_target_module_eq β_A β_C β_D
      (GHom β_D R) (G.comp F).objMap (G.comp F).deg_trans
      H.objMap H.deg_trans H.deg_trans_ofInt obj deg c

/-- For a fixed first `F`-composition, expanding `(H.comp G)` on the resulting
list gives the sum over one composition of that list. -/
private lemma comp_assoc_right_outer_term_indexed_sum
    (F : AInfinityFunctorData (β_A := β_A) (β_B := β_B) R ObjA ObjB)
    (G : AInfinityFunctorData (β_A := β_B) (β_B := β_C) R ObjB ObjC)
    (H : AInfinityFunctorData (β_A := β_C) (β_B := β_D) R ObjC ObjD)
    {n : ℕ} [NeZero n]
    (obj : Fin (n + 1) → ObjA)
    (deg : Fin n → β_A)
    (c : Composition n) :
    compTermMultilinearMap β_A β_B β_D
      (GHom β_A R) (GHom β_B R) (GHom β_D R)
      F.objMap F.deg_trans F.phi
      (H.comp G).objMap (H.comp G).deg_trans (H.comp G).deg_trans_ofInt (H.comp G).phi
      obj deg c =
      ∑ d : Composition c.length, compAssocRightIndexedTerm F G H obj deg ⟨c, d⟩ := by
  classical
  unfold compAssocRightIndexedTerm compTermMultilinearMap
  simp only [AInfinityFunctorData.comp, compPhi]
  rw [compComposition_sum_outer]
  rw [cast_multilinearMap_sum]
  · simp only [compTermMultilinearMap]
  · exact comp_term_target_module_eq β_A β_B β_D
      (GHom β_D R) F.objMap F.deg_trans
      (H.objMap ∘ G.objMap) (H.deg_trans.comp G.deg_trans)
      (by intro k; simp [AddMonoidHom.comp_apply, G.deg_trans_ofInt, H.deg_trans_ofInt])
      obj deg c

/-- Expanding the left bracketing gives the sum over left indexing data. -/
private lemma comp_assoc_phi_left_indexed_sum
    (F : AInfinityFunctorData (β_A := β_A) (β_B := β_B) R ObjA ObjB)
    (G : AInfinityFunctorData (β_A := β_B) (β_B := β_C) R ObjB ObjC)
    (H : AInfinityFunctorData (β_A := β_C) (β_B := β_D) R ObjC ObjD)
    {n : ℕ} [NeZero n]
    (obj : Fin (n + 1) → ObjA)
    (deg : Fin n → β_A) :
    compAssocLeftPhiExpanded F G H obj deg =
      ∑ I : compAssocLeftIndex n, compAssocLeftIndexedTerm F G H obj deg I := by
  classical
  unfold compAssocLeftPhiExpanded compPhi
  rw [Fintype.sum_sigma]
  exact Finset.sum_congr rfl fun c _ =>
    comp_assoc_left_outer_term_indexed_sum F G H obj deg c

/-- Expanding the right bracketing gives the sum over right indexing data. -/
private lemma comp_assoc_phi_right_indexed_sum
    (F : AInfinityFunctorData (β_A := β_A) (β_B := β_B) R ObjA ObjB)
    (G : AInfinityFunctorData (β_A := β_B) (β_B := β_C) R ObjB ObjC)
    (H : AInfinityFunctorData (β_A := β_C) (β_B := β_D) R ObjC ObjD)
    {n : ℕ} [NeZero n]
    (obj : Fin (n + 1) → ObjA)
    (deg : Fin n → β_A) :
    compAssocRightPhiExpanded F G H obj deg =
      ∑ I : compAssocRightIndex n, compAssocRightIndexedTerm F G H obj deg I := by
  classical
  unfold compAssocRightPhiExpanded compPhi
  rw [Fintype.sum_sigma]
  exact Finset.sum_congr rfl fun c _ =>
    comp_assoc_right_outer_term_indexed_sum F G H obj deg c

/-- Pointwise form of the final reindexing check.

After expanding both bracketings, a right index `(a, b)` corresponds under
`Composition.sigmaEquivSigmaPi` to the left index
`(a.gather b, a.sigmaCompositionAux b)`.  The remaining work is pure dependent
transport: the outer `H` arities are related by `length_gather`, the middle
`G` arities by `length_sigmaCompositionAux`, the inner `F` block sizes by
`blocksFun_sigmaCompositionAux`, and the original input coordinates by
`sizeUpTo_sizeUpTo_add`. -/
private lemma comp_assoc_phi_indexed_summand_apply
    (F : AInfinityFunctorData (β_A := β_A) (β_B := β_B) R ObjA ObjB)
    (G : AInfinityFunctorData (β_A := β_B) (β_B := β_C) R ObjB ObjC)
    (H : AInfinityFunctorData (β_A := β_C) (β_B := β_D) R ObjC ObjD)
    {n : ℕ} [NeZero n]
    (obj : Fin (n + 1) → ObjA)
    (deg : Fin n → β_A)
    (I : compAssocRightIndex n)
    (x : (i : Fin n) → ComposableHomType (GHom β_A R) obj deg i) :
    compAssocLeftIndexedTerm F G H obj deg ((Composition.sigmaEquivSigmaPi n) I) x =
      compAssocRightIndexedTerm F G H obj deg I x := by
  classical
  rcases I with ⟨a, b⟩
  unfold compAssocLeftIndexedTerm compAssocRightIndexedTerm
  rw [multilinearMap_cast_apply
    (h := comp_term_target_module_eq β_A β_C β_D
      (GHom β_D R) (G.comp F).objMap (G.comp F).deg_trans
      H.objMap H.deg_trans H.deg_trans_ofInt obj deg
      ((Composition.sigmaEquivSigmaPi n) ⟨a, b⟩).1)]
  rw [multilinearMap_cast_apply
    (h := comp_term_target_module_eq β_A β_B β_D
      (GHom β_D R) F.objMap F.deg_trans
      (H.comp G).objMap (H.comp G).deg_trans (H.comp G).deg_trans_ofInt obj deg a)]
  apply eq_of_heq
  refine HEq.trans (cast_heq _ _) ?_
  refine HEq.trans ?_ (cast_heq _ _).symm
  unfold compTermMultilinearMap
  dsimp [MultilinearMap.compComposition]
  rw [multilinearMap_cast_apply
    (h := comp_term_target_module_eq β_B β_C β_D
      (GHom β_D R) G.objMap G.deg_trans
      H.objMap H.deg_trans H.deg_trans_ofInt
      (functorCompositionOuterObj F.objMap obj a)
      (functorCompositionOuterDeg β_A β_B F.deg_trans deg a) b)]
  refine HEq.trans ?_ (cast_heq _ _).symm
  dsimp [Composition.sigmaEquivSigmaPi]
  refine phi_heq_of_arity_eq H (Composition.length_gather a b) ?_ ?_ _ _ ?_
  · apply Function.hfunext (by simp [Composition.length_gather])
    intro i j hij
    apply heq_of_eq
    have hlen_succ : (a.gather b).length + 1 = b.length + 1 := by
      rw [Composition.length_gather]
    have hijval : i.val = j.val := (Fin.heq_ext_iff hlen_succ).mp hij
    dsimp [functorCompositionOuterObj]
    apply congrArg (fun k => G.objMap (F.objMap (obj k)))
    apply Fin.ext
    dsimp [Composition.boundary]
    by_cases hjlast : j.val = b.length
    · have hi_last : i.val = (a.gather b).length := by
        omega
      simp [hi_last, hjlast, Composition.sizeUpTo_length]
    · have hjlt : j.val < b.length := by
        omega
      have hsize :
          a.sizeUpTo (b.sizeUpTo j.val) = (a.gather b).sizeUpTo j.val := by
        have h :=
          Composition.sizeUpTo_sizeUpTo_add a b (i := j.val) (j := 0) hjlt
            (show 0 < b.blocksFun ⟨j.val, hjlt⟩ from
              lt_of_lt_of_le Nat.zero_lt_one (b.one_le_blocksFun ⟨j.val, hjlt⟩))
        simpa using h
      rw [hijval, hsize]
  · -- The outer degree strings match by applying `comp_compatible_deg`
    -- inside each block selected by `b`.
    apply Function.hfunext (by simp [Composition.length_gather])
    intro i j hij
    apply heq_of_eq
    dsimp [functorCompositionOuterDeg]
    have hcomp :=
      comp_compatible_deg β_A β_B β_C
        F.deg_trans G.deg_trans G.deg_trans_ofInt
        (compositionBlockDeg β_A deg (a.gather b) i)
        (a.sigmaCompositionAux b i)
    symm
    convert hcomp using 2
    · have hlen : (a.gather b).length = b.length := Composition.length_gather a b
      have hijval : i.val = j.val := (Fin.heq_ext_iff hlen).mp hij
      have hi : i = ⟨j.val, hlen.symm ▸ j.2⟩ := Fin.ext hijval
      rw [hi]
      exact (Composition.length_sigmaCompositionAux a b j).symm
    · have hlen : (a.gather b).length = b.length := Composition.length_gather a b
      have hijval : i.val = j.val := (Fin.heq_ext_iff hlen).mp hij
      have hi : i = ⟨j.val, hlen.symm ▸ j.2⟩ := Fin.ext hijval
      rw [hi]
      apply Function.hfunext
        (congrArg Fin ((Composition.length_sigmaCompositionAux a b j).symm))
      intro p q hpq
      have hdom : b.blocksFun j =
          (a.sigmaCompositionAux b ⟨j.val, hlen.symm ▸ j.2⟩).length :=
        (Composition.length_sigmaCompositionAux a b j).symm
      have hpval : p.val = q.val := (Fin.heq_ext_iff hdom).mp hpq
      have hq :
          q =
            ⟨p.val, (Composition.length_sigmaCompositionAux a b j).symm ▸ p.2⟩ :=
        Fin.ext hpval.symm
      subst q
      have hblocks :
          (a.sigmaCompositionAux b ⟨j.val, hlen.symm ▸ j.2⟩).blocksFun
              ⟨p.val, (Composition.length_sigmaCompositionAux a b j).symm ▸ p.2⟩ =
            a.blocksFun (b.embedding j p) :=
        Composition.blocksFun_sigmaCompositionAux a b j p
      refine functorTargetDeg_heq_of_arity_eq F.deg_trans hblocks.symm ?_
      apply Function.hfunext (congrArg Fin hblocks.symm)
      intro r s hrs
      apply heq_of_eq
      apply congrArg deg
      apply Fin.ext
      have hrsval : r.val = s.val := (Fin.heq_ext_iff hblocks.symm).mp hrs
      have hsize :=
        Composition.sizeUpTo_sizeUpTo_add a b (i := j.val) (j := p.val) j.2 p.2
      dsimp [compositionBlockDeg]
      simp [hsize, hrsval, Nat.add_assoc]
  · -- The inputs to the outer `H.phi` match blockwise; each block uses
    -- `length_sigmaCompositionAux`, `blocksFun_sigmaCompositionAux`, and
    -- `sizeUpTo_sizeUpTo_add` to identify the nested `G` and `F` terms.
    apply Function.hfunext (congrArg Fin (Composition.length_gather a b))
    intro i j hij
    have hlen : (a.gather b).length = b.length := Composition.length_gather a b
    have hijval : i.val = j.val := (Fin.heq_ext_iff hlen).mp hij
    have hi : i = ⟨j.val, hlen.symm ▸ j.2⟩ := Fin.ext hijval
    rw [hi]
    unfold compAssocLeftIndexedBlock compTermBlock
    refine HEq.trans
      (heq_of_eq <| multilinearMap_cast_apply
        (h := comp_term_block_module_eq β_A β_C
          (GHom β_C R) (G.comp F).objMap (G.comp F).deg_trans
          obj deg (a.gather b) ⟨j.val, hlen.symm ▸ j.2⟩) _ _) ?_
    refine HEq.trans (cast_heq _ _) ?_
    refine HEq.trans ?_
      (heq_of_eq <| multilinearMap_cast_apply
        (h := comp_term_block_module_eq β_B β_C
          (GHom β_C R) G.objMap G.deg_trans
          (functorCompositionOuterObj F.objMap obj a)
          (functorCompositionOuterDeg β_A β_B F.deg_trans deg a) b j) _ _).symm
    refine HEq.trans ?_ (cast_heq _ _).symm
    unfold compTermMultilinearMap
    dsimp [MultilinearMap.compComposition]
    refine HEq.trans
      (heq_of_eq <| multilinearMap_cast_apply
        (h := comp_term_target_module_eq β_A β_B β_C
          (GHom β_C R) F.objMap F.deg_trans
          G.objMap G.deg_trans G.deg_trans_ofInt
          (compositionBlockObj obj (a.gather b) ⟨j.val, hlen.symm ▸ j.2⟩)
          (compositionBlockDeg β_A deg (a.gather b) ⟨j.val, hlen.symm ▸ j.2⟩)
          (a.sigmaCompositionAux b ⟨j.val, hlen.symm ▸ j.2⟩)) _ _) ?_
    refine HEq.trans (cast_heq _ _) ?_
    refine phi_heq_of_arity_eq G (Composition.length_sigmaCompositionAux a b j) ?_ ?_ _ _ ?_
    · exact comp_assoc_inner_outer_obj_heq F.objMap obj a b j
    · exact comp_assoc_inner_outer_deg_heq F.deg_trans deg a b j
    · apply Function.hfunext (congrArg Fin (Composition.length_sigmaCompositionAux a b j))
      intro p q hpq
      unfold compTermBlock
      refine HEq.trans
        (heq_of_eq <| multilinearMap_cast_apply
          (h := comp_term_block_module_eq β_A β_B
            (GHom β_B R) F.objMap F.deg_trans
            (compositionBlockObj obj (a.gather b) ⟨j.val, hlen.symm ▸ j.2⟩)
            (compositionBlockDeg β_A deg (a.gather b) ⟨j.val, hlen.symm ▸ j.2⟩)
            (a.sigmaCompositionAux b ⟨j.val, hlen.symm ▸ j.2⟩) p) _ _) ?_
      refine HEq.trans (cast_heq _ _) ?_
      refine HEq.trans ?_
        (heq_of_eq <| multilinearMap_cast_apply
          (h := comp_term_block_module_eq β_A β_B
            (GHom β_B R) F.objMap F.deg_trans
            obj deg a (b.embedding j q)) _ _).symm
      refine HEq.trans ?_ (cast_heq _ _).symm
      have hdom :
          (a.sigmaCompositionAux b ⟨j.val, hlen.symm ▸ j.2⟩).length =
            b.blocksFun j :=
        Composition.length_sigmaCompositionAux a b j
      have hpval : p.val = q.val := (Fin.heq_ext_iff hdom).mp hpq
      have hp :
          p =
            ⟨q.val, (Composition.length_sigmaCompositionAux a b j).symm ▸ q.2⟩ :=
        Fin.ext hpval
      subst p
      have hblocks :
          (a.sigmaCompositionAux b ⟨j.val, hlen.symm ▸ j.2⟩).blocksFun
              ⟨q.val, (Composition.length_sigmaCompositionAux a b j).symm ▸ q.2⟩ =
            a.blocksFun (b.embedding j q) :=
        Composition.blocksFun_sigmaCompositionAux a b j q
      refine phi_heq_of_arity_eq F hblocks ?_ ?_ _ _ ?_
      · apply Function.hfunext (congrArg Fin (congrArg Nat.succ hblocks))
        intro r s hrs
        apply heq_of_eq
        have hrsval : r.val = s.val :=
          (Fin.heq_ext_iff (congrArg Nat.succ hblocks)).mp hrs
        dsimp [compositionBlockObj]
        apply congrArg obj
        apply Fin.ext
        have hsize :=
          Composition.sizeUpTo_sizeUpTo_add a b (i := j.val) (j := q.val) j.2 q.2
        simp [hsize, hrsval, Nat.add_assoc]
      · apply Function.hfunext (congrArg Fin hblocks)
        intro r s hrs
        apply heq_of_eq
        apply congrArg deg
        exact comp_assoc_embedding_eq a b j hpq hrs
      · apply Function.hfunext (congrArg Fin hblocks)
        intro r s hrs
        exact congr_arg_heq x (comp_assoc_embedding_eq a b j hpq hrs)

/-- Corresponding fully expanded summands agree under the associativity
bijection of indexing data. -/
private lemma comp_assoc_phi_indexed_summand
    (F : AInfinityFunctorData (β_A := β_A) (β_B := β_B) R ObjA ObjB)
    (G : AInfinityFunctorData (β_A := β_B) (β_B := β_C) R ObjB ObjC)
    (H : AInfinityFunctorData (β_A := β_C) (β_B := β_D) R ObjC ObjD)
    {n : ℕ} [NeZero n]
    (obj : Fin (n + 1) → ObjA)
    (deg : Fin n → β_A)
    (I : compAssocRightIndex n) :
    compAssocLeftIndexedTerm F G H obj deg ((Composition.sigmaEquivSigmaPi n) I) =
      compAssocRightIndexedTerm F G H obj deg I := by
  classical
  ext x
  exact comp_assoc_phi_indexed_summand_apply F G H obj deg I x

/-- The two fully expanded finite sums agree after reindexing. -/
private lemma comp_assoc_phi_indexed_sum
    (F : AInfinityFunctorData (β_A := β_A) (β_B := β_B) R ObjA ObjB)
    (G : AInfinityFunctorData (β_A := β_B) (β_B := β_C) R ObjB ObjC)
    (H : AInfinityFunctorData (β_A := β_C) (β_B := β_D) R ObjC ObjD)
    {n : ℕ} [NeZero n]
    (obj : Fin (n + 1) → ObjA)
    (deg : Fin n → β_A) :
    (∑ I : compAssocLeftIndex n, compAssocLeftIndexedTerm F G H obj deg I) =
      ∑ I : compAssocRightIndex n, compAssocRightIndexedTerm F G H obj deg I := by
  classical
  rw [← (Composition.sigmaEquivSigmaPi n).sum_comp]
  exact Finset.sum_congr rfl fun I _ =>
    comp_assoc_phi_indexed_summand F G H obj deg I

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
  rw [comp_assoc_phi_left_indexed_sum, comp_assoc_phi_right_indexed_sum]
  exact comp_assoc_phi_indexed_sum F G H obj deg

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
  rw [comp_assoc_phi_expand_left]
  rw [comp_assoc_phi_reindex]

/-- Raw `A∞` functor composition is associative. -/
theorem comp_assoc
    (F : AInfinityFunctorData (β_A := β_A) (β_B := β_B) R ObjA ObjB)
    (G : AInfinityFunctorData (β_A := β_B) (β_B := β_C) R ObjB ObjC)
    (H : AInfinityFunctorData (β_A := β_C) (β_B := β_D) R ObjC ObjD) :
    H.comp (G.comp F) = (H.comp G).comp F := by
  obtain ⟨F_objMap, F_deg_trans, F_deg_trans_ofInt, F_deg_trans_sign, F_phi⟩ := F
  obtain ⟨G_objMap, G_deg_trans, G_deg_trans_ofInt, G_deg_trans_sign, G_phi⟩ := G
  obtain ⟨H_objMap, H_deg_trans, H_deg_trans_ofInt, H_deg_trans_sign, H_phi⟩ := H
  rw [AInfinityFunctorData.mk.injEq]
  refine ⟨rfl, rfl, ?_⟩
  apply heq_of_eq
  funext n hn obj deg
  convert comp_assoc_phi
    (β_A := β_A) (β_B := β_B) (β_C := β_C) (β_D := β_D)
    (R := R) (ObjA := ObjA) (ObjB := ObjB) (ObjC := ObjC) (ObjD := ObjD)
    { objMap := F_objMap
      deg_trans := F_deg_trans
      deg_trans_ofInt := F_deg_trans_ofInt
      deg_trans_sign := F_deg_trans_sign
      phi := F_phi }
    { objMap := G_objMap
      deg_trans := G_deg_trans
      deg_trans_ofInt := G_deg_trans_ofInt
      deg_trans_sign := G_deg_trans_sign
      phi := G_phi }
    { objMap := H_objMap
      deg_trans := H_deg_trans
      deg_trans_ofInt := H_deg_trans_ofInt
      deg_trans_sign := H_deg_trans_sign
      phi := H_phi }
    obj deg using 1

end BasicProperties
end AInfinityFunctorData

namespace AInfinityFunctor

section BasicProperties

variable {β_A : Type v} [GradingIndex β_A]
variable {β_B : Type w} [GradingIndex β_B]
variable {β_C : Type x} [GradingIndex β_C]
variable {R : Type u} [CommRing R]
variable {ObjA : Type y} {ObjB : Type z} {ObjC : Type t}
variable [AInfinityCategory β_A R ObjA]
variable [AInfinityCategory β_B R ObjB]
variable [AInfinityCategory β_C R ObjC]

/-- The left-hand side of the functor equation for the composite `G.comp F`. -/
private abbrev compFunctorEquationLHS
    (F : AInfinityFunctor (β_A := β_A) (β_B := β_B) R ObjA ObjB)
    (G : AInfinityFunctor (β_A := β_B) (β_B := β_C) R ObjB ObjC)
    {n : ℕ} [NeZero n]
    (obj : Fin (n + 1) → ObjA)
    (deg : Fin n → β_A)
    (x : (i : Fin n) → ComposableHomType (GHom β_A R) obj deg i) :
    AInfinityFunctorData.functorEqTargetType β_A β_C (GHom β_C R)
      (G.objMap ∘ F.objMap) (G.deg_trans.comp F.deg_trans) obj deg :=
  AInfinityFunctorData.functorLHSSum β_A β_C
    (GHom β_A R) (GHom β_C R)
    (G.objMap ∘ F.objMap) (G.deg_trans.comp F.deg_trans)
    (by intro k; simp [AddMonoidHom.comp_apply, F.deg_trans_ofInt, G.deg_trans_ofInt])
    (fun obj deg =>
      AInfinityFunctorData.compPhi β_A β_B β_C
        (GHom β_A R) (GHom β_B R) (GHom β_C R)
        F.objMap F.deg_trans F.phi
        G.objMap G.deg_trans G.deg_trans_ofInt G.phi
        obj deg)
    (AInfinityCategoryStruct.m (β := β_A) (R := R) (Obj := ObjA))
    obj deg x

/-- The right-hand side of the functor equation for the composite `G.comp F`. -/
private abbrev compFunctorEquationRHS
    (F : AInfinityFunctor (β_A := β_A) (β_B := β_B) R ObjA ObjB)
    (G : AInfinityFunctor (β_A := β_B) (β_B := β_C) R ObjB ObjC)
    {n : ℕ} [NeZero n]
    (obj : Fin (n + 1) → ObjA)
    (deg : Fin n → β_A)
    (x : (i : Fin n) → ComposableHomType (GHom β_A R) obj deg i) :
    AInfinityFunctorData.functorEqTargetType β_A β_C (GHom β_C R)
      (G.objMap ∘ F.objMap) (G.deg_trans.comp F.deg_trans) obj deg :=
  AInfinityFunctorData.functorRHSSum β_A β_C
    (GHom β_A R) (GHom β_C R)
    (G.objMap ∘ F.objMap) (G.deg_trans.comp F.deg_trans)
    (fun obj deg =>
      AInfinityFunctorData.compPhi β_A β_B β_C
        (GHom β_A R) (GHom β_B R) (GHom β_C R)
        F.objMap F.deg_trans F.phi
        G.objMap G.deg_trans G.deg_trans_ofInt G.phi
        obj deg)
    (AInfinityCategoryStruct.m (β := β_C) (R := R) (Obj := ObjC))
    obj deg x

/-- The composite left-hand side with the defining sum for `compPhi` exposed in
each Stasheff summand. -/
private abbrev compFunctorExpandedLHS
    (F : AInfinityFunctor (β_A := β_A) (β_B := β_B) R ObjA ObjB)
    (G : AInfinityFunctor (β_A := β_B) (β_B := β_C) R ObjB ObjC)
    {n : ℕ} [NeZero n]
    (obj : Fin (n + 1) → ObjA)
    (deg : Fin n → β_A)
    (x : (i : Fin n) → ComposableHomType (GHom β_A R) obj deg i) :
    AInfinityFunctorData.functorEqTargetType β_A β_C (GHom β_C R)
      (G.objMap ∘ F.objMap) (G.deg_trans.comp F.deg_trans) obj deg :=
  ∑ r ∈ (Finset.range (n + 1)).attach,
    ∑ s ∈ (Finset.Ico 1 (n - r.1 + 1)).attach,
      let h : ValidStasheffIndices n r.1 s.1 :=
        validStasheffIndices_of_mem_ranges (n := n) r.2 s.2
      letI : NeZero (n + 1 - s.1) :=
        ⟨Nat.ne_of_gt (indexedStasheffOuterArity_pos r.1 s.1 h.2)⟩
      (stasheffSign deg r.1 s.1 h.2) •
        cast
          (AInfinityFunctorData.functor_lhs_target_eq β_A β_C
            (GHom β_C R)
            (G.objMap ∘ F.objMap)
            (G.deg_trans.comp F.deg_trans)
            (by intro k; simp [AddMonoidHom.comp_apply, F.deg_trans_ofInt, G.deg_trans_ofInt])
            obj deg r.1 s.1 h.2)
          ((∑ c : Composition (n + 1 - s.1),
              AInfinityFunctorData.compTermMultilinearMap β_A β_B β_C
                (GHom β_A R) (GHom β_B R) (GHom β_C R)
                F.objMap F.deg_trans F.phi
                G.objMap G.deg_trans G.deg_trans_ofInt G.phi
                (stasheffObjOut obj r.1 s.1 h.2)
                (stasheffDegOut deg r.1 s.1 h.2)
                c)
            (indexedStasheffXOut (GHom β_A R)
              (AInfinityCategoryStruct.m (β := β_A) (R := R) (Obj := ObjA))
              obj deg x r.1 s.1 h.1 h.2))

/-- The composite LHS after reindexing by an original composition together
with the block that contains the inserted `m_A`.

This is the first genuinely useful intermediate stage for the composition
proof.  Its body is currently the already-expanded LHS; the intended final
replacement is a finite sum indexed by
`a : Composition n`, `l : Fin a.length`, and Stasheff indices inside the
`l`-th block of `a`. -/
private abbrev compFunctorFBlockLHSSum
    (F : AInfinityFunctor (β_A := β_A) (β_B := β_B) R ObjA ObjB)
    (G : AInfinityFunctor (β_A := β_B) (β_B := β_C) R ObjB ObjC)
    {n : ℕ} [NeZero n]
    (obj : Fin (n + 1) → ObjA)
    (deg : Fin n → β_A)
    (x : (i : Fin n) → ComposableHomType (GHom β_A R) obj deg i) :
    AInfinityFunctorData.functorEqTargetType β_A β_C (GHom β_C R)
      (G.objMap ∘ F.objMap) (G.deg_trans.comp F.deg_trans) obj deg :=
  compFunctorExpandedLHS F G obj deg x

/-- The previous block-indexed sum after applying the `F` functor equation
inside the selected block.

In the final proof this stage should contain the `m_B` term produced by
`F.satisfiesFunctorEquations`, still sitting inside the outer `G.phi`. -/
private abbrev compFunctorFBlockRHSSum
    (F : AInfinityFunctor (β_A := β_A) (β_B := β_B) R ObjA ObjB)
    (G : AInfinityFunctor (β_A := β_B) (β_B := β_C) R ObjB ObjC)
    {n : ℕ} [NeZero n]
    (obj : Fin (n + 1) → ObjA)
    (deg : Fin n → β_A)
    (x : (i : Fin n) → ComposableHomType (GHom β_A R) obj deg i) :
    AInfinityFunctorData.functorEqTargetType β_A β_C (GHom β_C R)
      (G.objMap ∘ F.objMap) (G.deg_trans.comp F.deg_trans) obj deg :=
  compFunctorFBlockLHSSum F G obj deg x

/-- The `l`-th output of `F` associated to a composition of the original
input string, viewed as an input for the outer `G` equation. -/
private abbrev compFunctorBlockOutput
    (F : AInfinityFunctor (β_A := β_A) (β_B := β_B) R ObjA ObjB)
    {n : ℕ} [NeZero n]
    (obj : Fin (n + 1) → ObjA)
    (deg : Fin n → β_A)
    (x : (i : Fin n) → ComposableHomType (GHom β_A R) obj deg i)
    (c : Composition n)
    (l : Fin c.length) :
    ComposableHomType (GHom β_B R)
      (AInfinityFunctorData.functorCompositionOuterObj F.objMap obj c)
      (AInfinityFunctorData.functorCompositionOuterDeg β_A β_B F.deg_trans deg c) l :=
  AInfinityFunctorData.functorRHSBlock β_A β_B
    (GHom β_A R) (GHom β_B R)
    F.objMap F.deg_trans F.phi obj deg c l
    (fun j => x (c.embedding l j))

/-- Target transport for the `G` equation applied to the tuple of `F` block
outputs attached to a composition of the original inputs. -/
private lemma comp_functor_G_equation_target_eq
    (F : AInfinityFunctor (β_A := β_A) (β_B := β_B) R ObjA ObjB)
    (G : AInfinityFunctor (β_A := β_B) (β_B := β_C) R ObjB ObjC)
    {n : ℕ} [NeZero n]
    (obj : Fin (n + 1) → ObjA)
    (deg : Fin n → β_A)
    (c : Composition n) :
    ((AInfinityFunctorData.functorEqTargetType β_B β_C (GHom β_C R)
        G.objMap G.deg_trans
        (AInfinityFunctorData.functorCompositionOuterObj F.objMap obj c)
        (AInfinityFunctorData.functorCompositionOuterDeg β_A β_B F.deg_trans deg c) :
        ModuleCat R) : Type u) =
      ((AInfinityFunctorData.functorEqTargetType β_A β_C (GHom β_C R)
        (G.objMap ∘ F.objMap) (G.deg_trans.comp F.deg_trans) obj deg :
        ModuleCat R) : Type u) := by
  have hsource :
      AInfinityFunctorData.functorCompositionOuterObj F.objMap obj c 0 =
        F.objMap (obj 0) := by
    simp [AInfinityFunctorData.functorCompositionOuterObj]
  have htarget :
      AInfinityFunctorData.functorCompositionOuterObj F.objMap obj c (Fin.last c.length) =
        F.objMap (obj (Fin.last n)) := by
    simp [AInfinityFunctorData.functorCompositionOuterObj]
  have hdeg :
      AInfinityFunctorData.functorEqTargetDeg β_B β_C G.deg_trans
          (AInfinityFunctorData.functorCompositionOuterDeg β_A β_B F.deg_trans deg c) =
        AInfinityFunctorData.functorEqTargetDeg β_A β_C
          (G.deg_trans.comp F.deg_trans) deg := by
    have hcomp :=
      AInfinityFunctorData.comp_compatible_deg β_A β_B β_C
        F.deg_trans G.deg_trans G.deg_trans_ofInt deg c
    convert congrArg (fun d : β_C => d + shift_ofInt (β := β_C) 1) hcomp using 1 <;>
      simp only [functorTargetDeg, AInfinityFunctorData.functorEqTargetDeg,
        add_assoc, shift_ofInt, ← map_add] <;>
      congr 2 <;>
      omega
  dsimp [AInfinityFunctorData.functorEqTargetType]
  rw [hsource, htarget]
  exact congrArg
    (fun d => ((GHom β_C R (G.objMap (F.objMap (obj 0)))
      (G.objMap (F.objMap (obj (Fin.last n)))) d : ModuleCat R) : Type u))
    hdeg

/-- The left-hand side of the `G` functor equation applied to the string of
outputs of the `F` components.

The final definition should be the same finite sum as
`compFunctorFBlockRHSSum`, reindexed so that the Stasheff insertion occurs in
the outer `G` equation. -/
private def compFunctorGLHSSum
    (F : AInfinityFunctor (β_A := β_A) (β_B := β_B) R ObjA ObjB)
    (G : AInfinityFunctor (β_A := β_B) (β_B := β_C) R ObjB ObjC)
    {n : ℕ} [NeZero n]
    (obj : Fin (n + 1) → ObjA)
    (deg : Fin n → β_A)
    (x : (i : Fin n) → ComposableHomType (GHom β_A R) obj deg i) :
    AInfinityFunctorData.functorEqTargetType β_A β_C (GHom β_C R)
      (G.objMap ∘ F.objMap) (G.deg_trans.comp F.deg_trans) obj deg :=
  ∑ c : Composition n,
    letI : NeZero c.length :=
      ⟨Nat.ne_of_gt (c.length_pos_of_pos (Nat.pos_of_ne_zero (NeZero.ne n)))⟩
    cast (comp_functor_G_equation_target_eq F G obj deg c)
      (AInfinityFunctorData.functorLHSSum β_B β_C
        (GHom β_B R) (GHom β_C R)
        G.objMap G.deg_trans G.deg_trans_ofInt G.phi
        (AInfinityCategoryStruct.m (β := β_B) (R := R) (Obj := ObjB))
        (AInfinityFunctorData.functorCompositionOuterObj F.objMap obj c)
        (AInfinityFunctorData.functorCompositionOuterDeg β_A β_B F.deg_trans deg c)
        (fun l => compFunctorBlockOutput F obj deg x c l))

/-- The right-hand side obtained after applying the `G` functor equation.

This stage is a two-level composition sum: first choose the `F` blocks, then
choose the blocks in the `G` equation. -/
private def compFunctorGRHSSum
    (F : AInfinityFunctor (β_A := β_A) (β_B := β_B) R ObjA ObjB)
    (G : AInfinityFunctor (β_A := β_B) (β_B := β_C) R ObjB ObjC)
    {n : ℕ} [NeZero n]
    (obj : Fin (n + 1) → ObjA)
    (deg : Fin n → β_A)
    (x : (i : Fin n) → ComposableHomType (GHom β_A R) obj deg i) :
    AInfinityFunctorData.functorEqTargetType β_A β_C (GHom β_C R)
      (G.objMap ∘ F.objMap) (G.deg_trans.comp F.deg_trans) obj deg :=
  ∑ c : Composition n,
    letI : NeZero c.length :=
      ⟨Nat.ne_of_gt (c.length_pos_of_pos (Nat.pos_of_ne_zero (NeZero.ne n)))⟩
    cast (comp_functor_G_equation_target_eq F G obj deg c)
      (AInfinityFunctorData.functorRHSSum β_B β_C
        (GHom β_B R) (GHom β_C R)
        G.objMap G.deg_trans G.phi
        (AInfinityCategoryStruct.m (β := β_C) (R := R) (Obj := ObjC))
        (AInfinityFunctorData.functorCompositionOuterObj F.objMap obj c)
        (AInfinityFunctorData.functorCompositionOuterDeg β_A β_B F.deg_trans deg c)
        (fun l => compFunctorBlockOutput F obj deg x c l))

/-- The composite RHS with the inner `compPhi` sums exposed blockwise.

The final contraction step should identify this expanded two-level sum with
`compFunctorEquationRHS`, using the same `Composition.sigmaEquivSigmaPi`
reindexing pattern as the associativity proof above. -/
private abbrev compFunctorExpandedRHS
    (F : AInfinityFunctor (β_A := β_A) (β_B := β_B) R ObjA ObjB)
    (G : AInfinityFunctor (β_A := β_B) (β_B := β_C) R ObjB ObjC)
    {n : ℕ} [NeZero n]
    (obj : Fin (n + 1) → ObjA)
    (deg : Fin n → β_A)
    (x : (i : Fin n) → ComposableHomType (GHom β_A R) obj deg i) :
    AInfinityFunctorData.functorEqTargetType β_A β_C (GHom β_C R)
      (G.objMap ∘ F.objMap) (G.deg_trans.comp F.deg_trans) obj deg :=
  compFunctorEquationRHS F G obj deg x

/-- The composite left-hand side after expanding every occurrence of
`(G.comp F).phi`.

This is the first bookkeeping step: distribute the finite sum defining
`compPhi` through the Stasheff-type left-hand side of the composite equation. -/
private lemma comp_functor_lhs_expand
    (F : AInfinityFunctor (β_A := β_A) (β_B := β_B) R ObjA ObjB)
    (G : AInfinityFunctor (β_A := β_B) (β_B := β_C) R ObjB ObjC)
    {n : ℕ} [NeZero n]
    (obj : Fin (n + 1) → ObjA)
    (deg : Fin n → β_A)
    (x : (i : Fin n) → ComposableHomType (GHom β_A R) obj deg i) :
    compFunctorEquationLHS F G obj deg x =
      compFunctorExpandedLHS F G obj deg x := by
  rfl

/-- The expanded composite left-hand side contracts back to the raw left-hand
side definitionally.

The genuinely algebraic `F` step is isolated in
`comp_functor_F_equation_raw` below; this lemma just keeps the expansion step
bidirectional for the surrounding calculation. -/
private lemma comp_functor_apply_F_equation
    (F : AInfinityFunctor (β_A := β_A) (β_B := β_B) R ObjA ObjB)
    (G : AInfinityFunctor (β_A := β_B) (β_B := β_C) R ObjB ObjC)
    {n : ℕ} [NeZero n]
    (obj : Fin (n + 1) → ObjA)
    (deg : Fin n → β_A)
    (x : (i : Fin n) → ComposableHomType (GHom β_A R) obj deg i) :
    compFunctorExpandedLHS F G obj deg x =
      compFunctorEquationLHS F G obj deg x := by
  rfl

/-- The raw functor equation for `F`, available as an equality between the
finite sums used by the bookkeeping proof. -/
private lemma comp_functor_F_equation_raw
    (F : AInfinityFunctor (β_A := β_A) (β_B := β_B) R ObjA ObjB)
    {n : ℕ} [NeZero n]
    (obj : Fin (n + 1) → ObjA)
    (deg : Fin n → β_A)
    (x : (i : Fin n) → ComposableHomType (GHom β_A R) obj deg i) :
    AInfinityFunctorData.functorLHSSum β_A β_B
      (GHom β_A R) (GHom β_B R)
      F.objMap F.deg_trans F.deg_trans_ofInt F.phi
      (AInfinityCategoryStruct.m (β := β_A) (R := R) (Obj := ObjA))
      obj deg x =
    AInfinityFunctorData.functorRHSSum β_A β_B
      (GHom β_A R) (GHom β_B R)
      F.objMap F.deg_trans F.phi
      (AInfinityCategoryStruct.m (β := β_B) (R := R) (Obj := ObjB))
      obj deg x := by
  exact F.satisfiesFunctorEquations n obj deg x

/-- The raw functor equation for `G`, available as an equality between the
finite sums used by the bookkeeping proof. -/
private lemma comp_functor_G_equation_raw
    (G : AInfinityFunctor (β_A := β_B) (β_B := β_C) R ObjB ObjC)
    {n : ℕ} [NeZero n]
    (obj : Fin (n + 1) → ObjB)
    (deg : Fin n → β_B)
    (x : (i : Fin n) → ComposableHomType (GHom β_B R) obj deg i) :
    AInfinityFunctorData.functorLHSSum β_B β_C
      (GHom β_B R) (GHom β_C R)
      G.objMap G.deg_trans G.deg_trans_ofInt G.phi
      (AInfinityCategoryStruct.m (β := β_B) (R := R) (Obj := ObjB))
      obj deg x =
    AInfinityFunctorData.functorRHSSum β_B β_C
      (GHom β_B R) (GHom β_C R)
      G.objMap G.deg_trans G.phi
      (AInfinityCategoryStruct.m (β := β_C) (R := R) (Obj := ObjC))
      obj deg x := by
  exact G.satisfiesFunctorEquations n obj deg x

/-- Reindex the expanded composite LHS into the block-indexed form where the
selected block is ready for the `F` functor equation. -/
private lemma comp_functor_expanded_lhs_to_F_block_lhs
    (F : AInfinityFunctor (β_A := β_A) (β_B := β_B) R ObjA ObjB)
    (G : AInfinityFunctor (β_A := β_B) (β_B := β_C) R ObjB ObjC)
    {n : ℕ} [NeZero n]
    (obj : Fin (n + 1) → ObjA)
    (deg : Fin n → β_A)
    (x : (i : Fin n) → ComposableHomType (GHom β_A R) obj deg i) :
    compFunctorExpandedLHS F G obj deg x =
      compFunctorFBlockLHSSum F G obj deg x := by
  rfl

/-- Apply `F.satisfiesFunctorEquations` inside each selected block of the
block-indexed composite LHS. -/
private lemma comp_functor_apply_F_blocks
    (F : AInfinityFunctor (β_A := β_A) (β_B := β_B) R ObjA ObjB)
    (G : AInfinityFunctor (β_A := β_B) (β_B := β_C) R ObjB ObjC)
    {n : ℕ} [NeZero n]
    (obj : Fin (n + 1) → ObjA)
    (deg : Fin n → β_A)
    (x : (i : Fin n) → ComposableHomType (GHom β_A R) obj deg i) :
    compFunctorFBlockLHSSum F G obj deg x =
      compFunctorFBlockRHSSum F G obj deg x := by
  rfl

/-- Reindex the result of the blockwise `F` equations as the LHS of the `G`
functor equation on the tuple of `F` block outputs. -/
private lemma comp_functor_F_block_rhs_to_G_lhs
    (F : AInfinityFunctor (β_A := β_A) (β_B := β_B) R ObjA ObjB)
    (G : AInfinityFunctor (β_A := β_B) (β_B := β_C) R ObjB ObjC)
    {n : ℕ} [NeZero n]
    (obj : Fin (n + 1) → ObjA)
    (deg : Fin n → β_A)
    (x : (i : Fin n) → ComposableHomType (GHom β_A R) obj deg i) :
    compFunctorFBlockRHSSum F G obj deg x =
      compFunctorGLHSSum F G obj deg x := by
  -- Final proof: identify the block containing the collapsed Stasheff input
  -- and split the total sign into the local `F` sign and the outer `G` sign.
  sorry

/-- Apply `G.satisfiesFunctorEquations` to the tuple of `F` block outputs,
summed over all original compositions of the input string. -/
private lemma comp_functor_apply_G_blocks
    (F : AInfinityFunctor (β_A := β_A) (β_B := β_B) R ObjA ObjB)
    (G : AInfinityFunctor (β_A := β_B) (β_B := β_C) R ObjB ObjC)
    {n : ℕ} [NeZero n]
    (obj : Fin (n + 1) → ObjA)
    (deg : Fin n → β_A)
    (x : (i : Fin n) → ComposableHomType (GHom β_A R) obj deg i) :
    compFunctorGLHSSum F G obj deg x =
      compFunctorGRHSSum F G obj deg x := by
  classical
  unfold compFunctorGLHSSum compFunctorGRHSSum
  refine Finset.sum_congr rfl ?_
  intro c _
  letI : NeZero c.length :=
    ⟨Nat.ne_of_gt (c.length_pos_of_pos (Nat.pos_of_ne_zero (NeZero.ne n)))⟩
  exact congrArg
    (fun y => cast (comp_functor_G_equation_target_eq F G obj deg c) y)
    (comp_functor_G_equation_raw G
      (AInfinityFunctorData.functorCompositionOuterObj F.objMap obj c)
      (AInfinityFunctorData.functorCompositionOuterDeg β_A β_B F.deg_trans deg c)
      (fun l => compFunctorBlockOutput F obj deg x c l))

/-- Reindex the RHS obtained from the `G` equation into the expanded RHS of the
composite functor equation. -/
private lemma comp_functor_G_rhs_to_expanded_rhs
    (F : AInfinityFunctor (β_A := β_A) (β_B := β_B) R ObjA ObjB)
    (G : AInfinityFunctor (β_A := β_B) (β_B := β_C) R ObjB ObjC)
    {n : ℕ} [NeZero n]
    (obj : Fin (n + 1) → ObjA)
    (deg : Fin n → β_A)
    (x : (i : Fin n) → ComposableHomType (GHom β_A R) obj deg i) :
    compFunctorGRHSSum F G obj deg x =
      compFunctorExpandedRHS F G obj deg x := by
  -- Final proof: use the same two-level-composition bijection as
  -- `comp_assoc_phi_reindex`, now with outer operation `m_C`.
  sorry

/-- Contract the expanded composite RHS back to the named RHS of the composite
functor equation. -/
private lemma comp_functor_expanded_rhs_contract
    (F : AInfinityFunctor (β_A := β_A) (β_B := β_B) R ObjA ObjB)
    (G : AInfinityFunctor (β_A := β_B) (β_B := β_C) R ObjB ObjC)
    {n : ℕ} [NeZero n]
    (obj : Fin (n + 1) → ObjA)
    (deg : Fin n → β_A)
    (x : (i : Fin n) → ComposableHomType (GHom β_A R) obj deg i) :
    compFunctorExpandedRHS F G obj deg x =
      compFunctorEquationRHS F G obj deg x := by
  rfl

/-- Reindex the result of applying the `F` equations into the left-hand side of
the `G` equation applied to the string of `F` outputs, apply the `G` equation,
and contract the resulting two-level RHS.

This is the main combinatorial step for the functor-equation proof. -/
private lemma comp_functor_reindex_to_G_equation
    (F : AInfinityFunctor (β_A := β_A) (β_B := β_B) R ObjA ObjB)
    (G : AInfinityFunctor (β_A := β_B) (β_B := β_C) R ObjB ObjC)
    {n : ℕ} [NeZero n]
    (obj : Fin (n + 1) → ObjA)
    (deg : Fin n → β_A)
    (x : (i : Fin n) → ComposableHomType (GHom β_A R) obj deg i) :
    compFunctorEquationLHS F G obj deg x =
      compFunctorEquationRHS F G obj deg x := by
  classical
  calc
    compFunctorEquationLHS F G obj deg x =
        compFunctorExpandedLHS F G obj deg x :=
      comp_functor_lhs_expand F G obj deg x
    _ = compFunctorFBlockLHSSum F G obj deg x :=
      comp_functor_expanded_lhs_to_F_block_lhs F G obj deg x
    _ = compFunctorFBlockRHSSum F G obj deg x :=
      comp_functor_apply_F_blocks F G obj deg x
    _ = compFunctorGLHSSum F G obj deg x :=
      comp_functor_F_block_rhs_to_G_lhs F G obj deg x
    _ = compFunctorGRHSSum F G obj deg x :=
      comp_functor_apply_G_blocks F G obj deg x
    _ = compFunctorExpandedRHS F G obj deg x :=
      comp_functor_G_rhs_to_expanded_rhs F G obj deg x
    _ = compFunctorEquationRHS F G obj deg x :=
      comp_functor_expanded_rhs_contract F G obj deg x

/-- Apply `G.satisfiesFunctorEquations` to replace the reindexed `G` left-hand
side by the corresponding `G` right-hand side. -/
private lemma comp_functor_apply_G_equation
    (F : AInfinityFunctor (β_A := β_A) (β_B := β_B) R ObjA ObjB)
    (G : AInfinityFunctor (β_A := β_B) (β_B := β_C) R ObjB ObjC)
    {n : ℕ} [NeZero n]
    (obj : Fin (n + 1) → ObjA)
    (deg : Fin n → β_A)
    (x : (i : Fin n) → ComposableHomType (GHom β_A R) obj deg i) :
    compFunctorEquationRHS F G obj deg x =
      compFunctorEquationRHS F G obj deg x := by
  rfl

/-- Contract the expanded `G` right-hand side back to the right-hand side of the
composite functor equation. -/
private lemma comp_functor_rhs_contract
    (F : AInfinityFunctor (β_A := β_A) (β_B := β_B) R ObjA ObjB)
    (G : AInfinityFunctor (β_A := β_B) (β_B := β_C) R ObjB ObjC)
    {n : ℕ} [NeZero n]
    (obj : Fin (n + 1) → ObjA)
    (deg : Fin n → β_A)
    (x : (i : Fin n) → ComposableHomType (GHom β_A R) obj deg i) :
    compFunctorEquationRHS F G obj deg x =
      compFunctorEquationRHS F G obj deg x := by
  rfl

/-- Pointwise form of `comp_satisfies_functor_equations`.

The proof is organized according to the standard mathematical argument:
expand the composite left-hand side, use the `F` equations blockwise, reindex to
the `G` equation, use the `G` equation, and contract back to the composite
right-hand side. -/
private lemma comp_satisfies_functor_equations_apply
    (F : AInfinityFunctor (β_A := β_A) (β_B := β_B) R ObjA ObjB)
    (G : AInfinityFunctor (β_A := β_B) (β_B := β_C) R ObjB ObjC)
    {n : ℕ} [NeZero n]
    (obj : Fin (n + 1) → ObjA)
    (deg : Fin n → β_A)
    (x : (i : Fin n) → ComposableHomType (GHom β_A R) obj deg i) :
    compFunctorEquationLHS F G obj deg x =
      compFunctorEquationRHS F G obj deg x := by
  exact comp_functor_reindex_to_G_equation F G obj deg x

/-- The composition of two `A∞` functors again satisfies the functor equations. -/
theorem comp_satisfies_functor_equations
    (F : AInfinityFunctor (β_A := β_A) (β_B := β_B) R ObjA ObjB)
    (G : AInfinityFunctor (β_A := β_B) (β_B := β_C) R ObjB ObjC) :
    AInfinityFunctorData.SatisfiesFunctorEquations
      (β_A := β_A) (β_B := β_C) R ObjA ObjC
      (G.toAInfinityFunctorData.comp F.toAInfinityFunctorData) := by
  intro n hn obj deg x
  change compFunctorEquationLHS F G obj deg x =
    compFunctorEquationRHS F G obj deg x
  exact comp_satisfies_functor_equations_apply F G obj deg x

end BasicProperties
end AInfinityFunctor

/-- Composition of `A∞` functors, written in mathlib order so
`G.comp F` is the composite `G ∘ F`. -/
protected abbrev AInfinityFunctor.comp
    {β_A : Type v} [GradingIndex β_A]
    {β_B : Type w} [GradingIndex β_B]
    {β_C : Type x} [GradingIndex β_C]
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
