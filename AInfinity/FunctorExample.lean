module

public import Mathlib
public import AInfinity.AInfinityFunctorComposition

@[expose] public section

open CategoryTheory Finset AInfinityTheory

noncomputable section

namespace AInfinityTheory
namespace FunctorExamples

universe u v w

variable (β : Type v) [GradingIndex β]
variable (R : Type u) [CommRing R]
variable (Obj : Type w)

/-- The degree translation for the identity A∞ functor. -/
abbrev identityDegTrans : β →+ β :=
  AddMonoidHom.id β

section Data

variable [AInfinityCategoryStruct β R Obj]

/-- The target module of the arity-one identity component is the original Hom-space. -/
lemma identityPhiOneTargetModuleEq
    (obj : Fin 2 → Obj)
    (deg : Fin 1 → β) :
    ComposableHomType (GHom β R) obj deg 0 =
      functorTargetType β β (GHom β R) id (identityDegTrans β) obj deg := by
  simp [functorTargetType, functorTargetDeg, ComposableHomType, identityDegTrans, shift_ofInt]

/-- The arity-one structure map of the identity A∞ functor. -/
def identityPhiOne
    (obj : Fin 2 → Obj)
    (deg : Fin 1 → β) :
    MultilinearMap R
      (fun i : Fin 1 => ComposableHomType (GHom β R) obj deg i)
      (functorTargetType β β (GHom β R) id (identityDegTrans β) obj deg) := by
  classical
  let f :
      MultilinearMap R
        (fun i : Fin 1 => ComposableHomType (GHom β R) obj deg i)
        (ComposableHomType (GHom β R) obj deg 0) :=
    MultilinearMap.mk'
      (R := R)
      (ι := Fin 1)
      (M₁ := fun i : Fin 1 => ComposableHomType (GHom β R) obj deg i)
      (M₂ := ComposableHomType (GHom β R) obj deg 0)
      (fun x => x 0)
      (by
        intro m i x y
        fin_cases i
        rfl)
      (by
        intro m i c x
        fin_cases i
        rfl)
  exact (identityPhiOneTargetModuleEq (β := β) (R := R) (Obj := Obj) obj deg) ▸ f

/-- The structure maps of the identity A∞ functor: arity one is the identity, and all
higher arities vanish. -/
def identityPhi
    {n : ℕ} [NeZero n]
    (obj : Fin (n + 1) → Obj)
    (deg : Fin n → β) :
    MultilinearMap R
      (fun i : Fin n => ComposableHomType (GHom β R) obj deg i)
      (functorTargetType β β (GHom β R) id (identityDegTrans β) obj deg) := by
  classical
  by_cases hn : n = 1
  · subst hn
    exact identityPhiOne (β := β) (R := R) (Obj := Obj) obj deg
  · exact 0

/-- The raw A∞ functor data of the identity functor on an A∞ category structure. -/
def identityFunctorData :
    AInfinityFunctorData (β_A := β) (β_B := β) R Obj Obj where
  objMap := id
  deg_trans := identityDegTrans β
  deg_trans_ofInt _n := rfl
  deg_trans_sign _b := rfl
  phi := identityPhi (β := β) (R := R) (Obj := Obj)

@[simp]
lemma identityPhi_eq_zero_of_ne_one
    {n : ℕ} [NeZero n]
    (obj : Fin (n + 1) → Obj)
    (deg : Fin n → β)
    (hn : n ≠ 1) :
    identityPhi (β := β) (R := R) (Obj := Obj) obj deg = 0 := by
  classical
  simp [identityPhi, hn]

@[simp]
lemma identityFunctorData_phi_eq_zero_of_ne_one
    {n : ℕ} [NeZero n]
    (obj : Fin (n + 1) → Obj)
    (deg : Fin n → β)
    (hn : n ≠ 1) :
    (identityFunctorData (β := β) (R := R) (Obj := Obj)).phi obj deg = 0 := by
  classical
  simpa [identityFunctorData] using
    (identityPhi_eq_zero_of_ne_one (β := β) (R := R) (Obj := Obj) obj deg hn)

end Data

section Proof

variable [AInfinityCategoryStruct β R Obj]

private lemma multilinearMap_eqRec_apply
    {ι : Type*} [DecidableEq ι] [Fintype ι]
    {M₁ : ι → Type u} [∀ i, AddCommMonoid (M₁ i)] [∀ i, Module R (M₁ i)]
    {M₂ M₂' : ModuleCat.{u} R}
    (h : M₂ = M₂')
    (f : MultilinearMap R M₁ M₂)
    (x : ∀ i, M₁ i) :
    (h ▸ f) x = cast (congrArg (fun M : ModuleCat R => (M : Type u)) h) (f x) := by
  subst h; rfl

private lemma identityPhiOne_apply
    (obj : Fin 2 → Obj)
    (deg : Fin 1 → β)
    (x : ∀ i : Fin 1, ComposableHomType (GHom β R) obj deg i) :
    identityPhiOne (β := β) (R := R) (Obj := Obj) obj deg x =
      cast
        (congrArg
          (fun M : ModuleCat R => (M : Type u))
          (identityPhiOneTargetModuleEq (β := β) (R := R) (Obj := Obj) obj deg))
        (x 0) := by
  unfold identityPhiOne
  exact multilinearMap_eqRec_apply (R := R)
    (identityPhiOneTargetModuleEq (β := β) (R := R) (Obj := Obj) obj deg) _ x

private lemma identity_functorLHSTerm_eq_zero_of_ne_one
    {n : ℕ}
    (obj : Fin (n + 1) → Obj)
    (deg : Fin n → β)
    (x : ∀ i : Fin n, ComposableHomType (GHom β R) obj deg i)
    (r s : ℕ)
    (hs : 1 ≤ s)
    (hr : r + s ≤ n)
    (houter : n + 1 - s ≠ 1) :
    AInfinityFunctorData.functorLHSTerm
      β β
      (GHom β R) (GHom β R)
      id (identityDegTrans β)
      (by intro n; rfl)
      (identityPhi (β := β) (R := R) (Obj := Obj))
      (AInfinityCategoryStruct.m (β := β) (R := R) (Obj := Obj))
      obj deg x r s hs hr = 0 := by
  classical
  let outerN := n + 1 - s
  let degOut := stasheffDegOut deg r s hr
  let objOut := stasheffObjOut obj r s hr
  let xOut : ∀ i : Fin outerN, ComposableHomType (GHom β R) objOut degOut i :=
    indexedStasheffXOut
      (GHom β R)
      (AInfinityCategoryStruct.m (β := β) (R := R) (Obj := Obj))
      obj deg x r s hs hr
  have houterN : 0 < outerN := by
    dsimp [outerN]
    exact indexedStasheffOuterArity_pos r s hr
  letI : NeZero outerN := ⟨Nat.ne_of_gt houterN⟩
  let outer :=
    identityPhi (β := β) (R := R) (Obj := Obj) objOut degOut xOut
  have houter_zero : outer = 0 := by
    have hmap :
        identityPhi (β := β) (R := R) (Obj := Obj) objOut degOut = 0 :=
      identityPhi_eq_zero_of_ne_one
        (β := β) (R := R) (Obj := Obj)
        objOut degOut houter
    dsimp [outer]
    simp [hmap]
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
      functorTargetType β β (GHom β R) id (identityDegTrans β) objOut degOut =
        AInfinityFunctorData.functorEqTargetType β β (GHom β R) id
          (identityDegTrans β) obj deg := by
    dsimp [functorTargetType, AInfinityFunctorData.functorEqTargetType]
    rw [hsource, htarget]
    exact congrArg _ <|
      AInfinityFunctorData.LHS_compatible_deg
        (β_A := β) (β_B := β)
        (deg_trans := identityDegTrans β)
        (deg_trans_ofInt := by intro k; rfl)
        deg r s hr
  unfold AInfinityFunctorData.functorLHSTerm
  simp [degOut, objOut, xOut, outer, houter_zero]
  simpa [eqRec_eq_cast] using cast_zero_of_module_eq (R := R) hdeg

/-- When the arity k equals 1, identityPhi acts as identity (up to HEq). -/
private lemma identityPhi_heq_of_eq_one {k : ℕ} [NeZero k] (hk : k = 1)
    (obj' : Fin (k + 1) → Obj) (deg' : Fin k → β)
    (x' : ∀ i : Fin k, ComposableHomType (GHom β R) obj' deg' i) :
    HEq (identityPhi (β := β) (R := R) (Obj := Obj) obj' deg' x')
         (x' ⟨0, by omega⟩) := by
  subst hk
  simp [identityPhi, identityPhiOne_apply (β := β) (R := R) (Obj := Obj)]

/-- If obj and deg are propositionally equal, then m gives HEq results.
    Allows different `NeZero` instances on the two sides. -/
private lemma m_heq_of_obj_deg_eq
    {n : ℕ} {inst₁ inst₂ : NeZero n}
    {O₁ O₂ : Fin (n + 1) → Obj}
    {D₁ D₂ : Fin n → β}
    (hO : O₁ = O₂) (hD : D₁ = D₂)
    (X₁ : ∀ i, ComposableHomType (GHom β R) O₁ D₁ i)
    (X₂ : ∀ i, ComposableHomType (GHom β R) O₂ D₂ i)
    (hX : HEq X₁ X₂) :
    HEq (@AInfinityCategoryStruct.m _ _ _ _ _ _ n inst₁ O₁ D₁ X₁)
         (@AInfinityCategoryStruct.m _ _ _ _ _ _ n inst₂ O₂ D₂ X₂) := by
  cases Subsingleton.elim inst₁ inst₂
  subst hO; subst hD; exact heq_of_eq (congrArg _ (eq_of_heq hX))

/-- The indexedStasheffXIn with r=0 is HEq to the original inputs.
    We generalize over the target obj/deg to enable subst. -/
private lemma m_xIn_heq_x_aux
    {n : ℕ} [NeZero n]
    {O₁ : Fin (n + 1) → Obj} {D₁ : Fin n → β}
    {O₂ : Fin (n + 1) → Obj} {D₂ : Fin n → β}
    (X₁ : ∀ i : Fin n, ComposableHomType (GHom β R) O₁ D₁ i)
    (X₂ : ∀ i : Fin n, ComposableHomType (GHom β R) O₂ D₂ i)
    (hO : O₁ = O₂) (hD : D₁ = D₂)
    (hX : ∀ i, HEq (X₁ i) (X₂ i)) :
    HEq X₁ X₂ := by
  subst hO; subst hD
  exact heq_of_eq (funext (fun i => eq_of_heq (hX i)))


private lemma identity_functorLHSTerm_eq_main
    {n : ℕ} [NeZero n]
    (obj : Fin (n + 1) → Obj)
    (deg : Fin n → β)
    (x : ∀ i : Fin n, ComposableHomType (GHom β R) obj deg i) :
    AInfinityFunctorData.functorLHSTerm
      β β
      (GHom β R) (GHom β R)
      id (identityDegTrans β)
      (by intro k; rfl)
      (identityPhi (β := β) (R := R) (Obj := Obj))
      (AInfinityCategoryStruct.m (β := β) (R := R) (Obj := Obj))
      obj deg x 0 n
      (Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne n)))
      (by simp) =
      AInfinityCategoryStruct.m (β := β) (R := R) (Obj := Obj) obj deg x := by
  classical
  -- Key equalities for r=0, s=n
  have hs : (1 : ℕ) ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne n))
  have hr : 0 + n ≤ n := by omega
  have hOuterN : n + 1 - n = 1 := by omega
  -- The LHS unfolds to hdeg ▸ (identityPhi objOut degOut xOut)
  -- Both sides live in the same type (operationTargetType = functorEqTargetType by rfl)
  -- We prove equality via eq_of_heq
  apply eq_of_heq
  unfold AInfinityFunctorData.functorLHSTerm
  -- Step 1: remove the outer cast
  refine HEq.trans (cast_heq _ _) ?_
  -- Step 2: identityPhi at outerN = 1 gives HEq to (xOut 0)
  haveI : NeZero (n + 1 - n) := ⟨by omega⟩
  refine HEq.trans (identityPhi_heq_of_eq_one (β := β) (R := R) (Obj := Obj) hOuterN _ _ _) ?_
  -- Step 3: xOut 0 at middle index is cast of indexedStasheffInner
  simp only [indexedStasheffXOut]
  simp only [show (0 < 0) = False from by decide, dif_neg (not_false), dif_pos trivial]
  refine HEq.trans (cast_heq _ _) ?_
  -- Step 4: indexedStasheffInner = m objIn degIn xIn, where objIn = obj, degIn = deg, xIn ≅ x
  unfold indexedStasheffInner
  -- m (stasheffObjIn obj 0 n) (stasheffDegIn deg 0 n) (indexedStasheffXIn ...)
  -- We need HEq to m obj deg x
  -- All three equalities hold propositionally
  have hobj : stasheffObjIn obj 0 n hr = obj := by ext i; simp [stasheffObjIn]
  have hdeg : stasheffDegIn deg 0 n hr = deg := by ext i; simp [stasheffDegIn]
  have hxin : HEq (indexedStasheffXIn (GHom β R) obj deg x 0 n hr) x := by
    apply Function.hfunext rfl
    intro i₁ i₂ hi
    have hi_eq : i₁ = i₂ := eq_of_heq hi
    subst hi_eq
    rw [indexedStasheffXIn_apply]
    exact congr_arg_heq x (Fin.ext (Nat.zero_add i₁.val))
  exact m_heq_of_obj_deg_eq (β := β) (R := R) (Obj := Obj) hobj hdeg _ _ hxin

/-
If one of the inner multilinear maps in a composition is zero,
    the entire composition is zero.
-/
private lemma compComposition_eq_zero_of_inner_zero
    {n : ℕ} (c : Composition n)
    {M : Fin n → Type*} {N : Fin c.length → Type*} {P : Type*}
    [∀ i, AddCommMonoid (M i)] [∀ l, AddCommMonoid (N l)] [AddCommMonoid P]
    [∀ i, Module R (M i)] [∀ l, Module R (N l)] [Module R P]
    (g : MultilinearMap R N P)
    (f : (l : Fin c.length) → MultilinearMap R (fun j => M (c.embedding l j)) (N l))
    (l0 : Fin c.length)
    (hf : f l0 = 0) :
    AInfinityFunctorData.MultilinearMap.compComposition c g f = 0 := by
  ext x;
  convert g.map_coord_zero l0 _;
  aesop

/-
Transporting a zero multilinear map along a codomain equality gives the zero map.
-/
private lemma eqRec_multilinearMap_zero
    {ι : Type*} [DecidableEq ι] [Fintype ι]
    {M₁ : ι → Type u} [∀ i, AddCommMonoid (M₁ i)] [∀ i, Module R (M₁ i)]
    {M₂ M₂' : ModuleCat.{u} R}
    (h : M₂ = M₂') :
    (h ▸ (0 : MultilinearMap R M₁ M₂)) = (0 : MultilinearMap R M₁ M₂') := by
  aesop

/-
Transporting a zero multilinear map by `cast` along a codomain equality still gives zero.
-/
private lemma cast_multilinearMap_zero
    {ι : Type*} [DecidableEq ι] [Fintype ι]
    {M₁ : ι → Type u} [∀ i, AddCommMonoid (M₁ i)] [∀ i, Module R (M₁ i)]
    {M₂ M₂' : ModuleCat.{u} R}
    (h : M₂ = M₂') :
    cast (congrArg (fun M : ModuleCat R => MultilinearMap R M₁ M) h)
      (0 : MultilinearMap R M₁ M₂) =
      (0 : MultilinearMap R M₁ M₂') := by
  subst h
  rfl

/-
Applying a multilinear map transported by `cast` is the same as transporting the value.
-/
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

/-
The `functorRHSTermMap` is the zero multilinear map whenever one of the inner
    phi-maps is zero (which happens for the identity functor at any block of size > 1).
-/
private lemma functorRHSTermMap_eq_zero_of_block_phi_zero
    {n : ℕ} [NeZero n]
    (obj : Fin (n + 1) → Obj)
    (deg : Fin n → β)
    (c : Composition n)
    (l0 : Fin c.length)
    [NeZero (c.blocksFun l0)]
    (hphi_zero : identityPhi (β := β) (R := R) (Obj := Obj)
      (AInfinityFunctorData.compositionBlockObj obj c l0)
      (AInfinityFunctorData.compositionBlockDeg β deg c l0) = 0) :
    AInfinityFunctorData.functorRHSTermMap
      β β
      (GHom β R) (GHom β R)
      id (identityDegTrans β)
      (identityPhi (β := β) (R := R) (Obj := Obj))
      (AInfinityCategoryStruct.m (β := β) (R := R) (Obj := Obj))
      obj deg c = 0 := by
  have hblock_zero :
      AInfinityFunctorData.functorRHSBlock
        β β
        (GHom β R) (GHom β R)
        id (identityDegTrans β)
        (identityPhi (β := β) (R := R) (Obj := Obj))
        obj deg c l0 = 0 := by
    unfold AInfinityFunctorData.functorRHSBlock
    simpa [hphi_zero] using
      (cast_multilinearMap_zero (R := R)
      (ι := Fin (c.blocksFun l0))
      (M₁ := fun j => ComposableHomType (GHom β R) obj deg (c.embedding l0 j))
      (AInfinityFunctorData.functor_rhs_block_module_eq
        (β_A := β) (β_B := β)
        (R := R)
        (BHom := GHom β R)
        (objMap := id)
        (deg_trans := identityDegTrans β)
        obj deg c l0))
  letI : NeZero c.length :=
    ⟨Nat.ne_of_gt (c.length_pos_of_pos (Nat.pos_of_ne_zero (NeZero.ne n)))⟩
  let f :
      (l : Fin c.length) →
        MultilinearMap R
          (fun j => ComposableHomType (GHom β R) obj deg (c.embedding l j))
          (ComposableHomType (GHom β R)
            (AInfinityFunctorData.functorCompositionOuterObj id obj c)
            (AInfinityFunctorData.functorCompositionOuterDeg β β (identityDegTrans β) deg c) l) :=
    fun l =>
      AInfinityFunctorData.functorRHSBlock
        β β
        (GHom β R) (GHom β R)
        id (identityDegTrans β)
        (identityPhi (β := β) (R := R) (Obj := Obj))
        obj deg c l
  have hf_zero : f l0 = 0 := by
    simpa [f] using hblock_zero
  let comp :
      MultilinearMap R
        (fun i => ComposableHomType (GHom β R) obj deg i)
        (operationTargetType
          (GHom β R)
          (AInfinityFunctorData.functorCompositionOuterObj id obj c)
          (AInfinityFunctorData.functorCompositionOuterDeg β β (identityDegTrans β) deg c)) :=
    AInfinityFunctorData.MultilinearMap.compComposition c
      (AInfinityCategoryStruct.m (β := β) (R := R) (Obj := Obj)
        (AInfinityFunctorData.functorCompositionOuterObj id obj c)
        (AInfinityFunctorData.functorCompositionOuterDeg β β (identityDegTrans β) deg c))
      f
  have hcomp_zero : comp = 0 := by
    ext x'
    dsimp [comp, AInfinityFunctorData.MultilinearMap.compComposition]
    exact
      (AInfinityCategoryStruct.m (β := β) (R := R) (Obj := Obj)
        (AInfinityFunctorData.functorCompositionOuterObj id obj c)
        (AInfinityFunctorData.functorCompositionOuterDeg β β (identityDegTrans β) deg c)).map_coord_zero
          l0 (by simp [hf_zero])
  unfold AInfinityFunctorData.functorRHSTermMap
  simpa [f, comp, hcomp_zero] using
    (cast_multilinearMap_zero (R := R)
    (ι := Fin n)
    (M₁ := fun i => ComposableHomType (GHom β R) obj deg i)
    (AInfinityFunctorData.functor_rhs_target_module_eq
      (β_A := β) (β_B := β)
      (R := R)
      (BHom := GHom β R)
      (objMap := id)
      (deg_trans := identityDegTrans β)
      obj deg c))

private lemma composition_exists_block_gt_one_of_ne_ones
    {n : ℕ}
    (c : Composition n)
    (hc : c ≠ Composition.ones n) :
    ∃ l : Fin c.length, 1 < c.blocksFun l := by
  obtain ⟨i, hi, hi_gt⟩ := Composition.ne_ones_iff.1 hc
  rw [← c.ofFn_blocksFun, List.mem_ofFn', Set.mem_range] at hi
  obtain ⟨l, rfl⟩ := hi
  exact ⟨l, hi_gt⟩

private lemma identity_functorRHSTerm_eq_zero_of_ne_ones
    {n : ℕ} [NeZero n]
    (obj : Fin (n + 1) → Obj)
    (deg : Fin n → β)
    (x : ∀ i : Fin n, ComposableHomType (GHom β R) obj deg i)
    (c : Composition n)
    (hc : c ≠ Composition.ones n) :
    AInfinityFunctorData.functorRHSTerm
      β β
      (GHom β R) (GHom β R)
      id (identityDegTrans β)
      (identityPhi (β := β) (R := R) (Obj := Obj))
      (AInfinityCategoryStruct.m (β := β) (R := R) (Obj := Obj))
      obj deg x c = 0 := by
  classical
  obtain ⟨l0, hl0⟩ := composition_exists_block_gt_one_of_ne_ones (c := c) hc
  letI : NeZero (c.blocksFun l0) :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one (c.one_le_blocksFun l0))⟩
  have hphi_zero : identityPhi (β := β) (R := R) (Obj := Obj)
      (AInfinityFunctorData.compositionBlockObj obj c l0)
      (AInfinityFunctorData.compositionBlockDeg β deg c l0) = 0 :=
    identityPhi_eq_zero_of_ne_one (β := β) (R := R) (Obj := Obj) _ _ (by
      exact Nat.ne_of_gt hl0)
  have hmap := functorRHSTermMap_eq_zero_of_block_phi_zero
    (β := β) (R := R) (Obj := Obj) obj deg c l0 hphi_zero
  show (AInfinityFunctorData.functorRHSTermMap
      β β (GHom β R) (GHom β R) id (identityDegTrans β)
      (identityPhi (β := β) (R := R) (Obj := Obj))
      (AInfinityCategoryStruct.m (β := β) (R := R) (Obj := Obj))
      obj deg c) x = 0
  simp [hmap]

/-- Generalized HEq for `m` across arity, object, degree, and input changes. -/
private lemma m_heq_of_arity_eq
    {n₁ n₂ : ℕ} {inst₁ : NeZero n₁} {inst₂ : NeZero n₂}
    (hn : n₁ = n₂)
    {O₁ : Fin (n₁ + 1) → Obj} {O₂ : Fin (n₂ + 1) → Obj}
    {D₁ : Fin n₁ → β} {D₂ : Fin n₂ → β}
    (hO : HEq O₁ O₂) (hD : HEq D₁ D₂)
    (X₁ : ∀ i, ComposableHomType (GHom β R) O₁ D₁ i)
    (X₂ : ∀ i, ComposableHomType (GHom β R) O₂ D₂ i)
    (hX : HEq X₁ X₂) :
    HEq (@AInfinityCategoryStruct.m _ _ _ _ _ _ n₁ inst₁ O₁ D₁ X₁)
         (@AInfinityCategoryStruct.m _ _ _ _ _ _ n₂ inst₂ O₂ D₂ X₂) := by
  subst hn
  cases Subsingleton.elim inst₁ inst₂
  have hO' := eq_of_heq hO
  have hD' := eq_of_heq hD
  subst hO'; subst hD'
  exact heq_of_eq (congrArg _ (eq_of_heq hX))

private lemma multilinearMap_eqRec_apply_heq
    {ι : Type*} [DecidableEq ι] [Fintype ι]
    {M₁ : ι → Type u} [∀ i, AddCommMonoid (M₁ i)] [∀ i, Module R (M₁ i)]
    {M₂ M₂' : ModuleCat.{u} R}
    (h : M₂ = M₂')
    (f : MultilinearMap R M₁ M₂)
    (x : ∀ i, M₁ i) :
    HEq ((h ▸ f) x) (f x) := by
  subst h; rfl


private lemma identity_functorRHSTerm_eq_main
    {n : ℕ} [NeZero n]
    (obj : Fin (n + 1) → Obj)
    (deg : Fin n → β)
    (x : ∀ i : Fin n, ComposableHomType (GHom β R) obj deg i) :
    AInfinityFunctorData.functorRHSTerm
      β β
      (GHom β R) (GHom β R)
      id (identityDegTrans β)
      (identityPhi (β := β) (R := R) (Obj := Obj))
      (AInfinityCategoryStruct.m (β := β) (R := R) (Obj := Obj))
      obj deg x (Composition.ones n) =
      AInfinityCategoryStruct.m (β := β) (R := R) (Obj := Obj) obj deg x := by
  classical
  unfold AInfinityFunctorData.functorRHSTerm
  unfold AInfinityFunctorData.functorRHSTermMap
  rw [multilinearMap_cast_apply (R := R)
      (h := AInfinityFunctorData.functor_rhs_target_module_eq
        (β_A := β) (β_B := β)
        (R := R)
        (BHom := GHom β R)
        (objMap := id)
        (deg_trans := identityDegTrans β)
        obj deg (Composition.ones n))]
  -- After unfolding, the LHS is:
  -- (cast hdeg (compComposition (ones n) (m outerObj outerDeg) functorRHSBlock)) x
  -- Use multilinearMap_cast_apply to separate the cast from the application
  -- Now goal is: cast ... (compComposition ... x) = m obj deg x
  -- Strip the cast using eq_of_heq + cast_heq
  apply eq_of_heq
  refine HEq.trans (cast_heq _ _) ?_
  -- Now goal is: HEq (compComposition ... x) (m obj deg x)
  -- compComposition unfolds to: m outerObj outerDeg (fun l => (hblock ▸ phi blockObj blockDeg) (fun j => x (emb l j)))
  -- Unfold compComposition to get m applied to phi outputs
  simp only [AInfinityFunctorData.MultilinearMap.compComposition]
  -- Use m_heq_of_arity_eq to match the two sides
  refine m_heq_of_arity_eq (β := β) (R := R) (Obj := Obj) (Composition.ones_length n) ?_ ?_ _ _ ?_
  · -- outerObj ≅ obj
    apply Function.hfunext (by simp [Composition.ones_length])
    intro l₁ l₂ hl
    have hl_eq : l₁.val = l₂.val :=
      (Fin.heq_ext_iff (by simp [Composition.ones_length])).mp hl
    dsimp [AInfinityFunctorData.functorCompositionOuterObj]
    simp only [Composition.boundary, Composition.ones_sizeUpTo]
    have hle : l₁.val ≤ n := by
      have h1 := l₁.isLt
      have h2 := Composition.ones_length n
      omega
    exact heq_of_eq (congrArg obj (Fin.ext (show min l₁.val n = l₂.val by omega)))
  · -- outerDeg ≅ deg
    apply Function.hfunext (by simp [Composition.ones_length])
    intro l₁ l₂ hl
    have hl_eq : l₁.val = l₂.val :=
      (Fin.heq_ext_iff (by simp [Composition.ones_length])).mp hl
    dsimp [AInfinityFunctorData.functorCompositionOuterDeg,
      AInfinityFunctorData.compositionBlockDeg]
    dsimp [functorTargetDeg, identityDegTrans, shift_ofInt]
    have hblock : (Composition.ones n).blocksFun l₁ = 1 := Composition.ones_blocksFun n l₁
    simp only [hblock, Nat.cast_one, sub_self, map_zero, add_zero]
    haveI : Subsingleton (Fin ((Composition.ones n).blocksFun l₁)) := by
      rw [hblock]; exact inferInstance
    rw [Fintype.sum_subsingleton _ ⟨0, by rw [hblock]; exact Nat.one_pos⟩]
    have hemb := Composition.ones_embedding l₁ (by rw [hblock]; exact Nat.one_pos)
    exact heq_of_eq (congrArg deg (by rw [Fin.ext_iff] at hemb ⊢; simpa using hemb.trans hl_eq))
  · -- phi outputs ≅ x
    apply Function.hfunext (by simp [Composition.ones_length])
    intro l₁ l₂ hl
    have hl_eq : l₁.val = l₂.val :=
      (Fin.heq_ext_iff (by simp [Composition.ones_length])).mp hl
    have hblock : (Composition.ones n).blocksFun l₁ = 1 := Composition.ones_blocksFun n l₁
    haveI : NeZero ((Composition.ones n).blocksFun l₁) := ⟨by rw [hblock]; exact one_ne_zero⟩
    unfold AInfinityFunctorData.functorRHSBlock
    refine HEq.trans
      (heq_of_eq <|
        multilinearMap_cast_apply (R := R)
          (h := AInfinityFunctorData.functor_rhs_block_module_eq
            (β_A := β) (β_B := β)
            (R := R)
            (BHom := GHom β R)
            (objMap := id)
            (deg_trans := identityDegTrans β)
            obj deg (Composition.ones n) l₁)
          _ _) ?_
    refine HEq.trans (cast_heq _ _) ?_
    refine HEq.trans (identityPhi_heq_of_eq_one (β := β) (R := R) (Obj := Obj) hblock _ _ _) ?_
    have hemb := Composition.ones_embedding l₁ (by rw [hblock]; exact Nat.one_pos)
    exact HEq.trans (congr_arg_heq x hemb) (congr_arg_heq x (Fin.ext hl_eq))


/-- The identity functor data satisfies the A∞ functor equations. -/
theorem identitySatisfiesFunctorEquations :
    AInfinityFunctorData.SatisfiesFunctorEquations
      (β_A := β) (β_B := β) R Obj Obj
      (identityFunctorData (β := β) (R := R) (Obj := Obj)) := by
  intro n _ obj deg x
  have hLHS :
      AInfinityFunctorData.functorLHSSum
        β β
        (GHom β R) (GHom β R)
        id (identityDegTrans β)
        (by intro k; rfl)
        (identityPhi (β := β) (R := R) (Obj := Obj))
        (AInfinityCategoryStruct.m (β := β) (R := R) (Obj := Obj))
        obj deg x =
      AInfinityCategoryStruct.m (β := β) (R := R) (Obj := Obj) obj deg x := by
    classical
    unfold AInfinityFunctorData.functorLHSSum
    rw [Finset.sum_eq_single ⟨0, by simp⟩]
    · rw [Finset.sum_eq_single ⟨n, by
            exact Finset.mem_Ico.mpr
              ⟨Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne n)), by simp⟩⟩]
      · have hsign : stasheffSign deg 0 n (by simp) = 1 := by
          haveI : IsEmpty (Fin (n - 0 - n)) := by
            simpa using (inferInstance : IsEmpty (Fin 0))
          simp [stasheffSign, stasheffSignParity]
        rw [hsign, one_smul]
        exact identity_functorLHSTerm_eq_main
          (β := β) (R := R) (Obj := Obj) obj deg x
      · intro s hs hsne
        have hslt : s.1 < n := by
          have hsmem : s.1 ∈ Finset.Ico 1 (n + 1) := by
            change s.1 ∈ Finset.Ico 1 (n - 0 + 1)
            exact s.2
          have hslt' : s.1 < n + 1 := (Finset.mem_Ico.mp hsmem).2
          have hsne' : s.1 ≠ n := by
            intro h
            apply hsne
            cases s
            exact Subtype.ext h
          omega
        have houter : n + 1 - s.1 ≠ 1 := by
          omega
        have hvalid : ValidStasheffIndices n 0 s.1 := by
          exact validStasheffIndices_of_mem_ranges (n := n) (by simp) s.2
        simp [identity_functorLHSTerm_eq_zero_of_ne_one
          (β := β) (R := R) (Obj := Obj)
          obj deg x 0 s.1 hvalid.1 hvalid.2 houter]
      · intro hs
        simp at hs
    · intro r hr hrne
      apply Finset.sum_eq_zero
      intro s hs
      have hvalid : ValidStasheffIndices n r.1 s.1 := by
        exact validStasheffIndices_of_mem_ranges (n := n) r.2 s.2
      have hrpos : 0 < r.1 := by
        have hrne' : r.1 ≠ 0 := by
          intro h
          apply hrne
          cases r
          exact Subtype.ext h
        exact Nat.pos_of_ne_zero hrne'
      have houter : n + 1 - s.1 ≠ 1 := by
        omega
      simp [identity_functorLHSTerm_eq_zero_of_ne_one
        (β := β) (R := R) (Obj := Obj)
        obj deg x r.1 s.1 hvalid.1 hvalid.2 houter]
    · intro hr
      simp at hr
  have hRHS :
      AInfinityFunctorData.functorRHSSum
        β β
        (GHom β R) (GHom β R)
        id (identityDegTrans β)
        (identityPhi (β := β) (R := R) (Obj := Obj))
        (AInfinityCategoryStruct.m (β := β) (R := R) (Obj := Obj))
        obj deg x =
      AInfinityCategoryStruct.m (β := β) (R := R) (Obj := Obj) obj deg x := by
    classical
    unfold AInfinityFunctorData.functorRHSSum
    rw [Finset.sum_eq_single (Composition.ones n)]
    · simpa using identity_functorRHSTerm_eq_main
        (β := β) (R := R) (Obj := Obj) obj deg x
    · intro c _ hc
      simp [identity_functorRHSTerm_eq_zero_of_ne_ones
        (β := β) (R := R) (Obj := Obj) obj deg x c hc]
    · intro hc
      simp at hc
  simpa [identityFunctorData] using hLHS.trans hRHS.symm

end Proof

section Functor

variable [AInfinityCategory β R Obj]

/-- The identity A∞ functor on an A∞ category. -/
def identityFunctor :
    AInfinityFunctor (β_A := β) (β_B := β) R Obj Obj where
  toAInfinityFunctorData := identityFunctorData (β := β) (R := R) (Obj := Obj)
  satisfiesFunctorEquations := identitySatisfiesFunctorEquations
    (β := β) (R := R) (Obj := Obj)

end Functor

section Composition

variable {β_A : Type*} [GradingIndex β_A]
variable {β_B : Type*} [GradingIndex β_B]
variable {ObjA : Type*} {ObjB : Type*}
variable [AInfinityCategory β_A R ObjA]
variable [AInfinityCategory β_B R ObjB]

/-- The `phi`-field of `F.comp identity` after unfolding only the outermost
composition.

This is the natural starting point for the right-identity proof on raw functor
data. The eventual proof should next analyze the sum over `Composition n`:
the `Composition.ones n` summand should reduce to `F.phi obj deg`, while every
other composition should vanish because the identity functor has only an
arity-one component. -/
private abbrev compIdentityFunctorPhiExpanded
    (F : AInfinityFunctorData (β_A := β_A) (β_B := β_B) R ObjA ObjB) :
    {n : ℕ} → [NeZero n] →
      (obj : Fin (n + 1) → ObjA) →
      (deg : Fin n → β_A) →
      MultilinearMap R
        (fun i : Fin n => ComposableHomType (GHom β_A R) obj deg i)
        (functorTargetType β_A β_B (GHom β_B R)
          (F.objMap ∘ id)
          (F.deg_trans.comp (identityDegTrans β_A))
          obj deg) :=
  fun {n : ℕ} [_inst : NeZero n]
      (obj : Fin (n + 1) → ObjA)
      (deg : Fin n → β_A) =>
    AInfinityFunctorData.compPhi β_A β_A β_B
      (GHom β_A R) (GHom β_A R) (GHom β_B R)
      id
      (identityDegTrans β_A)
      (identityFunctorData (β := β_A) (R := R) (Obj := ObjA)).phi
      F.objMap
      F.deg_trans
      F.deg_trans_ofInt
      F.phi
      obj deg

/-- The `phi`-field of `identity.comp F` after unfolding only the outermost
composition.

For the left-identity proof, the same outer sum over `Composition n` appears,
but now the outer functor is the identity. The intended strategy is again:
isolate the `Composition.ones n` term, show it reduces to `F.phi obj deg`, and
show that all remaining compositions vanish because some outer identity block
has arity strictly greater than one. -/
private abbrev identityFunctorCompPhiExpanded
    (F : AInfinityFunctorData (β_A := β_A) (β_B := β_B) R ObjA ObjB) :
    {n : ℕ} → [NeZero n] →
      (obj : Fin (n + 1) → ObjA) →
      (deg : Fin n → β_A) →
      MultilinearMap R
        (fun i : Fin n => ComposableHomType (GHom β_A R) obj deg i)
        (functorTargetType β_A β_B (GHom β_B R)
          (id ∘ F.objMap)
          ((identityDegTrans β_B).comp F.deg_trans)
          obj deg) :=
  fun {n : ℕ} [_inst : NeZero n]
      (obj : Fin (n + 1) → ObjA)
      (deg : Fin n → β_A) =>
    AInfinityFunctorData.compPhi β_A β_B β_B
      (GHom β_A R) (GHom β_B R) (GHom β_B R)
      F.objMap
      F.deg_trans
      F.phi
      id
      (identityDegTrans β_B)
      (by intro k; rfl)
      (identityFunctorData (β := β_B) (R := R) (Obj := ObjB)).phi
      obj deg

/-- Object-map field for the right-identity law on raw functor data.

This should be a one-line proof after unfolding `AInfinityFunctorData.comp`,
`identityFunctorData`, and `identityDegTrans`, then simplifying ordinary
function composition. -/
private lemma comp_identityFunctorData_objMap
    (F : AInfinityFunctorData (β_A := β_A) (β_B := β_B) R ObjA ObjB) :
    (F.comp (identityFunctorData (β := β_A) (R := R) (Obj := ObjA))).objMap = F.objMap := by
  sorry

/-- Degree-translation field for the right-identity law on raw functor data.

The proof should mirror `comp_identityFunctorData_objMap`, but now on
`AddMonoidHom`s. After unfolding, use that `identityDegTrans` is the identity
homomorphism and simplify `AddMonoidHom.comp`. -/
private lemma comp_identityFunctorData_degTrans
    (F : AInfinityFunctorData (β_A := β_A) (β_B := β_B) R ObjA ObjB) :
    (F.comp (identityFunctorData (β := β_A) (R := R) (Obj := ObjA))).deg_trans = F.deg_trans := by
  sorry

/-- Transport lemma for the `deg_trans_ofInt` field in the raw right-identity
law.

Recommended proof steps:
1. Rewrite the dependent codomain using `comp_identityFunctorData_degTrans`.
2. Reduce `HEq` to pointwise equality on `ℤ`.
3. Unfold `AInfinityFunctorData.comp`, `identityFunctorData`, and use the
   defining formula for `F.deg_trans_ofInt`. -/
private lemma comp_identityFunctorData_degTransOfInt
    (F : AInfinityFunctorData (β_A := β_A) (β_B := β_B) R ObjA ObjB) :
    HEq
      (F.comp (identityFunctorData (β := β_A) (R := R) (Obj := ObjA))).deg_trans_ofInt
      F.deg_trans_ofInt := by
  sorry

/-- Transport lemma for the `deg_trans_sign` field in the raw right-identity
law.

This should follow exactly the same pattern as
`comp_identityFunctorData_degTransOfInt`, but with the parity-preservation
field. The only substantive input should be `F.deg_trans_sign`. -/
private lemma comp_identityFunctorData_degTransSign
    (F : AInfinityFunctorData (β_A := β_A) (β_B := β_B) R ObjA ObjB) :
    HEq
      (F.comp (identityFunctorData (β := β_A) (R := R) (Obj := ObjA))).deg_trans_sign
      F.deg_trans_sign := by
  sorry

/-- First unfolding step for the `phi`-field in the raw right-identity law.

This lemma should be essentially definitional: unfold only the outermost
`AInfinityFunctorData.comp` and package the result as
`compIdentityFunctorPhiExpanded`. Keeping this separate prevents the later
proof from repeatedly unfolding the same large definition. -/
private lemma comp_identityFunctorData_phi_expand
    (F : AInfinityFunctorData (β_A := β_A) (β_B := β_B) R ObjA ObjB)
    {n : ℕ} [NeZero n]
    (obj : Fin (n + 1) → ObjA)
    (deg : Fin n → β_A) :
    (F.comp (identityFunctorData (β := β_A) (R := R) (Obj := ObjA))).phi obj deg =
      compIdentityFunctorPhiExpanded (R := R) F obj deg := by
  sorry

/-- Vanishing of non-`ones` summands in the right-identity `phi` proof.

What the future prover should do:
1. Unfold `compIdentityFunctorPhiExpanded` far enough to expose the summand
   `AInfinityFunctorData.compTermMultilinearMap`.
2. Use `composition_exists_block_gt_one_of_ne_ones` from earlier in this file
   to choose a block of size `> 1`.
3. Show that the corresponding inner block map coming from
   `identityFunctorData.phi` is zero via
   `identityFunctorData_phi_eq_zero_of_ne_one`.
4. Feed that zero block into
   `compComposition_eq_zero_of_inner_zero` or a directly analogous helper for
   `AInfinityFunctorData.compTermMultilinearMap`.

The important point is that every nontrivial composition forces at least one
identity component of arity greater than one, hence the whole term vanishes. -/
private lemma comp_identityFunctorData_phi_term_eq_zero_of_ne_ones
    (F : AInfinityFunctorData (β_A := β_A) (β_B := β_B) R ObjA ObjB)
    {n : ℕ} [NeZero n]
    (obj : Fin (n + 1) → ObjA)
    (deg : Fin n → β_A)
    (c : Composition n)
    (hc : c ≠ Composition.ones n) :
    AInfinityFunctorData.compTermMultilinearMap β_A β_A β_B
      (GHom β_A R) (GHom β_A R) (GHom β_B R)
      id
      (identityDegTrans β_A)
      (identityFunctorData (β := β_A) (R := R) (Obj := ObjA)).phi
      F.objMap
      F.deg_trans
      F.deg_trans_ofInt
      F.phi
      obj deg c = 0 := by
  sorry

/-- Identification of the `Composition.ones n` summand in the right-identity
`phi` proof.

Suggested route:
1. Unfold `AInfinityFunctorData.compTermMultilinearMap`,
   `AInfinityFunctorData.compTermBlock`, and
   `AInfinityFunctorData.MultilinearMap.compComposition` for `Composition.ones`.
2. Use `Composition.ones_length`, `Composition.ones_blocksFun`, and
   `Composition.ones_embedding` from the composition API to simplify the outer
   object string, outer degrees, and the block embeddings.
3. Invoke `identityPhi_heq_of_eq_one` from the proof of
   `identitySatisfiesFunctorEquations` to replace each identity block output by
   the original input.
4. Remove the transport casts exactly as in
   `identity_functorRHSTerm_eq_main`, whose proof is the closest local model.

After these simplifications, the remaining multilinear map should be exactly
`F.phi obj deg`. -/
private lemma comp_identityFunctorData_phi_term_eq_main
    (F : AInfinityFunctorData (β_A := β_A) (β_B := β_B) R ObjA ObjB)
    {n : ℕ} [NeZero n]
    (obj : Fin (n + 1) → ObjA)
    (deg : Fin n → β_A) :
    AInfinityFunctorData.compTermMultilinearMap β_A β_A β_B
      (GHom β_A R) (GHom β_A R) (GHom β_B R)
      id
      (identityDegTrans β_A)
      (identityFunctorData (β := β_A) (R := R) (Obj := ObjA)).phi
      F.objMap
      F.deg_trans
      F.deg_trans_ofInt
      F.phi
      obj deg (Composition.ones n) = F.phi obj deg := by
  sorry

/-- The `phi`-field for the raw right-identity law.

This should be a short assembly lemma:
1. Rewrite with `comp_identityFunctorData_phi_expand`.
2. Unfold the outer `compPhi` sum.
3. Use `Finset.sum_eq_single (Composition.ones n)`.
4. Discharge the main term with `comp_identityFunctorData_phi_term_eq_main`.
5. Discharge all other terms with
   `comp_identityFunctorData_phi_term_eq_zero_of_ne_ones`. -/
private lemma comp_identityFunctorData_phi
    (F : AInfinityFunctorData (β_A := β_A) (β_B := β_B) R ObjA ObjB)
    {n : ℕ} [NeZero n]
    (obj : Fin (n + 1) → ObjA)
    (deg : Fin n → β_A) :
    (F.comp (identityFunctorData (β := β_A) (R := R) (Obj := ObjA))).phi obj deg =
      F.phi obj deg := by
  sorry

/-- Raw right-identity law for `A∞` functor data.

The intended final proof should use the structure extensionality theorem for
`AInfinityFunctorData`, with the preceding helper lemmas solving the fields in
the order they appear:
`objMap`, `deg_trans`, `deg_trans_ofInt`, `deg_trans_sign`, and `phi`. -/
private theorem comp_identityFunctorData
    (F : AInfinityFunctorData (β_A := β_A) (β_B := β_B) R ObjA ObjB) :
    F.comp (identityFunctorData (β := β_A) (R := R) (Obj := ObjA)) = F := by
  sorry

/-- Object-map field for the left-identity law on raw functor data.

As in the right-identity proof, this should be a direct simplification after
unfolding `AInfinityFunctorData.comp` and `identityFunctorData`. -/
private lemma identityFunctor_compData_objMap
    (F : AInfinityFunctorData (β_A := β_A) (β_B := β_B) R ObjA ObjB) :
    ((identityFunctorData (β := β_B) (R := R) (Obj := ObjB)).comp F).objMap = F.objMap := by
  sorry

/-- Degree-translation field for the left-identity law on raw functor data.

The only real input here should be that `identityDegTrans` is the identity
homomorphism. After unfolding, simplify `AddMonoidHom.comp` in the opposite
order from the right-identity lemma. -/
private lemma identityFunctor_compData_degTrans
    (F : AInfinityFunctorData (β_A := β_A) (β_B := β_B) R ObjA ObjB) :
    ((identityFunctorData (β := β_B) (R := R) (Obj := ObjB)).comp F).deg_trans = F.deg_trans := by
  sorry

/-- Transport lemma for the `deg_trans_ofInt` field in the raw left-identity
law.

Use `identityFunctor_compData_degTrans` first, then prove pointwise equality on
`ℤ` by unfolding the composite field formula. -/
private lemma identityFunctor_compData_degTransOfInt
    (F : AInfinityFunctorData (β_A := β_A) (β_B := β_B) R ObjA ObjB) :
    HEq
      ((identityFunctorData (β := β_B) (R := R) (Obj := ObjB)).comp F).deg_trans_ofInt
      F.deg_trans_ofInt := by
  sorry

/-- Transport lemma for the `deg_trans_sign` field in the raw left-identity
law.

This is the parity analogue of
`identityFunctor_compData_degTransOfInt`; the proof should be completely
parallel. -/
private lemma identityFunctor_compData_degTransSign
    (F : AInfinityFunctorData (β_A := β_A) (β_B := β_B) R ObjA ObjB) :
    HEq
      ((identityFunctorData (β := β_B) (R := R) (Obj := ObjB)).comp F).deg_trans_sign
      F.deg_trans_sign := by
  sorry

/-- First unfolding step for the `phi`-field in the raw left-identity law.

This is the exact left-identity analogue of
`comp_identityFunctorData_phi_expand`. The later combinatorial proof should
work with `identityFunctorCompPhiExpanded` instead of repeatedly unfolding
`AInfinityFunctorData.comp`. -/
private lemma identityFunctor_compData_phi_expand
    (F : AInfinityFunctorData (β_A := β_A) (β_B := β_B) R ObjA ObjB)
    {n : ℕ} [NeZero n]
    (obj : Fin (n + 1) → ObjA)
    (deg : Fin n → β_A) :
    ((identityFunctorData (β := β_B) (R := R) (Obj := ObjB)).comp F).phi obj deg =
      identityFunctorCompPhiExpanded (R := R) F obj deg := by
  sorry

/-- Vanishing of non-`ones` summands in the left-identity `phi` proof.

The future proof should be modeled directly on
`identity_functorRHSTerm_eq_zero_of_ne_ones` from earlier in this file:
1. pick a block of size `> 1` using
   `composition_exists_block_gt_one_of_ne_ones`,
2. show the corresponding outer identity component is zero using
   `identityPhi_eq_zero_of_ne_one`,
3. conclude the entire term vanishes because the outer multilinear map itself
   is zero after transport.

Compared with the right-identity lemma, the zero now occurs in the outer
identity functor component rather than in an inner block. -/
private lemma identityFunctor_compData_phi_term_eq_zero_of_ne_ones
    (F : AInfinityFunctorData (β_A := β_A) (β_B := β_B) R ObjA ObjB)
    {n : ℕ} [NeZero n]
    (obj : Fin (n + 1) → ObjA)
    (deg : Fin n → β_A)
    (c : Composition n)
    (hc : c ≠ Composition.ones n) :
    AInfinityFunctorData.compTermMultilinearMap β_A β_B β_B
      (GHom β_A R) (GHom β_B R) (GHom β_B R)
      F.objMap
      F.deg_trans
      F.phi
      id
      (identityDegTrans β_B)
      (by intro k; rfl)
      (identityFunctorData (β := β_B) (R := R) (Obj := ObjB)).phi
      obj deg c = 0 := by
  sorry

/-- Identification of the `Composition.ones n` summand in the left-identity
`phi` proof.

This should be proved by following the simplification pattern in
`identity_functorRHSTerm_eq_main`, but now with `F` in the inner blocks and the
identity functor on the outside:
1. unfold `compTermMultilinearMap`,
2. simplify the outer object and degree data for `Composition.ones`,
3. identify each block output with the corresponding original input to the
   outer identity component,
4. use `identityPhi_heq_of_eq_one` to collapse that outer identity component to
   the value of `F.phi obj deg`. -/
private lemma identityFunctor_compData_phi_term_eq_main
    (F : AInfinityFunctorData (β_A := β_A) (β_B := β_B) R ObjA ObjB)
    {n : ℕ} [NeZero n]
    (obj : Fin (n + 1) → ObjA)
    (deg : Fin n → β_A) :
    AInfinityFunctorData.compTermMultilinearMap β_A β_B β_B
      (GHom β_A R) (GHom β_B R) (GHom β_B R)
      F.objMap
      F.deg_trans
      F.phi
      id
      (identityDegTrans β_B)
      (by intro k; rfl)
      (identityFunctorData (β := β_B) (R := R) (Obj := ObjB)).phi
      obj deg (Composition.ones n) = F.phi obj deg := by
  sorry

/-- The `phi`-field for the raw left-identity law.

The intended proof is the same short `sum_eq_single` assembly as in
`comp_identityFunctorData_phi`, but now using the left-identity helper lemmas. -/
private lemma identityFunctor_compData_phi
    (F : AInfinityFunctorData (β_A := β_A) (β_B := β_B) R ObjA ObjB)
    {n : ℕ} [NeZero n]
    (obj : Fin (n + 1) → ObjA)
    (deg : Fin n → β_A) :
    ((identityFunctorData (β := β_B) (R := R) (Obj := ObjB)).comp F).phi obj deg =
      F.phi obj deg := by
  sorry

/-- Raw left-identity law for `A∞` functor data.

Once the helper lemmas above are filled in, the final proof should again be a
straightforward application of structure extensionality for
`AInfinityFunctorData`. -/
private theorem identityFunctor_compData
    (F : AInfinityFunctorData (β_A := β_A) (β_B := β_B) R ObjA ObjB) :
    (identityFunctorData (β := β_B) (R := R) (Obj := ObjB)).comp F = F := by
  sorry


/-- Composing an `A∞` functor on the right with the identity functor on its source
gives back the original functor. -/
theorem comp_identityFunctor
    (F : AInfinityFunctor (β_A := β_A) (β_B := β_B) R ObjA ObjB) :
    F.comp (identityFunctor (β := β_A) (R := R) (Obj := ObjA)) = F := by
  -- Suggested final assembly:
  -- 1. Reduce from `AInfinityFunctor` equality to equality of the underlying
  --    `AInfinityFunctorData`.
  -- 2. Apply `comp_identityFunctorData` to the raw data.
  -- 3. Use proof irrelevance for the `satisfiesFunctorEquations` field.
  sorry

/-- Composing an `A∞` functor on the left with the identity functor on its target
gives back the original functor. -/
theorem identityFunctor_comp
    (F : AInfinityFunctor (β_A := β_A) (β_B := β_B) R ObjA ObjB) :
    (identityFunctor (β := β_B) (R := R) (Obj := ObjB)).comp F = F := by
  -- Suggested final assembly:
  -- 1. Reduce to the raw-data equality `identityFunctor_compData`.
  -- 2. Reuse proof irrelevance for the final proposition-valued field.
  -- 3. Keep this theorem tiny so all real work lives in the helper lemmas
  --    above.
  sorry

end Composition

end FunctorExamples
end AInfinityTheory

