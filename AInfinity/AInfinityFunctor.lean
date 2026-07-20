module

public import Mathlib
public import AInfinity.AInfinityCategory

@[expose] public section

open CategoryTheory Finset AInfinityTheory

noncomputable section

namespace AInfinityTheory

/-!
# A∞-functors

The general notion of an A∞-functor between (object-indexed) A∞-categories,
mirroring the design of `Stasheff.lean` / `AInfinityCategory.lean`:

* the data is an object map `F₀` together with, for every composable chain of
  `n` morphisms, a multilinear component `fₙ` of target degree `∑ deg + (1 − n)`
  (`functorTargetDeg`);
* the axioms `[SFₙ]` equate, in degree `∑ deg + (2 − n)` (`operationTargetDeg`),
  the *insertion* sum `∑ ± f_{n+1−s}(1^r ⊗ μ^C_s ⊗ 1^t)` (`indexedSFLeftSum`,
  reusing the `stasheff*` index machinery and the `stasheffSign` convention)
  with the *partition* sum `∑_c μ^D_k(f_{c₁} ⊗ ⋯ ⊗ f_{c_k})` over compositions
  `c` of `n` (`indexedSFRightSum`, indexed by `Composition n`).

Sign convention: the insertion side carries `stasheffSign`, the same convention
as `indexedStasheffSum`; the partition side carries no additional sign. Over a
`CharP R 2` base (the intended application) all sign conventions agree.
-/

universe u v w w'
variable {β : Type v} [Grading β]
variable {n : ℕ}

/-- Target degree of the `n`-th component of an A∞-functor: `∑ deg + (1 − n)`. -/
abbrev functorTargetDeg (deg : Fin n → β) : β :=
  (∑ i, deg i) + shift_ofInt (1 - (n : ℤ))

/-- The target type of the `n`-th component of an A∞-functor on a composable
string. -/
abbrev functorTargetType
    {R : Type u} [CommRing R]
    {ObjC : Type w} {ObjD : Type w'}
    (HomD : ObjD → ObjD → GradedRModule (β := β) (R := R))
    (F₀ : ObjC → ObjD)
    (obj : Fin (n + 1) → ObjC)
    (deg : Fin n → β) : ModuleCat R :=
  HomD (F₀ (obj 0)) (F₀ (obj (Fin.last n))) (functorTargetDeg deg)

/-- Degree bookkeeping for the insertion side of `[SFₙ]`: inserting `μₛ` and
applying `F_{n+1−s}` lands at `∑ deg + (2 − n) = operationTargetDeg deg`. -/
lemma sfLeftDegOut_sum
    (deg : Fin n → β)
    (r s : ℕ)
    (hr : r + s ≤ n) :
    (∑ i : Fin (n + 1 - s), stasheffDegOut deg r s hr i) +
      shift_ofInt (1 - ((n + 1 - s : ℕ) : ℤ)) =
    operationTargetDeg deg := by
  rw [stasheffDegOut_sum_core deg r s hr, add_assoc]
  congr 1
  show shift_ofInt (2 - (s : ℤ)) + shift_ofInt (1 - ((n + 1 - s : ℕ) : ℤ)) =
    shift_ofInt (2 - (n : ℤ))
  unfold shift_ofInt
  rw [← map_add]
  congr 1
  rw [Nat.cast_sub (by omega : s ≤ n + 1)]
  push_cast
  omega

/-- The `(r, s)` insertion term of the `[SFₙ]` equation:
`f_{n+1−s}(x₁, …, x_r, μ^C_s(x_{r+1}, …, x_{r+s}), …, x_n)`. -/
def indexedSFLeftTerm
    {R : Type u} [CommRing R]
    {ObjC : Type w} {ObjD : Type w'}
    (HomC : ObjC → ObjC → GradedRModule (β := β) (R := R))
    (HomD : ObjD → ObjD → GradedRModule (β := β) (R := R))
    (F₀ : ObjC → ObjD)
    (mC : {n : ℕ+} → (obj : Fin ((n : ℕ) + 1) → ObjC) → (deg : Fin (n : ℕ) → β) →
      MultilinearMap R
        (fun i : Fin (n : ℕ) => composableHomType HomC obj deg i)
        (operationTargetType HomC obj deg))
    (f : {n : ℕ+} → (obj : Fin ((n : ℕ) + 1) → ObjC) → (deg : Fin (n : ℕ) → β) →
      MultilinearMap R
        (fun i : Fin (n : ℕ) => composableHomType HomC obj deg i)
        (functorTargetType HomD F₀ obj deg))
    {n : ℕ+}
    (obj : Fin ((n : ℕ) + 1) → ObjC)
    (deg : Fin (n : ℕ) → β)
    (x : ∀ i : Fin (n : ℕ), composableHomType HomC obj deg i)
    (r s : ℕ)
    (hs : 1 ≤ s)
    (hr : r + s ≤ (n : ℕ)) :
    HomD (F₀ (obj 0)) (F₀ (obj (Fin.last (n : ℕ)))) (operationTargetDeg deg) := by
  let degIn := stasheffDegIn deg r s hr
  let objIn := stasheffObjIn obj r s hr
  let xIn : ∀ i : Fin s, composableHomType HomC objIn degIn i := fun i => by
    simpa [composableHomType, objIn, stasheffObjIn, degIn, stasheffDegIn]
      using x ⟨r + i.val, by omega⟩
  let inner := mC (n := ⟨s, hs⟩) objIn degIn xIn
  let outerN : ℕ := (n : ℕ) + 1 - s
  let degOut := stasheffDegOut deg r s hr
  let objOut := stasheffObjOut obj r s hr
  let xOut : ∀ i : Fin outerN, composableHomType HomC objOut degOut i := by
    intro i
    by_cases hlt : i.val < r
    · simpa [composableHomType, objOut, stasheffObjOut, degOut, stasheffDegOut, hlt,
        Nat.le_of_lt hlt]
        using x ⟨i.val, by omega⟩
    · by_cases heq : i.val = r
      · simpa
          [composableHomType, operationTargetType, objIn, stasheffObjIn,
            degIn, stasheffDegIn, objOut, stasheffObjOut, degOut, stasheffDegOut,
            stasheffInnerDeg, hlt, heq]
          using inner
      · have hgt : ¬ i.val ≤ r := by omega
        have hsucc : i.val + s - 1 + 1 = i.val + s := by omega
        simpa
          [composableHomType, objOut, stasheffObjOut, degOut, stasheffDegOut,
            hlt, heq, hgt, hsucc]
          using x ⟨i.val + s - 1, by omega⟩
  have houterN : 0 < outerN := by
    dsimp [outerN]
    omega
  let outer := f (n := ⟨outerN, houterN⟩) objOut degOut xOut
  have hsource : objOut 0 = obj 0 := by
    simp [objOut, stasheffObjOut]
  have hlast_gt : ¬ outerN ≤ r := by
    dsimp [outerN]
    omega
  have htarget : objOut (Fin.last outerN) = obj (Fin.last (n : ℕ)) := by
    simp [objOut, stasheffObjOut, Fin.last, hlast_gt]
    congr
    omega
  have hdeg :
      functorTargetType HomD F₀ objOut degOut =
        HomD (F₀ (obj 0)) (F₀ (obj (Fin.last (n : ℕ)))) (operationTargetDeg deg) := by
    dsimp [functorTargetType]
    rw [hsource, htarget]
    exact congrArg (fun d => HomD (F₀ (obj 0)) (F₀ (obj (Fin.last (n : ℕ)))) d)
      (sfLeftDegOut_sum deg r s hr)
  exact hdeg ▸ outer

/-- The insertion side of the `[SFₙ]` equation, with the `stasheffSign`
convention. -/
def indexedSFLeftSum
    {R : Type u} [CommRing R]
    {ObjC : Type w} {ObjD : Type w'}
    (HomC : ObjC → ObjC → GradedRModule (β := β) (R := R))
    (HomD : ObjD → ObjD → GradedRModule (β := β) (R := R))
    (F₀ : ObjC → ObjD)
    (mC : {n : ℕ+} → (obj : Fin ((n : ℕ) + 1) → ObjC) → (deg : Fin (n : ℕ) → β) →
      MultilinearMap R
        (fun i : Fin (n : ℕ) => composableHomType HomC obj deg i)
        (operationTargetType HomC obj deg))
    (f : {n : ℕ+} → (obj : Fin ((n : ℕ) + 1) → ObjC) → (deg : Fin (n : ℕ) → β) →
      MultilinearMap R
        (fun i : Fin (n : ℕ) => composableHomType HomC obj deg i)
        (functorTargetType HomD F₀ obj deg))
    {n : ℕ+}
    (obj : Fin ((n : ℕ) + 1) → ObjC)
    (deg : Fin (n : ℕ) → β)
    (x : ∀ i : Fin (n : ℕ), composableHomType HomC obj deg i) :
    HomD (F₀ (obj 0)) (F₀ (obj (Fin.last (n : ℕ)))) (operationTargetDeg deg) :=
  Finset.sum ((Finset.range ((n : ℕ) + 1)).attach) fun r =>
    Finset.sum ((Finset.Ico 1 ((n : ℕ) - r.1 + 1)).attach) fun s =>
      let h : validStasheffIndices (n : ℕ) r.1 s.1 :=
        validStasheffIndices_of_mem_ranges (n := (n : ℕ)) r.2 s.2
      (stasheffSign deg r.1 s.1 h.2) •
        indexedSFLeftTerm HomC HomD F₀ mC f obj deg x r.1 s.1 h.1 h.2

/-- Every block of a composition stays inside the ambient index range. -/
lemma Composition.sizeUpTo_add_blocksFun_le {n : ℕ} (c : Composition n)
    (j : Fin c.length) : c.sizeUpTo j.val + c.blocksFun j ≤ n := by
  have h1 := c.sizeUpTo_succ' j
  have h2 := c.sizeUpTo_le (j.val + 1)
  omega

/-- Degree bookkeeping for the partition side of `[SFₙ]`: applying `μ^D_k` to
the `F`-images of the blocks of a composition `c` of `n` lands at
`∑ deg + (2 − n) = operationTargetDeg deg`. -/
lemma sfRightDeg_sum {n : ℕ} (deg : Fin n → β) (c : Composition n) :
    (∑ j : Fin c.length,
        functorTargetDeg (fun i : Fin (c.blocksFun j) =>
          deg ⟨c.sizeUpTo j.val + i.val,
            by have := c.sizeUpTo_add_blocksFun_le j; omega⟩)) +
      shift_ofInt (2 - (c.length : ℤ)) =
    operationTargetDeg deg := by
  unfold functorTargetDeg operationTargetDeg
  rw [Finset.sum_add_distrib]
  have hsum : (∑ j : Fin c.length, ∑ i : Fin (c.blocksFun j),
      deg ⟨c.sizeUpTo j.val + i.val,
        by have := c.sizeUpTo_add_blocksFun_le j; omega⟩) = ∑ i, deg i := by
    rw [Finset.sum_sigma', Finset.univ_sigma_univ]
    exact Fintype.sum_equiv c.blocksFinEquiv _ _ fun p =>
      congrArg deg (Fin.ext (by
        show c.sizeUpTo p.1.val + p.2.val = ((c.embedding p.1) p.2 : Fin n).val
        rw [Composition.coe_embedding]))
  have hshift : (∑ j : Fin c.length, shift_ofInt (β := β) (1 - (c.blocksFun j : ℤ))) +
      shift_ofInt (2 - (c.length : ℤ)) = shift_ofInt (2 - (n : ℤ)) := by
    unfold shift_ofInt
    rw [← map_sum, ← map_add]
    congr 1
    have hb : (∑ j : Fin c.length, ((c.blocksFun j : ℤ))) = (n : ℤ) := by
      rw [← Nat.cast_sum]
      exact congrArg _ c.sum_blocksFun
    rw [Finset.sum_sub_distrib, hb]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    ring
  calc (∑ j : Fin c.length, ∑ i : Fin (c.blocksFun j),
          deg ⟨c.sizeUpTo j.val + i.val,
            by have := c.sizeUpTo_add_blocksFun_le j; omega⟩) +
        (∑ j : Fin c.length, shift_ofInt (β := β) (1 - (c.blocksFun j : ℤ))) +
        shift_ofInt (2 - (c.length : ℤ))
      = (∑ i, deg i) +
        ((∑ j : Fin c.length, shift_ofInt (β := β) (1 - (c.blocksFun j : ℤ))) +
          shift_ofInt (2 - (c.length : ℤ))) := by rw [hsum, add_assoc]
    _ = (∑ i, deg i) + shift_ofInt (2 - (n : ℤ)) := by rw [hshift]

/-- The term of the partition side of `[SFₙ]` attached to a composition `c` of
`n`: `μ^D_k(f_{c₁}(x₁, …), …, f_{c_k}(…, x_n))` where `k = c.length` and `cⱼ`
are the block sizes. -/
def indexedSFRightTerm
    {R : Type u} [CommRing R]
    {ObjC : Type w} {ObjD : Type w'}
    (HomC : ObjC → ObjC → GradedRModule (β := β) (R := R))
    (HomD : ObjD → ObjD → GradedRModule (β := β) (R := R))
    (F₀ : ObjC → ObjD)
    (mD : {n : ℕ+} → (obj : Fin ((n : ℕ) + 1) → ObjD) → (deg : Fin (n : ℕ) → β) →
      MultilinearMap R
        (fun i : Fin (n : ℕ) => composableHomType HomD obj deg i)
        (operationTargetType HomD obj deg))
    (f : {n : ℕ+} → (obj : Fin ((n : ℕ) + 1) → ObjC) → (deg : Fin (n : ℕ) → β) →
      MultilinearMap R
        (fun i : Fin (n : ℕ) => composableHomType HomC obj deg i)
        (functorTargetType HomD F₀ obj deg))
    {n : ℕ+}
    (obj : Fin ((n : ℕ) + 1) → ObjC)
    (deg : Fin (n : ℕ) → β)
    (x : ∀ i : Fin (n : ℕ), composableHomType HomC obj deg i)
    (c : Composition (n : ℕ)) :
    HomD (F₀ (obj 0)) (F₀ (obj (Fin.last (n : ℕ)))) (operationTargetDeg deg) := by
  -- the `j`-th block of the chain
  let objSeg : ∀ j : Fin c.length, Fin (c.blocksFun j + 1) → ObjC := fun j i =>
    obj ⟨c.sizeUpTo j.val + i.val,
      by have := c.sizeUpTo_add_blocksFun_le j; omega⟩
  let degSeg : ∀ j : Fin c.length, Fin (c.blocksFun j) → β := fun j i =>
    deg ⟨c.sizeUpTo j.val + i.val,
      by have := c.sizeUpTo_add_blocksFun_le j; omega⟩
  let xSeg : ∀ (j : Fin c.length) (i : Fin (c.blocksFun j)),
      composableHomType HomC (objSeg j) (degSeg j) i := fun j i => by
    simpa [composableHomType, objSeg, degSeg]
      using x ⟨c.sizeUpTo j.val + i.val,
        by have := c.sizeUpTo_add_blocksFun_le j; omega⟩
  -- the `F`-image of each block
  let Fblock : ∀ j : Fin c.length, functorTargetType HomD F₀ (objSeg j) (degSeg j) :=
    fun j => f (n := ⟨c.blocksFun j, c.one_le_blocksFun j⟩) (objSeg j) (degSeg j) (xSeg j)
  -- the outer chain in the target category
  let objOut : Fin (c.length + 1) → ObjD := fun j =>
    F₀ (obj ⟨c.sizeUpTo j.val, by have := c.sizeUpTo_le j.val; omega⟩)
  let degOut : Fin c.length → β := fun j => functorTargetDeg (degSeg j)
  let xOut : ∀ j : Fin c.length, composableHomType HomD objOut degOut j := fun j => by
    have hsucc : c.sizeUpTo (j.val + 1) = c.sizeUpTo j.val + c.blocksFun j :=
      c.sizeUpTo_succ' j
    simpa [composableHomType, functorTargetType, objOut, degOut, objSeg, degSeg, hsucc]
      using Fblock j
  have hlen : 0 < c.length := c.length_pos_of_pos n.pos
  let outer := mD (n := ⟨c.length, hlen⟩) objOut degOut xOut
  have hsource : objOut 0 = F₀ (obj 0) := by
    simp only [objOut]
    exact congrArg F₀ (congrArg obj (Fin.ext (by simp [Composition.sizeUpTo_zero])))
  have htarget : objOut (Fin.last c.length) = F₀ (obj (Fin.last (n : ℕ))) := by
    simp only [objOut]
    exact congrArg F₀ (congrArg obj (Fin.ext (by simp [Fin.last, Composition.sizeUpTo_length])))
  have hdeg :
      operationTargetType HomD objOut degOut =
        HomD (F₀ (obj 0)) (F₀ (obj (Fin.last (n : ℕ)))) (operationTargetDeg deg) := by
    dsimp [operationTargetType]
    rw [hsource, htarget]
    exact congrArg (fun d => HomD (F₀ (obj 0)) (F₀ (obj (Fin.last (n : ℕ)))) d)
      (sfRightDeg_sum deg c)
  exact hdeg ▸ outer

/-- The partition side of the `[SFₙ]` equation: the sum over all compositions
`c` of `n` of `μ^D_{c.length}` applied to the `F`-images of the blocks. -/
def indexedSFRightSum
    {R : Type u} [CommRing R]
    {ObjC : Type w} {ObjD : Type w'}
    (HomC : ObjC → ObjC → GradedRModule (β := β) (R := R))
    (HomD : ObjD → ObjD → GradedRModule (β := β) (R := R))
    (F₀ : ObjC → ObjD)
    (mD : {n : ℕ+} → (obj : Fin ((n : ℕ) + 1) → ObjD) → (deg : Fin (n : ℕ) → β) →
      MultilinearMap R
        (fun i : Fin (n : ℕ) => composableHomType HomD obj deg i)
        (operationTargetType HomD obj deg))
    (f : {n : ℕ+} → (obj : Fin ((n : ℕ) + 1) → ObjC) → (deg : Fin (n : ℕ) → β) →
      MultilinearMap R
        (fun i : Fin (n : ℕ) => composableHomType HomC obj deg i)
        (functorTargetType HomD F₀ obj deg))
    {n : ℕ+}
    (obj : Fin ((n : ℕ) + 1) → ObjC)
    (deg : Fin (n : ℕ) → β)
    (x : ∀ i : Fin (n : ℕ), composableHomType HomC obj deg i) :
    HomD (F₀ (obj 0)) (F₀ (obj (Fin.last (n : ℕ)))) (operationTargetDeg deg) :=
  ∑ c : Composition (n : ℕ),
    indexedSFRightTerm HomC HomD F₀ mD f obj deg x c

/-- The `[SFₙ]` axioms for object-indexed A∞-functor data: for every composable
chain, the insertion sum equals the partition sum. -/
def indexedSatisfiesSF
    {R : Type u} [CommRing R]
    {ObjC : Type w} {ObjD : Type w'}
    (HomC : ObjC → ObjC → GradedRModule (β := β) (R := R))
    (HomD : ObjD → ObjD → GradedRModule (β := β) (R := R))
    (F₀ : ObjC → ObjD)
    (mC : {n : ℕ+} → (obj : Fin ((n : ℕ) + 1) → ObjC) → (deg : Fin (n : ℕ) → β) →
      MultilinearMap R
        (fun i : Fin (n : ℕ) => composableHomType HomC obj deg i)
        (operationTargetType HomC obj deg))
    (mD : {n : ℕ+} → (obj : Fin ((n : ℕ) + 1) → ObjD) → (deg : Fin (n : ℕ) → β) →
      MultilinearMap R
        (fun i : Fin (n : ℕ) => composableHomType HomD obj deg i)
        (operationTargetType HomD obj deg))
    (f : {n : ℕ+} → (obj : Fin ((n : ℕ) + 1) → ObjC) → (deg : Fin (n : ℕ) → β) →
      MultilinearMap R
        (fun i : Fin (n : ℕ) => composableHomType HomC obj deg i)
        (functorTargetType HomD F₀ obj deg)) : Prop :=
  ∀ (n : ℕ+) (obj : Fin ((n : ℕ) + 1) → ObjC) (deg : Fin (n : ℕ) → β)
    (x : ∀ i : Fin (n : ℕ), composableHomType HomC obj deg i),
    indexedSFLeftSum HomC HomD F₀ mC f obj deg x =
      indexedSFRightSum HomC HomD F₀ mD f obj deg x

/-! ### Vanishing criteria for the SF terms

Mirrors the corresponding facts for `indexedStasheffTerm`: a term dies when its
outer map is zero, or when its inner map is zero (a coordinate of the outer
input vector becomes a cast of `0`). The map-vanishing hypotheses are
universally quantified over the arity proof and the whole chain, matching the
intended uses (`μₖ = 0` identically, `fₖ = 0` from truncation). -/

private lemma modcat_cast_zero {R : Type u} [CommRing R] {A B : ModuleCat R} (h : A = B) :
    h ▸ (0 : A) = (0 : B) := by cases h; rfl

private lemma modcat_cast_zero_iff {R : Type u} [CommRing R] {A B : ModuleCat R}
    (h : A = B) {a : A} : h ▸ a = (0 : B) ↔ a = (0 : A) := by cases h; simp

private lemma modcat_cast_zero_of_eq {R : Type u} [CommRing R] {A B : ModuleCat R}
    (h : A = B) {T_mid : Type*} (h₁ : ↑A = T_mid) (h₂ : ↑B = T_mid) :
    Eq.mpr h₂ (Eq.mp h₁ (0 : ↑A)) = (0 : ↑B) := by
  subst h; subst h₁; cases h₂; rfl

/-- If the outer functor component vanishes identically, the insertion term
vanishes. -/
theorem indexedSFLeftTerm_outer_zero
    {R : Type u} [CommRing R]
    {ObjC : Type w} {ObjD : Type w'}
    (HomC : ObjC → ObjC → GradedRModule (β := β) (R := R))
    (HomD : ObjD → ObjD → GradedRModule (β := β) (R := R))
    (F₀ : ObjC → ObjD)
    (mC : {n : ℕ+} → (obj : Fin ((n : ℕ) + 1) → ObjC) → (deg : Fin (n : ℕ) → β) →
      MultilinearMap R
        (fun i : Fin (n : ℕ) => composableHomType HomC obj deg i)
        (operationTargetType HomC obj deg))
    (f : {n : ℕ+} → (obj : Fin ((n : ℕ) + 1) → ObjC) → (deg : Fin (n : ℕ) → β) →
      MultilinearMap R
        (fun i : Fin (n : ℕ) => composableHomType HomC obj deg i)
        (functorTargetType HomD F₀ obj deg))
    {n : ℕ+}
    (obj : Fin ((n : ℕ) + 1) → ObjC)
    (deg : Fin (n : ℕ) → β)
    (x : ∀ i : Fin (n : ℕ), composableHomType HomC obj deg i)
    {r s : ℕ} {hs : 1 ≤ s} {hr : r + s ≤ (n : ℕ)}
    (hm : ∀ (h : 0 < (n : ℕ) + 1 - s) (o : Fin ((n : ℕ) + 1 - s + 1) → ObjC)
      (d : Fin ((n : ℕ) + 1 - s) → β), f (n := ⟨(n : ℕ) + 1 - s, h⟩) o d = 0) :
    indexedSFLeftTerm HomC HomD F₀ mC f obj deg x r s hs hr = 0 := by
  simp only [indexedSFLeftTerm, hm, MultilinearMap.zero_apply]
  exact modcat_cast_zero _

set_option maxHeartbeats 800000 in
/-- If the inner source operation vanishes identically, the insertion term
vanishes. -/
theorem indexedSFLeftTerm_inner_zero
    {R : Type u} [CommRing R]
    {ObjC : Type w} {ObjD : Type w'}
    (HomC : ObjC → ObjC → GradedRModule (β := β) (R := R))
    (HomD : ObjD → ObjD → GradedRModule (β := β) (R := R))
    (F₀ : ObjC → ObjD)
    (mC : {n : ℕ+} → (obj : Fin ((n : ℕ) + 1) → ObjC) → (deg : Fin (n : ℕ) → β) →
      MultilinearMap R
        (fun i : Fin (n : ℕ) => composableHomType HomC obj deg i)
        (operationTargetType HomC obj deg))
    (f : {n : ℕ+} → (obj : Fin ((n : ℕ) + 1) → ObjC) → (deg : Fin (n : ℕ) → β) →
      MultilinearMap R
        (fun i : Fin (n : ℕ) => composableHomType HomC obj deg i)
        (functorTargetType HomD F₀ obj deg))
    {n : ℕ+}
    (obj : Fin ((n : ℕ) + 1) → ObjC)
    (deg : Fin (n : ℕ) → β)
    (x : ∀ i : Fin (n : ℕ), composableHomType HomC obj deg i)
    {r s : ℕ} {hs : 1 ≤ s} {hr : r + s ≤ (n : ℕ)}
    (hm : ∀ (h : 0 < s) (o : Fin (s + 1) → ObjC) (d : Fin s → β),
      mC (n := ⟨s, h⟩) o d = 0) :
    indexedSFLeftTerm HomC HomD F₀ mC f obj deg x r s hs hr = 0 := by
  apply modcat_cast_zero_iff _ |>.mpr
  convert MultilinearMap.map_coord_zero _ _ _
  exact ⟨r, Nat.lt_sub_of_add_lt (by omega)⟩
  convert modcat_cast_zero_of_eq _ _ _
  rotate_left
  exact operationTargetType HomC (stasheffObjIn obj r s hr) (stasheffDegIn deg r s hr)
  all_goals norm_num [operationTargetType, composableHomType]
  rotate_left
  exact ↑(HomC (stasheffObjIn obj r s hr 0) (stasheffObjIn obj r s hr (Fin.last s))
    (operationTargetDeg (stasheffDegIn deg r s hr)))
  · rfl
  · unfold stasheffObjOut stasheffObjIn stasheffDegOut operationTargetDeg
    simp +decide [Nat.mod_eq_of_lt]
    rfl
  · exact (hm (by omega) _ _).symm ▸ rfl
  · simp +decide [stasheffObjIn, stasheffObjOut, stasheffDegIn, stasheffDegOut,
      operationTargetDeg]
    congr! 2

/-- If the target operation at the partition length vanishes identically, the
partition term vanishes. -/
theorem indexedSFRightTerm_outer_zero
    {R : Type u} [CommRing R]
    {ObjC : Type w} {ObjD : Type w'}
    (HomC : ObjC → ObjC → GradedRModule (β := β) (R := R))
    (HomD : ObjD → ObjD → GradedRModule (β := β) (R := R))
    (F₀ : ObjC → ObjD)
    (mD : {n : ℕ+} → (obj : Fin ((n : ℕ) + 1) → ObjD) → (deg : Fin (n : ℕ) → β) →
      MultilinearMap R
        (fun i : Fin (n : ℕ) => composableHomType HomD obj deg i)
        (operationTargetType HomD obj deg))
    (f : {n : ℕ+} → (obj : Fin ((n : ℕ) + 1) → ObjC) → (deg : Fin (n : ℕ) → β) →
      MultilinearMap R
        (fun i : Fin (n : ℕ) => composableHomType HomC obj deg i)
        (functorTargetType HomD F₀ obj deg))
    {n : ℕ+}
    (obj : Fin ((n : ℕ) + 1) → ObjC)
    (deg : Fin (n : ℕ) → β)
    (x : ∀ i : Fin (n : ℕ), composableHomType HomC obj deg i)
    (c : Composition (n : ℕ))
    (hm : ∀ (h : 0 < c.length) (o : Fin (c.length + 1) → ObjD) (d : Fin c.length → β),
      mD (n := ⟨c.length, h⟩) o d = 0) :
    indexedSFRightTerm HomC HomD F₀ mD f obj deg x c = 0 := by
  simp only [indexedSFRightTerm, hm, MultilinearMap.zero_apply]
  exact modcat_cast_zero _

set_option maxHeartbeats 800000 in
/-- If the functor component at some block size of the partition vanishes
identically, the partition term vanishes. -/
theorem indexedSFRightTerm_inner_zero
    {R : Type u} [CommRing R]
    {ObjC : Type w} {ObjD : Type w'}
    (HomC : ObjC → ObjC → GradedRModule (β := β) (R := R))
    (HomD : ObjD → ObjD → GradedRModule (β := β) (R := R))
    (F₀ : ObjC → ObjD)
    (mD : {n : ℕ+} → (obj : Fin ((n : ℕ) + 1) → ObjD) → (deg : Fin (n : ℕ) → β) →
      MultilinearMap R
        (fun i : Fin (n : ℕ) => composableHomType HomD obj deg i)
        (operationTargetType HomD obj deg))
    (f : {n : ℕ+} → (obj : Fin ((n : ℕ) + 1) → ObjC) → (deg : Fin (n : ℕ) → β) →
      MultilinearMap R
        (fun i : Fin (n : ℕ) => composableHomType HomC obj deg i)
        (functorTargetType HomD F₀ obj deg))
    {n : ℕ+}
    (obj : Fin ((n : ℕ) + 1) → ObjC)
    (deg : Fin (n : ℕ) → β)
    (x : ∀ i : Fin (n : ℕ), composableHomType HomC obj deg i)
    (c : Composition (n : ℕ))
    (j : Fin c.length)
    (hm : ∀ (h : 0 < c.blocksFun j) (o : Fin (c.blocksFun j + 1) → ObjC)
      (d : Fin (c.blocksFun j) → β), f (n := ⟨c.blocksFun j, h⟩) o d = 0) :
    indexedSFRightTerm HomC HomD F₀ mD f obj deg x c = 0 := by
  apply modcat_cast_zero_iff _ |>.mpr
  convert MultilinearMap.map_coord_zero _ _ _
  exact j
  convert modcat_cast_zero_of_eq _ _ _
  · exact (congrArg (fun g : MultilinearMap R _ _ => g _)
      (hm (c.one_le_blocksFun j) _ _)).trans (MultilinearMap.zero_apply _)
  · simp only [composableHomType, functorTargetType, c.sizeUpTo_succ']
    rfl
  · rfl
  · congr 1
    exact congrArg
      (fun v : Fin ((n : ℕ) + 1) =>
        HomD (F₀ (obj ⟨c.sizeUpTo j.val, by have := c.sizeUpTo_le j.val; omega⟩))
          (F₀ (obj v))
          (functorTargetDeg fun i : Fin (c.blocksFun j) =>
            deg ⟨c.sizeUpTo j.val + i.val,
              by have := c.sizeUpTo_add_blocksFun_le j; have := i.isLt; omega⟩))
      (Fin.ext (c.sizeUpTo_succ' j) :
        (⟨c.sizeUpTo (j.val + 1),
            by have := c.sizeUpTo_le (j.val + 1); omega⟩ : Fin ((n : ℕ) + 1)) =
          ⟨c.sizeUpTo j.val + c.blocksFun j,
            by have := c.sizeUpTo_add_blocksFun_le j; omega⟩)

/-- Fixed-chain variant of `indexedSFLeftTerm_outer_zero`: it suffices that the
outer functor component vanishes on the actual collapsed chain. -/
theorem indexedSFLeftTerm_outer_zero_at
    {R : Type u} [CommRing R]
    {ObjC : Type w} {ObjD : Type w'}
    (HomC : ObjC → ObjC → GradedRModule (β := β) (R := R))
    (HomD : ObjD → ObjD → GradedRModule (β := β) (R := R))
    (F₀ : ObjC → ObjD)
    (mC : {n : ℕ+} → (obj : Fin ((n : ℕ) + 1) → ObjC) → (deg : Fin (n : ℕ) → β) →
      MultilinearMap R
        (fun i : Fin (n : ℕ) => composableHomType HomC obj deg i)
        (operationTargetType HomC obj deg))
    (f : {n : ℕ+} → (obj : Fin ((n : ℕ) + 1) → ObjC) → (deg : Fin (n : ℕ) → β) →
      MultilinearMap R
        (fun i : Fin (n : ℕ) => composableHomType HomC obj deg i)
        (functorTargetType HomD F₀ obj deg))
    {n : ℕ+}
    (obj : Fin ((n : ℕ) + 1) → ObjC)
    (deg : Fin (n : ℕ) → β)
    (x : ∀ i : Fin (n : ℕ), composableHomType HomC obj deg i)
    {r s : ℕ} {hs : 1 ≤ s} {hr : r + s ≤ (n : ℕ)}
    (hm : ∀ (h : 0 < (n : ℕ) + 1 - s),
      f (n := ⟨(n : ℕ) + 1 - s, h⟩) (stasheffObjOut obj r s hr)
        (stasheffDegOut deg r s hr) = 0) :
    indexedSFLeftTerm HomC HomD F₀ mC f obj deg x r s hs hr = 0 := by
  simp only [indexedSFLeftTerm, hm, MultilinearMap.zero_apply]
  exact modcat_cast_zero _

set_option maxHeartbeats 800000 in
/-- Fixed-chain variant of `indexedSFLeftTerm_inner_zero`: it suffices that the
inner source operation vanishes on the actual inserted chain. -/
theorem indexedSFLeftTerm_inner_zero_at
    {R : Type u} [CommRing R]
    {ObjC : Type w} {ObjD : Type w'}
    (HomC : ObjC → ObjC → GradedRModule (β := β) (R := R))
    (HomD : ObjD → ObjD → GradedRModule (β := β) (R := R))
    (F₀ : ObjC → ObjD)
    (mC : {n : ℕ+} → (obj : Fin ((n : ℕ) + 1) → ObjC) → (deg : Fin (n : ℕ) → β) →
      MultilinearMap R
        (fun i : Fin (n : ℕ) => composableHomType HomC obj deg i)
        (operationTargetType HomC obj deg))
    (f : {n : ℕ+} → (obj : Fin ((n : ℕ) + 1) → ObjC) → (deg : Fin (n : ℕ) → β) →
      MultilinearMap R
        (fun i : Fin (n : ℕ) => composableHomType HomC obj deg i)
        (functorTargetType HomD F₀ obj deg))
    {n : ℕ+}
    (obj : Fin ((n : ℕ) + 1) → ObjC)
    (deg : Fin (n : ℕ) → β)
    (x : ∀ i : Fin (n : ℕ), composableHomType HomC obj deg i)
    {r s : ℕ} {hs : 1 ≤ s} {hr : r + s ≤ (n : ℕ)}
    (hm : ∀ (h : 0 < s),
      mC (n := ⟨s, h⟩) (stasheffObjIn obj r s hr) (stasheffDegIn deg r s hr) = 0) :
    indexedSFLeftTerm HomC HomD F₀ mC f obj deg x r s hs hr = 0 := by
  apply modcat_cast_zero_iff _ |>.mpr
  convert MultilinearMap.map_coord_zero _ _ _
  exact ⟨r, Nat.lt_sub_of_add_lt (by omega)⟩
  convert modcat_cast_zero_of_eq _ _ _
  rotate_left
  exact operationTargetType HomC (stasheffObjIn obj r s hr) (stasheffDegIn deg r s hr)
  all_goals norm_num [operationTargetType, composableHomType]
  rotate_left
  exact ↑(HomC (stasheffObjIn obj r s hr 0) (stasheffObjIn obj r s hr (Fin.last s))
    (operationTargetDeg (stasheffDegIn deg r s hr)))
  · rfl
  · unfold stasheffObjOut stasheffObjIn stasheffDegOut operationTargetDeg
    simp +decide [Nat.mod_eq_of_lt]
    rfl
  · exact (hm (by omega)).symm ▸ rfl
  · simp +decide [stasheffObjIn, stasheffObjOut, stasheffDegIn, stasheffDegOut,
      operationTargetDeg]
    congr! 2

set_option maxHeartbeats 800000 in
/-- Fixed-chain variant of `indexedSFRightTerm_inner_zero`: it suffices that
the functor component vanishes on the actual `j`-th block chain. -/
theorem indexedSFRightTerm_inner_zero_at
    {R : Type u} [CommRing R]
    {ObjC : Type w} {ObjD : Type w'}
    (HomC : ObjC → ObjC → GradedRModule (β := β) (R := R))
    (HomD : ObjD → ObjD → GradedRModule (β := β) (R := R))
    (F₀ : ObjC → ObjD)
    (mD : {n : ℕ+} → (obj : Fin ((n : ℕ) + 1) → ObjD) → (deg : Fin (n : ℕ) → β) →
      MultilinearMap R
        (fun i : Fin (n : ℕ) => composableHomType HomD obj deg i)
        (operationTargetType HomD obj deg))
    (f : {n : ℕ+} → (obj : Fin ((n : ℕ) + 1) → ObjC) → (deg : Fin (n : ℕ) → β) →
      MultilinearMap R
        (fun i : Fin (n : ℕ) => composableHomType HomC obj deg i)
        (functorTargetType HomD F₀ obj deg))
    {n : ℕ+}
    (obj : Fin ((n : ℕ) + 1) → ObjC)
    (deg : Fin (n : ℕ) → β)
    (x : ∀ i : Fin (n : ℕ), composableHomType HomC obj deg i)
    (c : Composition (n : ℕ))
    (j : Fin c.length)
    (hm : ∀ (h : 0 < c.blocksFun j),
      f (n := ⟨c.blocksFun j, h⟩)
        (fun i : Fin (c.blocksFun j + 1) => obj ⟨c.sizeUpTo j.val + i.val,
          by have := c.sizeUpTo_add_blocksFun_le j; omega⟩)
        (fun i : Fin (c.blocksFun j) => deg ⟨c.sizeUpTo j.val + i.val,
          by have := c.sizeUpTo_add_blocksFun_le j; omega⟩) = 0) :
    indexedSFRightTerm HomC HomD F₀ mD f obj deg x c = 0 := by
  apply modcat_cast_zero_iff _ |>.mpr
  convert MultilinearMap.map_coord_zero _ _ _
  exact j
  convert modcat_cast_zero_of_eq _ _ _
  · exact (congrArg (fun g : MultilinearMap R _ _ => g _)
      (hm (c.one_le_blocksFun j))).trans (MultilinearMap.zero_apply _)
  · simp only [composableHomType, functorTargetType, c.sizeUpTo_succ']
    rfl
  · rfl
  · congr 1
    exact congrArg
      (fun v : Fin ((n : ℕ) + 1) =>
        HomD (F₀ (obj ⟨c.sizeUpTo j.val, by have := c.sizeUpTo_le j.val; omega⟩))
          (F₀ (obj v))
          (functorTargetDeg fun i : Fin (c.blocksFun j) =>
            deg ⟨c.sizeUpTo j.val + i.val,
              by have := c.sizeUpTo_add_blocksFun_le j; have := i.isLt; omega⟩))
      (Fin.ext (c.sizeUpTo_succ' j) :
        (⟨c.sizeUpTo (j.val + 1),
            by have := c.sizeUpTo_le (j.val + 1); omega⟩ : Fin ((n : ℕ) + 1)) =
          ⟨c.sizeUpTo j.val + c.blocksFun j,
            by have := c.sizeUpTo_add_blocksFun_le j; omega⟩)

end AInfinityTheory

namespace AInfinityCategoryTheory

open AInfinityTheory

universe u v w w'
variable {β : Type v} [Grading β]
variable {R : Type u} [CommRing R]
variable {ObjC : Type w} {ObjD : Type w'}

/-- The data of an A∞-functor between A∞-(pre)categories: an object map
together with a multilinear component for every composable chain, of target
degree `∑ deg + (1 − n)`. -/
structure AInfinityPreFunctor
    (X : AInfinityPreCategory (β := β) R ObjC)
    (Y : AInfinityPreCategory (β := β) R ObjD) where
  obj : ObjC → ObjD
  f :
    {n : ℕ+} →
    (objs : Fin ((n : ℕ) + 1) → ObjC) →
    (deg : Fin (n : ℕ) → β) →
    MultilinearMap R
      (fun i : Fin (n : ℕ) => composableHomType X.Hom objs deg i)
      (functorTargetType Y.Hom obj objs deg)

namespace AInfinityPreFunctor

variable {X : AInfinityPreCategory (β := β) R ObjC}
variable {Y : AInfinityPreCategory (β := β) R ObjD}

/-- The insertion side of `[SFₙ]` for this functor data. -/
def sfLeftSum (F : AInfinityPreFunctor X Y)
    {n : ℕ+}
    (objs : Fin ((n : ℕ) + 1) → ObjC)
    (deg : Fin (n : ℕ) → β)
    (x : ∀ i : Fin (n : ℕ), composableHomType X.Hom objs deg i) :
    Y.Hom (F.obj (objs 0)) (F.obj (objs (Fin.last (n : ℕ)))) (operationTargetDeg deg) :=
  indexedSFLeftSum X.Hom Y.Hom F.obj X.m F.f objs deg x

/-- The partition side of `[SFₙ]` for this functor data. -/
def sfRightSum (F : AInfinityPreFunctor X Y)
    {n : ℕ+}
    (objs : Fin ((n : ℕ) + 1) → ObjC)
    (deg : Fin (n : ℕ) → β)
    (x : ∀ i : Fin (n : ℕ), composableHomType X.Hom objs deg i) :
    Y.Hom (F.obj (objs 0)) (F.obj (objs (Fin.last (n : ℕ)))) (operationTargetDeg deg) :=
  indexedSFRightSum X.Hom Y.Hom F.obj Y.m F.f objs deg x

/-- The `[SFₙ]` axioms as a property of A∞-functor data. -/
def satisfiesSF (F : AInfinityPreFunctor X Y) : Prop :=
  indexedSatisfiesSF X.Hom Y.Hom F.obj X.m Y.m F.f

end AInfinityPreFunctor

/-- An A∞-functor: A∞-functor data satisfying the `[SFₙ]` axioms. -/
structure AInfinityFunctor
    (X : AInfinityPreCategory (β := β) R ObjC)
    (Y : AInfinityPreCategory (β := β) R ObjD)
    extends AInfinityPreFunctor X Y where
  sf : toAInfinityPreFunctor.satisfiesSF

namespace AInfinityFunctor

variable {X : AInfinityPreCategory (β := β) R ObjC}
variable {Y : AInfinityPreCategory (β := β) R ObjD}

lemma sf_eq (F : AInfinityFunctor X Y)
    {n : ℕ+}
    (objs : Fin ((n : ℕ) + 1) → ObjC)
    (deg : Fin (n : ℕ) → β)
    (x : ∀ i : Fin (n : ℕ), composableHomType X.Hom objs deg i) :
    F.toAInfinityPreFunctor.sfLeftSum objs deg x =
      F.toAInfinityPreFunctor.sfRightSum objs deg x :=
  F.sf n objs deg x

end AInfinityFunctor

end AInfinityCategoryTheory
