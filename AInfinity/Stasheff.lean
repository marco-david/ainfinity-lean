module

public import Mathlib
public import AInfinity.Grading
public import AInfinity.GradedLinearAlgebra

@[expose] public section

open CategoryTheory Finset AInfinityTheory

noncomputable section

namespace AInfinityTheory

universe u v w w'
variable {β : Type v} [AddCommGroup β] [GradingType β]
variable {n : ℕ}

/-- Target degree of the `n`-ary operation `m`. -/
abbrev operationTargetDeg
    (deg : Fin n → β) : β :=
  (∑ i, deg i) + shift (2 - (n : ℤ))

/-- Target degree of the arity-`n` Stasheff relation. -/
abbrev stasheffTargetDeg
    (deg : Fin n → β) : β :=
  (∑ i, deg i) + shift (3 - (n : ℤ))

/-- Valid index pairs for an arity-`n` Stasheff summand. -/
abbrev ValidStasheffIndices (n r s : ℕ) : Prop :=
  1 ≤ s ∧ r + s ≤ n

variable {R : Type u} [CommRing R] {Obj : Type w}
variable (Hom : Obj → Obj → β → Type w') [∀ X Y i, AddCommGroup (Hom X Y i)]
  [∀ X Y i, Module R (Hom X Y i)]

/-- The hom space containing the `i`-th morphism of a composable string of objects, in
degree `b`. -/
abbrev ComposableHomType
    (obj : Fin (n + 1) → Obj)
    (i : Fin n)
    (b : β) : Type w' :=
  Hom
    (obj ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
    (obj ⟨i.val + 1, by omega⟩)
    b

variable (R) in
/-- The type of A∞ compositions on a graded quiver `Hom`: for each arity `n ≥ 1` and each
composable string of objects `obj`, a graded multilinear map `mₙ` of degree `2 - n` from the
composable hom spaces to the hom space from `obj 0` to `obj (Fin.last n)`. -/
abbrev AInfinityComposition :=
  {n : ℕ} → [NeZero n] → (obj : Fin (n + 1) → Obj) →
    GradedMultilinearMap R (ComposableHomType Hom obj) (Hom (obj 0) (obj (Fin.last n)))
      (shift (2 - (n : ℤ)))

variable (m : AInfinityComposition R Hom)
variable (obj : Fin (n + 1) → Obj) (deg : Fin n → β)
variable (x : ∀ i : Fin n, ComposableHomType Hom obj i (deg i))
variable (r s t : ℕ) (ht : r + s + t = n)

variable (R) in
/-- Transport between graded hom spaces along equalities of the source, target and degree.
This is the three-index form of `LinearEquiv.cast`. -/
def gradedHomCongr
    {X X' Y Y' : Obj}
    {i i' : β}
    (hX : X = X')
    (hY : Y = Y')
    (hi : i = i') :
    Hom X Y i ≃ₗ[R] Hom X' Y' i' := by
  subst hX hY hi
  exact LinearEquiv.refl R _

variable (R) in
omit [AddCommGroup β] [GradingType β] in
/-- Transport along reflexivity is the identity. -/
@[simp]
lemma gradedHomCongr_refl
    (X Y : Obj)
    (i : β) :
    gradedHomCongr R Hom (rfl : X = X) (rfl : Y = Y) (rfl : i = i) = LinearEquiv.refl R _ :=
  rfl

variable (R) in
omit [AddCommGroup β] [GradingType β] in
/-- The inverse of a transport is the transport along the reversed equalities. -/
@[simp]
lemma gradedHomCongr_symm
    {X X' Y Y' : Obj}
    {i i' : β}
    (hX : X = X')
    (hY : Y = Y')
    (hi : i = i') :
    (gradedHomCongr R Hom hX hY hi).symm = gradedHomCongr R Hom hX.symm hY.symm hi.symm := by
  subst hX hY hi
  rfl

variable (R) in
omit [AddCommGroup β] [GradingType β] in
/-- Transporting twice is transporting along the composite equalities. -/
@[simp]
lemma gradedHomCongr_trans
    {X X' X'' Y Y' Y'' : Obj}
    {i i' i'' : β}
    (hX : X = X')
    (hY : Y = Y')
    (hi : i = i')
    (hX' : X' = X'')
    (hY' : Y' = Y'')
    (hi' : i' = i'') :
    (gradedHomCongr R Hom hX hY hi).trans (gradedHomCongr R Hom hX' hY' hi') =
      gradedHomCongr R Hom (hX.trans hX') (hY.trans hY') (hi.trans hi') := by
  subst hX hY hi hX' hY' hi'
  rfl

/-- Helper: degree function for the inner portion of the Stasheff composition. -/
def stasheffDegIn : Fin s → β :=
  fun j => deg (Fin.cast ht (Fin.castAdd t (Fin.natAdd r j)))

/-- Helper: inner degree (the degree of the result of the inner multilinear map). -/
def stasheffInnerDeg : β :=
  operationTargetDeg (stasheffDegIn deg r s t ht)

/-- Helper: the outer degree function. It lists the degrees of the first `r` inputs, then the
degree of the inner output, then the degrees of the last `t` inputs. -/
def stasheffDegOut : Fin (r + 1 + t) → β :=
  fun i =>
    if h : i.val < r then
      deg ⟨i.val, by omega⟩
    else if h' : i.val = r then
      stasheffInnerDeg deg r s t ht
    else
      deg ⟨i.val + s - 1, by omega⟩

/-- On the first block, the outer degrees are the degrees of the first `r` inputs. -/
@[simp]
lemma stasheffDegOut_left
    (j : Fin r) :
    stasheffDegOut deg r s t ht (Fin.castAdd t (Fin.castAdd 1 j)) =
      deg (Fin.cast ht (Fin.castAdd t (Fin.castAdd s j))) := by
  simp [stasheffDegOut]
  rfl

/-- In the middle slot, the outer degree is the degree of the inner output. -/
@[simp]
lemma stasheffDegOut_middle
    (k : Fin 1) :
    stasheffDegOut deg r s t ht (Fin.castAdd t (Fin.natAdd r k)) =
      stasheffInnerDeg deg r s t ht := by
  simp [stasheffDegOut]

/-- On the last block, the outer degrees are the degrees of the last `t` inputs. -/
@[simp]
lemma stasheffDegOut_right
    (k : Fin t) :
    stasheffDegOut deg r s t ht (Fin.natAdd (r + 1) k) =
      deg (Fin.cast ht (Fin.natAdd (r + s) k)) := by
  simp only [stasheffDegOut, Fin.val_natAdd, show ¬ r + 1 + k < r by omega,
    show r + 1 + k ≠ r by omega, dite_false]
  congr 1
  ext
  simp
  omega

/-- Helper: the inner object string. -/
def stasheffObjIn : Fin (s + 1) → Obj :=
  fun j => obj ⟨r + j.val, by omega⟩

/-- Helper: the outer object string obtained by collapsing the inner block. -/
def stasheffObjOut : Fin (r + 1 + t + 1) → Obj :=
  fun i =>
    if h : i.val ≤ r then
      obj ⟨i.val, by omega⟩
    else
      obj ⟨i.val + s - 1, by omega⟩

/-- The finite ranges used in the Stasheff sum produce valid index pairs. -/
lemma validStasheffIndices_of_mem_ranges
    {r s : ℕ}
    (hr : r ∈ Finset.range (n + 1))
    (hs : s ∈ Finset.Ico 1 (n - r + 1)) :
    ValidStasheffIndices n r s := by
  rcases Finset.mem_range.mp hr with hr
  rcases Finset.mem_Ico.mp hs with ⟨hs₁, hs₂⟩
  refine ⟨hs₁, ?_⟩
  omega

/-- The outer operation has the Stasheff target degree. -/
lemma stasheffDegOut_sum :
    operationTargetDeg (stasheffDegOut deg r s t ht) = stasheffTargetDeg deg := by
  simp only [operationTargetDeg, stasheffTargetDeg, Fin.sum_univ_add, stasheffDegOut_left,
    stasheffDegOut_middle, stasheffDegOut_right, Fin.sum_univ_one, stasheffInnerDeg,
    stasheffDegIn, ← Fin.sum_congr' deg ht]
  rw [show (3 - (n : ℤ)) = (2 - s) + (2 - ((r + 1 + t : ℕ) : ℤ)) by omega, map_add]
  abel

/-! From here on, `Hom`, `obj` and `deg` are inferred from the operations `m` and the inputs
`x`; declarations that take neither bind them explicitly. -/

variable {Hom obj deg}

/-- Rewriting the degree function and transporting each input does not change the value of `m`. -/
lemma multilinearFamily_eq_of_deg_eq
    [NeZero n]
    {deg deg' : Fin n → β}
    (hdeg : deg = deg')
    (x : ∀ i : Fin n, ComposableHomType Hom obj i (deg i))
    {d : β}
    (hd : operationTargetDeg deg = d)
    (hd' : operationTargetDeg deg' = d) :
    m obj deg' d hd' (fun i => gradedHomCongr R Hom rfl rfl (congrFun hdeg i) (x i)) =
      m obj deg d hd x := by
  subst hdeg
  rfl

/-- Helper: the input tuple for the inner operation in a Stasheff term. -/
def indexedStasheffXIn :
    ∀ j : Fin s,
      ComposableHomType Hom (stasheffObjIn obj r s t ht) j (stasheffDegIn deg r s t ht j) :=
  fun j => x (Fin.cast ht (Fin.castAdd t (Fin.natAdd r j)))

omit [AddCommGroup β] [GradingType β] [∀ X Y i, AddCommGroup (Hom X Y i)] in
/-- Evaluating the inner input tuple just picks out the corresponding original input. -/
lemma indexedStasheffXIn_apply
    (j : Fin s) :
    indexedStasheffXIn x r s t ht j = x (Fin.cast ht (Fin.castAdd t (Fin.natAdd r j))) :=
  rfl

/-- Helper: the inner value appearing in a Stasheff term, in any degree `d` equal to the
inner degree. -/
def indexedStasheffInner
    (hs : 1 ≤ s)
    (d : β)
    (hd : stasheffInnerDeg deg r s t ht = d) :
    Hom (stasheffObjIn obj r s t ht 0) (stasheffObjIn obj r s t ht (Fin.last s)) d :=
  letI : NeZero s := ⟨by omega⟩
  m (stasheffObjIn obj r s t ht) (stasheffDegIn deg r s t ht) d hd
    (indexedStasheffXIn x r s t ht)

/-- Helper: the middle index in the outer tuple of a Stasheff term. -/
abbrev indexedStasheffMiddleIndex : Fin (r + 1 + t) :=
  Fin.castAdd t (Fin.natAdd r 0)

variable (R Hom obj deg) in
/-- Before the inserted block, the space of an original input is identified with the
corresponding outer input space. -/
def indexedStasheffXOutEquivLeft
    (j : Fin r) :
    ComposableHomType Hom obj (Fin.cast ht (Fin.castAdd t (Fin.castAdd s j)))
        (deg (Fin.cast ht (Fin.castAdd t (Fin.castAdd s j)))) ≃ₗ[R]
      ComposableHomType Hom (stasheffObjOut obj r s t ht) (Fin.castAdd t (Fin.castAdd 1 j))
        (stasheffDegOut deg r s t ht (Fin.castAdd t (Fin.castAdd 1 j))) :=
  gradedHomCongr R Hom (by simp [stasheffObjOut, j.isLt.le])
    (by simp [stasheffObjOut, Nat.succ_le_of_lt j.isLt]) (by simp)

variable (R Hom obj) in
/-- At the inserted block, the space of the inner output is identified with the outer middle
input space, in any degree `d`. -/
def indexedStasheffXOutEquivMid
    (k : Fin 1)
    (d : β) :
    Hom (stasheffObjIn obj r s t ht 0) (stasheffObjIn obj r s t ht (Fin.last s)) d ≃ₗ[R]
      ComposableHomType Hom (stasheffObjOut obj r s t ht) (Fin.castAdd t (Fin.natAdd r k)) d :=
  gradedHomCongr R Hom (by simp [stasheffObjIn, stasheffObjOut])
    (by simp [stasheffObjIn, stasheffObjOut]) rfl

variable (R Hom obj deg) in
/-- After the inserted block, the space of an original input is identified with the
corresponding outer input space. -/
def indexedStasheffXOutEquivRight
    (k : Fin t) :
    ComposableHomType Hom obj (Fin.cast ht (Fin.natAdd (r + s) k))
        (deg (Fin.cast ht (Fin.natAdd (r + s) k))) ≃ₗ[R]
      ComposableHomType Hom (stasheffObjOut obj r s t ht) (Fin.natAdd (r + 1) k)
        (stasheffDegOut deg r s t ht (Fin.natAdd (r + 1) k)) :=
  gradedHomCongr R Hom
    (by
      simp only [stasheffObjOut, Fin.val_natAdd, Fin.val_cast, show ¬ r + 1 + k ≤ r by omega,
        dite_false]
      congr 1
      ext
      simp only
      omega)
    (by
      simp only [stasheffObjOut, Fin.val_natAdd, Fin.val_cast,
        show ¬ r + 1 + k + 1 ≤ r by omega, dite_false]
      congr 1
      ext
      simp only
      omega)
    (by simp)

/-- Helper: the input tuple for the outer operation in a Stasheff term: the first `r` inputs,
then the inner output, then the last `t` inputs. -/
def indexedStasheffXOut
    (hs : 1 ≤ s) :
    ∀ i : Fin (r + 1 + t),
      ComposableHomType Hom (stasheffObjOut obj r s t ht) i (stasheffDegOut deg r s t ht i) :=
  Fin.addCases
    (motive := fun i =>
      ComposableHomType Hom (stasheffObjOut obj r s t ht) i (stasheffDegOut deg r s t ht i))
    (Fin.addCases
      (motive := fun i =>
        ComposableHomType Hom (stasheffObjOut obj r s t ht) (Fin.castAdd t i)
          (stasheffDegOut deg r s t ht (Fin.castAdd t i)))
      (fun j => indexedStasheffXOutEquivLeft R Hom obj deg r s t ht j
        (x (Fin.cast ht (Fin.castAdd t (Fin.castAdd s j)))))
      (fun k => indexedStasheffXOutEquivMid R Hom obj r s t ht k _
        (indexedStasheffInner m x r s t ht hs _ (by simp))))
    (fun k => indexedStasheffXOutEquivRight R Hom obj deg r s t ht k
      (x (Fin.cast ht (Fin.natAdd (r + s) k))))

/-- Before the inserted block, the outer input tuple agrees with the original inputs. -/
@[simp]
lemma indexedStasheffXOut_left
    (hs : 1 ≤ s)
    (j : Fin r) :
    indexedStasheffXOut m x r s t ht hs (Fin.castAdd t (Fin.castAdd 1 j)) =
      indexedStasheffXOutEquivLeft R Hom obj deg r s t ht j
        (x (Fin.cast ht (Fin.castAdd t (Fin.castAdd s j)))) := by
  simp [indexedStasheffXOut]

/-- After the inserted block, the outer input tuple agrees with the original inputs. -/
@[simp]
lemma indexedStasheffXOut_right
    (hs : 1 ≤ s)
    (k : Fin t) :
    indexedStasheffXOut m x r s t ht hs (Fin.natAdd (r + 1) k) =
      indexedStasheffXOutEquivRight R Hom obj deg r s t ht k
        (x (Fin.cast ht (Fin.natAdd (r + s) k))) := by
  simp [indexedStasheffXOut]

/-- The middle outer input is the transported inner output. -/
lemma indexedStasheffXOut_middle
    (hs : 1 ≤ s) :
    indexedStasheffXOut m x r s t ht hs (indexedStasheffMiddleIndex r t) =
      indexedStasheffXOutEquivMid R Hom obj r s t ht 0 _
        (indexedStasheffInner m x r s t ht hs _
          (by simp [indexedStasheffMiddleIndex])) := by
  simp [indexedStasheffXOut, indexedStasheffMiddleIndex]

/-- The middle outer input vanishes whenever the inner output vanishes. -/
lemma indexedStasheffXOut_middle_eq_zero_of_inner_eq_zero
    (hs : 1 ≤ s)
    (hinner : ∀ d hd, indexedStasheffInner m x r s t ht hs d hd = 0) :
    indexedStasheffXOut m x r s t ht hs (indexedStasheffMiddleIndex r t) = 0 := by
  rw [indexedStasheffXOut_middle, hinner, map_zero]

/-- Helper: the outer value appearing in a Stasheff term, in any degree `d` equal to the
degree of the outer operation. -/
def indexedStasheffOuter
    (hs : 1 ≤ s)
    (d : β)
    (hd : operationTargetDeg (stasheffDegOut deg r s t ht) = d) :
    Hom (stasheffObjOut obj r s t ht 0) (stasheffObjOut obj r s t ht (Fin.last (r + 1 + t))) d :=
  letI : NeZero (r + 1 + t) := ⟨by omega⟩
  m (stasheffObjOut obj r s t ht) (stasheffDegOut deg r s t ht) d hd
    (indexedStasheffXOut m x r s t ht hs)

variable (R Hom obj) in
/-- Helper: the identification of the outer target space with the final Stasheff target space,
in any degree `d`. -/
def indexedStasheffTargetEquiv
    (d : β) :
    Hom (stasheffObjOut obj r s t ht 0) (stasheffObjOut obj r s t ht (Fin.last (r + 1 + t))) d
      ≃ₗ[R] Hom (obj 0) (obj (Fin.last n)) d :=
  gradedHomCongr R Hom (by simp [stasheffObjOut])
    (by
      simp only [stasheffObjOut, Fin.val_last, show ¬ r + 1 + t ≤ r by omega, dite_false]
      congr 1
      ext
      simp
      omega)
    rfl

/-- A generic Stasheff term builder for object-indexed A∞ operations, in any degree `d` equal
to the Stasheff target degree. -/
def indexedStasheffTerm
    (hs : 1 ≤ s)
    (d : β)
    (hd : stasheffTargetDeg deg = d) :
    Hom (obj 0) (obj (Fin.last n)) d :=
  indexedStasheffTargetEquiv R Hom obj r s t ht d
    (indexedStasheffOuter m x r s t ht hs d ((stasheffDegOut_sum deg r s t ht).trans hd))

/-- The inner value vanishes if the inner multilinear map itself vanishes. -/
lemma indexedStasheffInner_eq_zero_of_map_eq_zero
    (hs : 1 ≤ s)
    (hm : ∀ d hd,
      @m s ⟨by omega⟩ (stasheffObjIn obj r s t ht) (stasheffDegIn deg r s t ht) d hd = 0)
    (d : β)
    (hd : stasheffInnerDeg deg r s t ht = d) :
    indexedStasheffInner m x r s t ht hs d hd = 0 := by
  simp [indexedStasheffInner, hm]

/-- The outer value vanishes if the outer multilinear map itself vanishes. -/
lemma indexedStasheffOuter_eq_zero_of_map_eq_zero
    (hs : 1 ≤ s)
    (hm : ∀ d hd,
      @m (r + 1 + t) ⟨by omega⟩ (stasheffObjOut obj r s t ht) (stasheffDegOut deg r s t ht)
        d hd = 0)
    (d : β)
    (hd : operationTargetDeg (stasheffDegOut deg r s t ht) = d) :
    indexedStasheffOuter m x r s t ht hs d hd = 0 := by
  simp [indexedStasheffOuter, hm]

/-- The outer value vanishes whenever the inserted inner output vanishes. -/
lemma indexedStasheffOuter_eq_zero_of_inner_eq_zero
    (hs : 1 ≤ s)
    (hinner : ∀ d hd, indexedStasheffInner m x r s t ht hs d hd = 0)
    (d : β)
    (hd : operationTargetDeg (stasheffDegOut deg r s t ht) = d) :
    indexedStasheffOuter m x r s t ht hs d hd = 0 := by
  dsimp [indexedStasheffOuter]
  letI : NeZero (r + 1 + t) := ⟨by omega⟩
  exact MultilinearMap.map_coord_zero
    (m (stasheffObjOut obj r s t ht) (stasheffDegOut deg r s t ht) d hd)
    (indexedStasheffMiddleIndex r t)
    (indexedStasheffXOut_middle_eq_zero_of_inner_eq_zero m x r s t ht hs hinner)

/-- The final transported Stasheff term vanishes exactly when the outer value vanishes. -/
lemma indexedStasheffTerm_eq_zero_iff_outer_eq_zero
    (hs : 1 ≤ s)
    (d : β)
    (hd : stasheffTargetDeg deg = d) :
    indexedStasheffTerm m x r s t ht hs d hd = 0 ↔
      indexedStasheffOuter m x r s t ht hs d
        ((stasheffDegOut_sum deg r s t ht).trans hd) = 0 :=
  (indexedStasheffTargetEquiv R Hom obj r s t ht d).map_eq_zero_iff

/-- The final Stasheff term vanishes if the outer multilinear map vanishes. -/
lemma indexedStasheffTerm_eq_zero_of_outer_map_eq_zero
    (hs : 1 ≤ s)
    (hm : ∀ d hd,
      @m (r + 1 + t) ⟨by omega⟩ (stasheffObjOut obj r s t ht) (stasheffDegOut deg r s t ht)
        d hd = 0)
    (d : β)
    (hd : stasheffTargetDeg deg = d) :
    indexedStasheffTerm m x r s t ht hs d hd = 0 :=
  (indexedStasheffTerm_eq_zero_iff_outer_eq_zero m x r s t ht hs d hd).2
    (indexedStasheffOuter_eq_zero_of_map_eq_zero m x r s t ht hs hm _ _)

/-- The final Stasheff term vanishes if the inner multilinear map vanishes. -/
lemma indexedStasheffTerm_eq_zero_of_inner_map_eq_zero
    (hs : 1 ≤ s)
    (hm : ∀ d hd,
      @m s ⟨by omega⟩ (stasheffObjIn obj r s t ht) (stasheffDegIn deg r s t ht) d hd = 0)
    (d : β)
    (hd : stasheffTargetDeg deg = d) :
    indexedStasheffTerm m x r s t ht hs d hd = 0 :=
  (indexedStasheffTerm_eq_zero_iff_outer_eq_zero m x r s t ht hs d hd).2
    (indexedStasheffOuter_eq_zero_of_inner_eq_zero m x r s t ht hs
      (indexedStasheffInner_eq_zero_of_map_eq_zero m x r s t ht hs hm) _ _)

variable (deg) in
/-- The Koszul sign `(-1)^(‖a_{r+s+1}‖ + ⋯ + ‖a_n‖)` of the `(r, s, t)` Stasheff term, where
`‖a‖ = |a| - 1` is the reduced degree of an input after the inner operation. -/
def stasheffSign : ℤˣ :=
  ∏ k : Fin t, sign (deg (Fin.cast ht (Fin.natAdd (r + s) k)) - shift 1)

/-- The full Stasheff sum in arity `n`, with Koszul signs, in any degree `d` equal to the
Stasheff target degree. The term indexed by `(r, s)` has `t = n - r - s` trailing inputs. -/
def indexedStasheffSum
    (d : β)
    (hd : stasheffTargetDeg deg = d) :
    Hom (obj 0) (obj (Fin.last n)) d :=
  ∑ r : Finset.range (n + 1),
    ∑ s : Finset.Ico 1 (n - r.1 + 1),
      have h : ValidStasheffIndices n r.1 s.1 :=
        validStasheffIndices_of_mem_ranges (n := n) r.2 s.2
      have ht : r.1 + s.1 + (n - r.1 - s.1) = n := by
        rw [Nat.sub_sub]
        exact Nat.add_sub_of_le h.2
      (stasheffSign deg r.1 s.1 (n - r.1 - s.1) ht) •
        (indexedStasheffTerm m x r.1 s.1 (n - r.1 - s.1) ht h.1 d hd)

/-- The Stasheff identities for object-indexed A∞ operations. -/
def indexedSatisfiesStasheff : Prop :=
  ∀ (n : ℕ) [NeZero n] (obj : Fin (n + 1) → Obj) (deg : Fin n → β)
    (x : ∀ i : Fin n, ComposableHomType Hom obj i (deg i)) (d : β)
    (hd : stasheffTargetDeg deg = d),
    indexedStasheffSum m x d hd = 0

/-- If `m` vanishes outside arity `2`, a Stasheff term vanishes unless both its inner and its
outer operation are binary. -/
lemma indexedStasheffTerm_eq_zero_of_arity_ne_two
    (hm : ∀ (k : ℕ) [NeZero k], k ≠ 2 → ∀ obj : Fin (k + 1) → Obj, m obj = 0)
    {n : ℕ} {obj : Fin (n + 1) → Obj} {deg : Fin n → β}
    (x : ∀ i : Fin n, ComposableHomType Hom obj i (deg i)) (r s t : ℕ) (ht : r + s + t = n)
    (hs : 1 ≤ s) (h2 : s ≠ 2 ∨ r + 1 + t ≠ 2) (d : β) (hd : stasheffTargetDeg deg = d) :
    indexedStasheffTerm m x r s t ht hs d hd = 0 := by
  rcases h2 with h2 | h2
  · have : NeZero s := ⟨by omega⟩
    exact indexedStasheffTerm_eq_zero_of_inner_map_eq_zero m x r s t ht hs
      (fun d hd => by simp only [hm s h2]; rfl) d hd
  · have : NeZero (r + 1 + t) := ⟨by omega⟩
    exact indexedStasheffTerm_eq_zero_of_outer_map_eq_zero m x r s t ht hs
      (fun d hd => by simp only [hm _ h2]; rfl) d hd

/-- If `m` vanishes outside arity `2`, the Stasheff identities reduce to the one in arity `3`,
`±m₂(m₂(a₁, a₂), a₃) + m₂(a₁, m₂(a₂, a₃)) = 0`. -/
theorem indexedSatisfiesStasheff_of_arity_two
    (hm : ∀ (k : ℕ) [NeZero k], k ≠ 2 → ∀ obj : Fin (k + 1) → Obj, m obj = 0)
    (h3 : ∀ (obj : Fin (3 + 1) → Obj) (deg : Fin 3 → β)
      (x : ∀ i : Fin 3, ComposableHomType Hom obj i (deg i)) (d : β)
      (hd : stasheffTargetDeg deg = d),
      stasheffSign deg 0 2 1 rfl • indexedStasheffTerm m x 0 2 1 rfl (by norm_num) d hd +
        indexedStasheffTerm m x 1 2 0 rfl (by norm_num) d hd = 0) :
    indexedSatisfiesStasheff m := by
  intro n _ obj deg x d hd
  have hterm := indexedStasheffTerm_eq_zero_of_arity_ne_two m hm x
  rcases eq_or_ne n 3 with rfl | hn
  · refine (Fintype.sum_eq_add ⟨0, by simp⟩ ⟨1, by simp⟩ (by simp) fun r ⟨hr0, hr1⟩ =>
      Finset.sum_eq_zero fun s _ => smul_eq_zero_of_right _ ?_).trans ?_
    · rw [Fintype.sum_eq_single ⟨2, by simp⟩, Fintype.sum_eq_single ⟨2, by simp⟩]
      · exact (congrArg (_ + ·) ((congrArg (· • _) (Fin.prod_univ_zero _)).trans
          (one_smul _ _))).trans (h3 obj deg x d hd)
      all_goals
        exact fun s hs => smul_eq_zero_of_right _
          (hterm _ _ _ _ _ (Or.inl fun h => hs (Subtype.ext h)) d hd)
    · have h := validStasheffIndices_of_mem_ranges r.2 s.2
      have : r.1 ≠ 0 := fun h => hr0 (Subtype.ext h)
      have : r.1 ≠ 1 := fun h => hr1 (Subtype.ext h)
      exact hterm _ _ _ _ _ (by omega) d hd
  · refine Finset.sum_eq_zero fun r _ => Finset.sum_eq_zero fun s _ => ?_
    have h := validStasheffIndices_of_mem_ranges r.2 s.2
    exact smul_eq_zero_of_right _ (hterm _ _ _ _ _ (by omega) d hd)

end AInfinityTheory
