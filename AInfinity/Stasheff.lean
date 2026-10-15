/-
Copyright (c) 2026 Annie Yao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Annie Yao, Marco David, Zhan Shi
-/
module

public import Mathlib
public import AInfinity.Grading
public import AInfinity.GradedLinearAlgebra
public import AInfinity.GradedLinearQuiver

/-! # The Stasheff identities

Given a graded `R`-linear quiver with higher compositions
`mₙ : Hom(X₀, X₁) ⊗ ⋯ ⊗ Hom(Xₙ₋₁, Xₙ) → Hom(X₀, Xₙ)` of degree `2 - n`, the arity-`n` Stasheff
identity states that
`∑_{r + s + t = n, s ≥ 1} (-1)^(‖a_{r+s+1}‖ + ⋯ + ‖a_n‖) m_{r+1+t}(a_1, …, a_r,
m_s(a_{r+1}, …, a_{r+s}), a_{r+s+1}, …, a_n) = 0`.

## Main definitions

* `AInfinityTheory.AInfinityComposition`: the type of higher compositions `mₙ` on a graded
  linear quiver.
* `AInfinityTheory.indexedStasheffTerm`: the `(r, s, t)` summand of the Stasheff sum.
* `AInfinityTheory.stasheffSign`: the Koszul sign of the `(r, s, t)` summand.
* `AInfinityTheory.indexedStasheffSum`: the signed Stasheff sum in arity `n`.
* `AInfinityTheory.indexedSatisfiesStasheff`: the Stasheff identities in every arity.

## Main results

* `AInfinityTheory.indexedSatisfiesStasheff_of_arity_two`: if `m` vanishes outside arity `2`,
  the Stasheff identities reduce to the arity-`3` one, i.e. associativity of `m₂` up to sign.
-/

@[expose] public section

open CategoryTheory Finset AInfinityTheory

noncomputable section

namespace AInfinityTheory

universe u v w

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

open GradedLinearQuiver

variable {R : Type u} [CommRing R] {Obj : Type w} [GradedLinearQuiver β R Obj]

variable (β R Obj) in
/-- The type of A∞ compositions on a graded linear quiver: for each arity `n ≥ 1` and each
composable string of objects `obj`, a graded multilinear map `mₙ` of degree `2 - n` from the
composable hom spaces to the hom space from `obj 0` to `obj (Fin.last n)`. -/
abbrev AInfinityComposition :=
  {n : ℕ} → [NeZero n] → (obj : Fin (n + 1) → Obj) →
    GradedMultilinearMap R (ComposableHomType R (β := β) obj) (obj 0 →ᵍ[R] obj (Fin.last n))
      (shift (2 - (n : ℤ)))

variable (m : AInfinityComposition β R Obj)
variable (obj : Fin (n + 1) → Obj) (deg : Fin n → β)
variable (x : ∀ i : Fin n, ComposableHomType R obj i (deg i))
variable (r s t : ℕ) (ht : r + s + t = n)

/-- Helper: degree function for the inner portion of the Stasheff composition. -/
def stasheffDegIn : Fin s → β :=
  fun j => deg (((j.natAdd r).castAdd t).cast ht)

/-- Helper: inner degree (the degree of the result of the inner multilinear map). -/
def stasheffInnerDeg : β :=
  operationTargetDeg (stasheffDegIn deg r s t ht)

/-- Helper: the outer degree function. It lists the degrees of the first `r` inputs, then the
degree of the inner output, then the degrees of the last `t` inputs. -/
def stasheffDegOut : Fin (r + 1 + t) → β :=
  Fin.append
    (Fin.snoc (fun j : Fin r => deg (((j.castAdd s).castAdd t).cast ht))
      (stasheffInnerDeg deg r s t ht))
    (fun k : Fin t => deg ((k.natAdd (r + s)).cast ht))

/-- On the first block, the outer degrees are the degrees of the first `r` inputs. -/
@[simp]
lemma stasheffDegOut_left
    (j : Fin r) :
    stasheffDegOut deg r s t ht (j.castSucc.castAdd t) =
      deg (((j.castAdd s).castAdd t).cast ht) := by
  simp [stasheffDegOut]

/-- In the middle slot, the outer degree is the degree of the inner output. -/
@[simp]
lemma stasheffDegOut_middle :
    stasheffDegOut deg r s t ht ((Fin.last r).castAdd t) =
      stasheffInnerDeg deg r s t ht := by
  simp [stasheffDegOut]

/-- On the last block, the outer degrees are the degrees of the last `t` inputs. -/
@[simp]
lemma stasheffDegOut_right
    (k : Fin t) :
    stasheffDegOut deg r s t ht (k.natAdd (r + 1)) =
      deg ((k.natAdd (r + s)).cast ht) := by
  simp [stasheffDegOut]

/-- Helper: the inner object string `obj r, …, obj (r + s)`. -/
def stasheffObjIn : Fin (s + 1) → Obj :=
  fun j => obj ((j.natAdd r).castLE (by omega))

/-- Helper: the outer object string `obj 0, …, obj r, obj (r + s), …, obj n` obtained by
collapsing the inner block. -/
def stasheffObjOut : Fin (r + 1 + t + 1) → Obj :=
  Fin.append (fun i : Fin (r + 1) => obj (i.castLE (by omega)))
      (fun k : Fin (t + 1) => obj ((k.natAdd (r + s)).cast (by omega))) ∘
    Fin.cast (Nat.add_assoc ..)

/-- Up to the inner block, the outer object string agrees with the original one. -/
@[simp]
lemma stasheffObjOut_castLE
    (i : Fin (r + 1)) :
    stasheffObjOut obj r s t ht (i.castLE (by omega)) = obj (i.castLE (by omega)) := by
  simp [stasheffObjOut]

/-- After the inner block, the outer object string agrees with the original one, shifted by
`s - 1`. -/
@[simp]
lemma stasheffObjOut_natAdd
    (k : Fin (t + 1)) :
    stasheffObjOut obj r s t ht (k.natAdd (r + 1)) =
      obj ((k.natAdd (r + s)).cast (by omega)) := by
  simp [stasheffObjOut]

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
    stasheffDegOut_middle, stasheffDegOut_right, Fin.sum_univ_castSucc, stasheffInnerDeg,
    stasheffDegIn, ← Fin.sum_congr' deg ht]
  rw [show (3 - (n : ℤ)) = (2 - s) + (2 - ((r + 1 + t : ℕ) : ℤ)) by omega, map_add]
  abel

/-! From here on, `obj` and `deg` are inferred from the operations `m` and the inputs
`x`; declarations that take neither bind them explicitly. -/

variable {obj deg}

/-- Rewriting the degree function and transporting each input does not change the value of `m`. -/
lemma multilinearFamily_eq_of_deg_eq
    [NeZero n]
    {deg deg' : Fin n → β}
    (hdeg : deg = deg')
    (x : ∀ i : Fin n, ComposableHomType R obj i (deg i))
    {d : β}
    (hd : operationTargetDeg deg = d)
    (hd' : operationTargetDeg deg' = d) :
    m obj deg' d hd' (fun i => homCongr R rfl rfl (congrFun hdeg i) (x i)) =
      m obj deg d hd x := by
  subst hdeg
  rfl

/-- Helper: the input tuple for the inner operation in a Stasheff term. -/
def indexedStasheffXIn :
    ∀ j : Fin s,
      ComposableHomType R (stasheffObjIn obj r s t ht) j (stasheffDegIn deg r s t ht j) :=
  fun j => x (((j.natAdd r).castAdd t).cast ht)

omit [AddCommGroup β] [GradingType β] in
/-- Evaluating the inner input tuple just picks out the corresponding original input. -/
lemma indexedStasheffXIn_apply
    (j : Fin s) :
    indexedStasheffXIn x r s t ht j = x (((j.natAdd r).castAdd t).cast ht) :=
  rfl

/-- Helper: the inner value appearing in a Stasheff term, in any degree `d` equal to the
inner degree. -/
def indexedStasheffInner
    (hs : 1 ≤ s)
    (d : β)
    (hd : stasheffInnerDeg deg r s t ht = d) :
    (stasheffObjIn obj r s t ht 0 →ᵍ[R] stasheffObjIn obj r s t ht (Fin.last s)) d :=
  letI : NeZero s := ⟨by omega⟩
  m (stasheffObjIn obj r s t ht) (stasheffDegIn deg r s t ht) d hd
    (indexedStasheffXIn x r s t ht)

/-- Helper: the middle index in the outer tuple of a Stasheff term. -/
abbrev indexedStasheffMiddleIndex : Fin (r + 1 + t) :=
  (Fin.last r).castAdd t

variable (R obj deg) in
/-- Before the inserted block, the space of an original input is identified with the
corresponding outer input space. -/
def indexedStasheffXOutEquivLeft
    (j : Fin r) :
    ComposableHomType R obj (((j.castAdd s).castAdd t).cast ht)
        (deg (((j.castAdd s).castAdd t).cast ht)) ≃ₗ[R]
      ComposableHomType R (stasheffObjOut obj r s t ht) (j.castSucc.castAdd t)
        (stasheffDegOut deg r s t ht (j.castSucc.castAdd t)) :=
  homCongr R (stasheffObjOut_castLE obj r s t ht j.castSucc).symm
    (stasheffObjOut_castLE obj r s t ht j.succ).symm (stasheffDegOut_left deg r s t ht j).symm

variable (R obj) in
/-- At the inserted block, the space of the inner output is identified with the outer middle
input space, in any degree `d`. -/
def indexedStasheffXOutEquivMid
    (d : β) :
    (stasheffObjIn obj r s t ht 0 →ᵍ[R] stasheffObjIn obj r s t ht (Fin.last s)) d ≃ₗ[R]
      ComposableHomType R (stasheffObjOut obj r s t ht) (indexedStasheffMiddleIndex r t) d :=
  homCongr R (stasheffObjOut_castLE obj r s t ht (Fin.last r)).symm
    (stasheffObjOut_natAdd obj r s t ht 0).symm rfl

variable (R obj deg) in
/-- After the inserted block, the space of an original input is identified with the
corresponding outer input space. -/
def indexedStasheffXOutEquivRight
    (k : Fin t) :
    ComposableHomType R obj ((k.natAdd (r + s)).cast ht) (deg ((k.natAdd (r + s)).cast ht)) ≃ₗ[R]
      ComposableHomType R (stasheffObjOut obj r s t ht) (k.natAdd (r + 1))
        (stasheffDegOut deg r s t ht (k.natAdd (r + 1))) :=
  homCongr R (stasheffObjOut_natAdd obj r s t ht k.castSucc).symm
    (stasheffObjOut_natAdd obj r s t ht k.succ).symm (stasheffDegOut_right deg r s t ht k).symm

/-- Helper: the input tuple for the outer operation in a Stasheff term: the first `r` inputs,
then the inner output, then the last `t` inputs. -/
def indexedStasheffXOut
    (hs : 1 ≤ s) :
    ∀ i : Fin (r + 1 + t),
      ComposableHomType R (stasheffObjOut obj r s t ht) i (stasheffDegOut deg r s t ht i) :=
  Fin.addCases
    (Fin.snoc
      (fun j => indexedStasheffXOutEquivLeft R obj deg r s t ht j
        (x (((j.castAdd s).castAdd t).cast ht)))
      (indexedStasheffXOutEquivMid R obj r s t ht _
        (indexedStasheffInner m x r s t ht hs _ (stasheffDegOut_middle deg r s t ht).symm)))
    (fun k => indexedStasheffXOutEquivRight R obj deg r s t ht k (x ((k.natAdd (r + s)).cast ht)))

/-- Before the inserted block, the outer input tuple agrees with the original inputs. -/
@[simp]
lemma indexedStasheffXOut_left
    (hs : 1 ≤ s)
    (j : Fin r) :
    indexedStasheffXOut m x r s t ht hs (j.castSucc.castAdd t) =
      indexedStasheffXOutEquivLeft R obj deg r s t ht j
        (x (((j.castAdd s).castAdd t).cast ht)) := by
  simp [indexedStasheffXOut]

/-- After the inserted block, the outer input tuple agrees with the original inputs. -/
@[simp]
lemma indexedStasheffXOut_right
    (hs : 1 ≤ s)
    (k : Fin t) :
    indexedStasheffXOut m x r s t ht hs (k.natAdd (r + 1)) =
      indexedStasheffXOutEquivRight R obj deg r s t ht k (x ((k.natAdd (r + s)).cast ht)) := by
  simp [indexedStasheffXOut]

/-- The middle outer input is the transported inner output. -/
lemma indexedStasheffXOut_middle
    (hs : 1 ≤ s) :
    indexedStasheffXOut m x r s t ht hs (indexedStasheffMiddleIndex r t) =
      indexedStasheffXOutEquivMid R obj r s t ht _
        (indexedStasheffInner m x r s t ht hs _ (stasheffDegOut_middle deg r s t ht).symm) := by
  simp [indexedStasheffXOut]

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
    (stasheffObjOut obj r s t ht 0 →ᵍ[R]
      stasheffObjOut obj r s t ht (Fin.last (r + 1 + t))) d :=
  letI : NeZero (r + 1 + t) := ⟨by omega⟩
  m (stasheffObjOut obj r s t ht) (stasheffDegOut deg r s t ht) d hd
    (indexedStasheffXOut m x r s t ht hs)

variable (R obj) in
/-- Helper: the identification of the outer target space with the final Stasheff target space,
in any degree `d`. -/
def indexedStasheffTargetEquiv
    (d : β) :
    (stasheffObjOut obj r s t ht 0 →ᵍ[R]
      stasheffObjOut obj r s t ht (Fin.last (r + 1 + t))) d
      ≃ₗ[R] (obj 0 →ᵍ[R] obj (Fin.last n)) d :=
  homCongr R (by simpa using stasheffObjOut_castLE obj r s t ht 0)
    ((stasheffObjOut_natAdd obj r s t ht (Fin.last t)).trans
      (congrArg obj (Fin.ext (by simp only [Fin.val_cast, Fin.val_natAdd, Fin.val_last]; omega))))
    rfl

/-- A generic Stasheff term builder for object-indexed A∞ operations, in any degree `d` equal
to the Stasheff target degree. -/
def indexedStasheffTerm
    (hs : 1 ≤ s)
    (d : β)
    (hd : stasheffTargetDeg deg = d) :
    (obj 0 →ᵍ[R] obj (Fin.last n)) d :=
  indexedStasheffTargetEquiv R obj r s t ht d
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
  (indexedStasheffTargetEquiv R obj r s t ht d).map_eq_zero_iff

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
  ∏ k : Fin t, sign (deg ((k.natAdd (r + s)).cast ht) - shift 1)

/-- The full Stasheff sum in arity `n`, with Koszul signs, in any degree `d` equal to the
Stasheff target degree. The term indexed by `(r, s)` has `t = n - r - s` trailing inputs. -/
def indexedStasheffSum
    (d : β)
    (hd : stasheffTargetDeg deg = d) :
    (obj 0 →ᵍ[R] obj (Fin.last n)) d :=
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
    (x : ∀ i : Fin n, ComposableHomType R obj i (deg i)) (d : β)
    (hd : stasheffTargetDeg deg = d),
    indexedStasheffSum m x d hd = 0

/-- If `m` vanishes outside arity `2`, a Stasheff term vanishes unless both its inner and its
outer operation are binary. -/
lemma indexedStasheffTerm_eq_zero_of_arity_ne_two
    (hm : ∀ (k : ℕ) [NeZero k], k ≠ 2 → ∀ obj : Fin (k + 1) → Obj, m obj = 0)
    {n : ℕ} {obj : Fin (n + 1) → Obj} {deg : Fin n → β}
    (x : ∀ i : Fin n, ComposableHomType R obj i (deg i)) (r s t : ℕ) (ht : r + s + t = n)
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
      (x : ∀ i : Fin 3, ComposableHomType R obj i (deg i)) (d : β)
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
