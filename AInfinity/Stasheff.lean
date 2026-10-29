/-
Copyright (c) 2026 Annie Yao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Annie Yao, Marco David, Zhan Shi
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import AInfinity.Grading
public import AInfinity.GradedLinearAlgebra
public import AInfinity.GradedLinearQuiver

/-! # The Stasheff identities

Given a graded `R`-linear quiver with higher compositions
`mₙ : Hom(X₀, X₁) ⊗ ⋯ ⊗ Hom(Xₙ₋₁, Xₙ) → Hom(X₀, Xₙ)` of degree `2 - n`, the arity-`n` Stasheff
identity states that
`∑_{r + s + t = n, s ≥ 1} (-1)^(‖a_{r+s+1}‖ + ⋯ + ‖aₙ‖) m_{r+1+t}(a₁, …, aᵣ,
mₛ(a_{r+1}, …, a_{r+s}), a_{r+s+1}, …, aₙ) = 0`.

## Main definitions

* `AInfinityTheory.AInfinityComposition`: the type of higher compositions `mₙ` on a graded
  linear quiver.
* `AInfinityTheory.StasheffIndex`: the index triples `(r, s, t)` with `r + s + t = n` and
  `1 ≤ s`.
* `AInfinityTheory.stasheffSign`: the Koszul sign of the `(r, s, t)` summand.
* `AInfinityTheory.signedStasheffSum`: the sum of a family of `(r, s, t)` terms with these signs.
* `AInfinityTheory.indexedStasheffTerm`: the `(r, s, t)` summand of the Stasheff sum.
* `AInfinityTheory.indexedStasheffSum`: the signed Stasheff sum in arity `n`.
* `AInfinityTheory.IndexedSatisfiesStasheff`: the Stasheff identities in every arity.

## Main results

* `AInfinityTheory.indexedSatisfiesStasheff_of_arity_two`: if `m` vanishes outside arity `2`,
  the Stasheff identities reduce to the arity-`3` one, i.e. associativity of `m₂` up to sign.
-/

@[expose] public section

namespace AInfinityTheory

universe u v w

variable {β : Type v} [AddCommGroup β] [Grading β]
variable {n : ℕ}

/-- The degree of `mₙ(a₁, …, aₙ)` for inputs `aᵢ` of degrees `deg i`, where `mₙ` itself has
degree `2 - n`. -/
abbrev operationTargetDeg
    (deg : Fin n → β) : β :=
  (∑ i, deg i) + shift (2 - (n : ℤ))

/-- Target degree of the arity-`n` Stasheff identity on inputs of degrees `deg`. -/
abbrev stasheffTargetDeg
    (deg : Fin n → β) : β :=
  (∑ i, deg i) + shift (3 - (n : ℤ))

/-- The arity-`n` Stasheff identity has degree one more than the `n`-ary operation `mₙ`. -/
lemma stasheffTargetDeg_eq_operationTargetDeg_add_shift_one
    (deg : Fin n → β) :
    stasheffTargetDeg deg = operationTargetDeg deg + shift 1 := by
  rw [stasheffTargetDeg, operationTargetDeg, add_assoc, ← map_add]
  congr 2
  lia

/-- An index triple `(r, s, t)` of the arity-`n` Stasheff identity: `r + s + t = n` and
`1 ≤ s`. -/
@[ext]
structure StasheffIndex (n : ℕ) where
  /-- The number of inputs before the inner operation. -/
  r : ℕ
  /-- The arity of the inner operation. -/
  s : ℕ
  /-- The number of inputs after the inner operation. -/
  t : ℕ
  /-- The three blocks of inputs make up all `n` inputs. -/
  sum_eq : r + s + t = n
  /-- The inner operation has at least one input. -/
  one_le_s : 1 ≤ s
  deriving DecidableEq

/-- An index triple `(r, s, t)` is determined by the endpoints `r < r + s` of the nonempty
interval of inputs fed to the inner operation. -/
def StasheffIndex.equivLt : StasheffIndex n ≃ {x : Fin (n + 1) × Fin (n + 1) // x.1 < x.2} where
  toFun p := ⟨(⟨p.r, by have := p.sum_eq; omega⟩, ⟨p.r + p.s, by have := p.sum_eq; omega⟩),
    Fin.mk_lt_mk.2 (Nat.lt_add_of_pos_right p.one_le_s)⟩
  invFun x := ⟨x.1.1, x.1.2 - x.1.1, n - x.1.2, by have := x.1.2.isLt; omega,
    Nat.sub_pos_of_lt x.2⟩
  left_inv p := by have := p.sum_eq; ext <;> dsimp only <;> omega
  right_inv x := Subtype.ext <| Prod.ext rfl <| Fin.ext <| Nat.add_sub_cancel' x.2.le

/-- The index triples of the arity-`n` Stasheff identity form a finite type, through their
identification with pairs of endpoints. -/
instance : Fintype (StasheffIndex n) :=
  .ofEquiv _ StasheffIndex.equivLt.symm

/-- The inner operation of a Stasheff term has positive arity. -/
instance (p : StasheffIndex n) : NeZero p.s :=
  ⟨by have := p.one_le_s; omega⟩

/-- The outer operation of a Stasheff term has positive arity. -/
instance (p : StasheffIndex n) : NeZero (p.r + 1 + p.t) :=
  ⟨by omega⟩

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
variable (p : StasheffIndex n)

/-- Helper: degree function for the inner portion of the Stasheff composition. -/
def stasheffDegIn : Fin p.s → β :=
  fun j => deg (((j.natAdd p.r).castAdd p.t).cast p.sum_eq)

/-- Helper: inner degree (the degree of the result of the inner multilinear map). -/
def stasheffInnerDeg : β :=
  operationTargetDeg (stasheffDegIn deg p)

/-- Helper: the outer degree function. It lists the degrees of the first `r` inputs, then the
degree of the inner output, then the degrees of the last `t` inputs. -/
def stasheffDegOut : Fin (p.r + 1 + p.t) → β :=
  Fin.append
    (Fin.snoc (fun j : Fin p.r => deg (((j.castAdd p.s).castAdd p.t).cast p.sum_eq))
      (stasheffInnerDeg deg p))
    (fun k : Fin p.t => deg ((k.natAdd (p.r + p.s)).cast p.sum_eq))

/-- On the first block, the outer degrees are the degrees of the first `r` inputs. -/
@[simp]
lemma stasheffDegOut_left
    (j : Fin p.r) :
    stasheffDegOut deg p (j.castSucc.castAdd p.t) =
      deg (((j.castAdd p.s).castAdd p.t).cast p.sum_eq) := by
  simp [stasheffDegOut]

/-- In the middle slot, the outer degree is the degree of the inner output. -/
@[simp]
lemma stasheffDegOut_middle :
    stasheffDegOut deg p ((Fin.last p.r).castAdd p.t) = stasheffInnerDeg deg p := by
  simp [stasheffDegOut]

/-- On the last block, the outer degrees are the degrees of the last `t` inputs. -/
@[simp]
lemma stasheffDegOut_right
    (k : Fin p.t) :
    stasheffDegOut deg p (k.natAdd (p.r + 1)) = deg ((k.natAdd (p.r + p.s)).cast p.sum_eq) := by
  simp [stasheffDegOut]

/-- Helper: the inner object string `obj r, …, obj (r + s)`. -/
def stasheffObjIn : Fin (p.s + 1) → Obj :=
  fun j => obj ((j.natAdd p.r).castLE (by have := p.sum_eq; omega))

/-- Helper: the outer object string `obj 0, …, obj r, obj (r + s), …, obj n` obtained by
collapsing the inner block. -/
def stasheffObjOut : Fin (p.r + 1 + p.t + 1) → Obj :=
  Fin.append (m := p.r + 1) (fun j : Fin (p.r + 1) => obj (j.castLE (by have := p.sum_eq; omega)))
      (fun k : Fin (p.t + 1) =>
        obj ((k.natAdd (p.r + p.s)).cast (by have := p.sum_eq; omega)))

/-- Up to the inner block, the outer object string agrees with the original one. -/
@[simp]
lemma stasheffObjOut_left
    (j : Fin (p.r + 1)) :
    stasheffObjOut obj p (j.castLE (by omega)) =
      obj (j.castLE (by have := p.sum_eq; omega)) := by
  simp [stasheffObjOut]

/-- After the inner block, the outer object string agrees with the original one, shifted by
`s - 1`. -/
@[simp]
lemma stasheffObjOut_right
    (k : Fin (p.t + 1)) :
    stasheffObjOut obj p (k.natAdd (p.r + 1)) =
      obj ((k.natAdd (p.r + p.s)).cast (by have := p.sum_eq; omega)) := by
  simp [stasheffObjOut]

/-- The outer object string starts at `obj 0`. -/
@[simp]
lemma stasheffObjOut_zero : stasheffObjOut obj p 0 = obj 0 :=
  stasheffObjOut_left obj p 0

/-- The outer object string ends at `obj (Fin.last n)`. -/
@[simp]
lemma stasheffObjOut_last :
    stasheffObjOut obj p (Fin.last (p.r + 1 + p.t)) = obj (Fin.last n) :=
  (stasheffObjOut_right obj p (Fin.last p.t)).trans (congrArg obj (Fin.ext p.sum_eq))

/-- The outer operation has the Stasheff target degree. -/
lemma stasheffDegOut_sum :
    operationTargetDeg (stasheffDegOut deg p) = stasheffTargetDeg deg := by
  have := p.sum_eq
  simp only [operationTargetDeg, stasheffTargetDeg, Fin.sum_univ_add, stasheffDegOut_left,
    stasheffDegOut_middle, stasheffDegOut_right, Fin.sum_univ_castSucc, stasheffInnerDeg,
    stasheffDegIn, ← Fin.sum_congr' deg p.sum_eq]
  rw [show (3 - (n : ℤ)) = (2 - p.s) + (2 - ((p.r + 1 + p.t : ℕ) : ℤ)) by omega, map_add]
  abel

/-! From here on, `obj` and `deg` are inferred from the operations `m` and the inputs
`x`; declarations that take neither bind them explicitly. -/

variable {obj deg}

/-- Rewriting the degree function and transporting each input does not change the value of `m`. -/
lemma aInfinityComposition_homCongr_deg
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
    ∀ j : Fin p.s, ComposableHomType R (stasheffObjIn obj p) j (stasheffDegIn deg p j) :=
  fun j => x (((j.natAdd p.r).castAdd p.t).cast p.sum_eq)

omit [AddCommGroup β] [Grading β] in
/-- Evaluating the inner input tuple just picks out the corresponding original input. -/
@[simp]
lemma indexedStasheffXIn_apply
    (j : Fin p.s) :
    indexedStasheffXIn x p j = x (((j.natAdd p.r).castAdd p.t).cast p.sum_eq) :=
  rfl

/-- Helper: the inner value appearing in a Stasheff term, in any degree `d` equal to the
inner degree. -/
def indexedStasheffInner
    (d : β)
    (hd : stasheffInnerDeg deg p = d) :
    (stasheffObjIn obj p 0 →ᵍ[R] stasheffObjIn obj p (Fin.last p.s)) d :=
  m (stasheffObjIn obj p) (stasheffDegIn deg p) d hd (indexedStasheffXIn x p)

/-- Helper: the middle index in the outer tuple of a Stasheff term. -/
abbrev indexedStasheffMiddleIndex : Fin (p.r + 1 + p.t) :=
  (Fin.last p.r).castAdd p.t

variable (R obj deg) in
/-- Before the inserted block, the space of an original input is identified with the
corresponding outer input space. -/
def indexedStasheffXOutEquivLeft
    (j : Fin p.r) :
    ComposableHomType R obj (((j.castAdd p.s).castAdd p.t).cast p.sum_eq)
        (deg (((j.castAdd p.s).castAdd p.t).cast p.sum_eq)) ≃ₗ[R]
      ComposableHomType R (stasheffObjOut obj p) (j.castSucc.castAdd p.t)
        (stasheffDegOut deg p (j.castSucc.castAdd p.t)) :=
  homCongr R (stasheffObjOut_left obj p j.castSucc).symm
    (stasheffObjOut_left obj p j.succ).symm (stasheffDegOut_left deg p j).symm

variable (R obj) in
/-- At the inserted block, the space of the inner output is identified with the outer middle
input space, in any degree `d`. -/
def indexedStasheffXOutEquivMid
    (d : β) :
    (stasheffObjIn obj p 0 →ᵍ[R] stasheffObjIn obj p (Fin.last p.s)) d ≃ₗ[R]
      ComposableHomType R (stasheffObjOut obj p) (indexedStasheffMiddleIndex p) d :=
  homCongr R (stasheffObjOut_left obj p (Fin.last p.r)).symm
    (stasheffObjOut_right obj p 0).symm rfl

variable (R obj deg) in
/-- After the inserted block, the space of an original input is identified with the
corresponding outer input space. -/
def indexedStasheffXOutEquivRight
    (k : Fin p.t) :
    ComposableHomType R obj ((k.natAdd (p.r + p.s)).cast p.sum_eq)
        (deg ((k.natAdd (p.r + p.s)).cast p.sum_eq)) ≃ₗ[R]
      ComposableHomType R (stasheffObjOut obj p) (k.natAdd (p.r + 1))
        (stasheffDegOut deg p (k.natAdd (p.r + 1))) :=
  homCongr R (stasheffObjOut_right obj p k.castSucc).symm
    (stasheffObjOut_right obj p k.succ).symm (stasheffDegOut_right deg p k).symm

/-- Helper: the input tuple for the outer operation in a Stasheff term: the first `r` inputs,
then the inner output, then the last `t` inputs. -/
def indexedStasheffXOut :
    ∀ a : Fin (p.r + 1 + p.t),
      ComposableHomType R (stasheffObjOut obj p) a (stasheffDegOut deg p a) :=
  Fin.addCases
    (Fin.snoc
      (fun j => indexedStasheffXOutEquivLeft R obj deg p j
        (x (((j.castAdd p.s).castAdd p.t).cast p.sum_eq)))
      (indexedStasheffXOutEquivMid R obj p _
        (indexedStasheffInner m x p _ (stasheffDegOut_middle deg p).symm)))
    (fun k => indexedStasheffXOutEquivRight R obj deg p k
      (x ((k.natAdd (p.r + p.s)).cast p.sum_eq)))

/-- Before the inserted block, the outer input tuple agrees with the original inputs. -/
@[simp]
lemma indexedStasheffXOut_left
    (j : Fin p.r) :
    indexedStasheffXOut m x p (j.castSucc.castAdd p.t) =
      indexedStasheffXOutEquivLeft R obj deg p j
        (x (((j.castAdd p.s).castAdd p.t).cast p.sum_eq)) := by
  simp [indexedStasheffXOut]

/-- After the inserted block, the outer input tuple agrees with the original inputs. -/
@[simp]
lemma indexedStasheffXOut_right
    (k : Fin p.t) :
    indexedStasheffXOut m x p (k.natAdd (p.r + 1)) =
      indexedStasheffXOutEquivRight R obj deg p k (x ((k.natAdd (p.r + p.s)).cast p.sum_eq)) := by
  simp [indexedStasheffXOut]

/-- The middle outer input is the transported inner output. -/
@[simp]
lemma indexedStasheffXOut_middle :
    indexedStasheffXOut m x p (indexedStasheffMiddleIndex p) =
      indexedStasheffXOutEquivMid R obj p _
        (indexedStasheffInner m x p _ (stasheffDegOut_middle deg p).symm) := by
  simp [indexedStasheffXOut]

/-- The middle outer input vanishes whenever the inner output vanishes. -/
lemma indexedStasheffXOut_middle_eq_zero_of_inner_eq_zero
    (hinner : ∀ d hd, indexedStasheffInner m x p d hd = 0) :
    indexedStasheffXOut m x p (indexedStasheffMiddleIndex p) = 0 := by
  rw [indexedStasheffXOut_middle, hinner, map_zero]

/-- Helper: the outer value appearing in a Stasheff term, in any degree `d` equal to the
degree of the outer operation. -/
def indexedStasheffOuter
    (d : β)
    (hd : operationTargetDeg (stasheffDegOut deg p) = d) :
    (stasheffObjOut obj p 0 →ᵍ[R] stasheffObjOut obj p (Fin.last (p.r + 1 + p.t))) d :=
  m (stasheffObjOut obj p) (stasheffDegOut deg p) d hd (indexedStasheffXOut m x p)

variable (R obj) in
/-- Helper: the identification of the outer target space with the final Stasheff target space,
in any degree `d`. -/
def indexedStasheffTargetEquiv
    (d : β) :
    (stasheffObjOut obj p 0 →ᵍ[R] stasheffObjOut obj p (Fin.last (p.r + 1 + p.t))) d
      ≃ₗ[R] (obj 0 →ᵍ[R] obj (Fin.last n)) d :=
  homCongr R (stasheffObjOut_zero obj p) (stasheffObjOut_last obj p) rfl

/-- A generic Stasheff term builder for object-indexed A∞ operations, in any degree `d` equal
to the Stasheff target degree. -/
def indexedStasheffTerm
    (d : β)
    (hd : stasheffTargetDeg deg = d) :
    (obj 0 →ᵍ[R] obj (Fin.last n)) d :=
  indexedStasheffTargetEquiv R obj p d
    (indexedStasheffOuter m x p d ((stasheffDegOut_sum deg p).trans hd))

/-- The inner value vanishes if the inner multilinear map itself vanishes. -/
lemma indexedStasheffInner_eq_zero_of_map_eq_zero
    (hm : ∀ d hd, m (stasheffObjIn obj p) (stasheffDegIn deg p) d hd = 0)
    (d : β)
    (hd : stasheffInnerDeg deg p = d) :
    indexedStasheffInner m x p d hd = 0 := by
  simp [indexedStasheffInner, hm]

/-- The outer value vanishes if the outer multilinear map itself vanishes. -/
lemma indexedStasheffOuter_eq_zero_of_map_eq_zero
    (hm : ∀ d hd, m (stasheffObjOut obj p) (stasheffDegOut deg p) d hd = 0)
    (d : β)
    (hd : operationTargetDeg (stasheffDegOut deg p) = d) :
    indexedStasheffOuter m x p d hd = 0 := by
  simp [indexedStasheffOuter, hm]

/-- The outer value vanishes whenever the inserted inner output vanishes. -/
lemma indexedStasheffOuter_eq_zero_of_inner_eq_zero
    (hinner : ∀ d hd, indexedStasheffInner m x p d hd = 0)
    (d : β)
    (hd : operationTargetDeg (stasheffDegOut deg p) = d) :
    indexedStasheffOuter m x p d hd = 0 :=
  MultilinearMap.map_coord_zero (m (stasheffObjOut obj p) (stasheffDegOut deg p) d hd)
    (indexedStasheffMiddleIndex p)
    (indexedStasheffXOut_middle_eq_zero_of_inner_eq_zero m x p hinner)

/-- The final transported Stasheff term vanishes exactly when the outer value vanishes. -/
lemma indexedStasheffTerm_eq_zero_iff_outer_eq_zero
    (d : β)
    (hd : stasheffTargetDeg deg = d) :
    indexedStasheffTerm m x p d hd = 0 ↔
      indexedStasheffOuter m x p d ((stasheffDegOut_sum deg p).trans hd) = 0 :=
  (indexedStasheffTargetEquiv R obj p d).map_eq_zero_iff

/-- The final Stasheff term vanishes if the outer multilinear map vanishes. -/
lemma indexedStasheffTerm_eq_zero_of_outer_map_eq_zero
    (hm : ∀ d hd, m (stasheffObjOut obj p) (stasheffDegOut deg p) d hd = 0)
    (d : β)
    (hd : stasheffTargetDeg deg = d) :
    indexedStasheffTerm m x p d hd = 0 :=
  (indexedStasheffTerm_eq_zero_iff_outer_eq_zero m x p d hd).2
    (indexedStasheffOuter_eq_zero_of_map_eq_zero m x p hm _ _)

/-- The final Stasheff term vanishes if the inner multilinear map vanishes. -/
lemma indexedStasheffTerm_eq_zero_of_inner_map_eq_zero
    (hm : ∀ d hd, m (stasheffObjIn obj p) (stasheffDegIn deg p) d hd = 0)
    (d : β)
    (hd : stasheffTargetDeg deg = d) :
    indexedStasheffTerm m x p d hd = 0 :=
  (indexedStasheffTerm_eq_zero_iff_outer_eq_zero m x p d hd).2
    (indexedStasheffOuter_eq_zero_of_inner_eq_zero m x p
      (indexedStasheffInner_eq_zero_of_map_eq_zero m x p hm) _ _)

variable (deg) in
/-- The Koszul sign `(-1)^(‖a_{r+s+1}‖ + ⋯ + ‖aₙ‖)` of the Stasheff term indexed by
`p = (r, s, t)`, where `‖a‖ = |a| - 1` is the reduced degree of an input after the inner
operation. -/
def stasheffSign : ℤˣ :=
  ∏ k : Fin p.t, sign (deg ((k.natAdd (p.r + p.s)).cast p.sum_eq) - shift 1)

variable (deg) in
/-- The signed sum `∑_{r + s + t = n, s ≥ 1} (-1)^(‖a_{r+s+1}‖ + ⋯ + ‖aₙ‖) f (r, s, t)` over
the index triples `StasheffIndex n` of the arity-`n` Stasheff identity. Both the Stasheff
identities and the `A∞`-functor equations are sums of this form. -/
def signedStasheffSum {M : Type*} [AddCommGroup M] (f : StasheffIndex n → M) : M :=
  ∑ q, stasheffSign deg q • f q

/-- A signed Stasheff sum of vanishing terms vanishes. -/
lemma signedStasheffSum_eq_zero {M : Type*} [AddCommGroup M] {f : StasheffIndex n → M}
    (h : ∀ q, f q = 0) :
    signedStasheffSum deg f = 0 :=
  Finset.sum_eq_zero fun q _ => smul_eq_zero_of_right _ (h q)

/-- Additive maps commute with signed Stasheff sums. -/
lemma map_signedStasheffSum {M N G : Type*} [AddCommGroup M] [AddCommGroup N] [FunLike G M N]
    [AddMonoidHomClass G M N] (g : G) (f : StasheffIndex n → M) :
    g (signedStasheffSum deg f) = signedStasheffSum deg fun q => g (f q) := by
  simp only [signedStasheffSum, map_sum, Units.smul_def, map_zsmul]

/-- The full Stasheff sum in arity `n`, with Koszul signs, in any degree `d` equal to the
Stasheff target degree. -/
def indexedStasheffSum
    (d : β)
    (hd : stasheffTargetDeg deg = d) :
    (obj 0 →ᵍ[R] obj (Fin.last n)) d :=
  signedStasheffSum deg fun q => indexedStasheffTerm m x q d hd

/-- The Stasheff identities for object-indexed A∞ operations. -/
def IndexedSatisfiesStasheff : Prop :=
  ∀ (n : ℕ) [NeZero n] (obj : Fin (n + 1) → Obj) (deg : Fin n → β)
    (x : ∀ i : Fin n, ComposableHomType R obj i (deg i)) (d : β)
    (hd : stasheffTargetDeg deg = d),
    indexedStasheffSum m x d hd = 0

/-- If `m` vanishes outside arity `2`, a Stasheff term vanishes unless both its inner and its
outer operation are binary. -/
lemma indexedStasheffTerm_eq_zero_of_arity_ne_two
    (hm : ∀ (k : ℕ) [NeZero k], k ≠ 2 → ∀ obj : Fin (k + 1) → Obj, m obj = 0)
    {n : ℕ} {obj : Fin (n + 1) → Obj} {deg : Fin n → β}
    (x : ∀ i : Fin n, ComposableHomType R obj i (deg i)) (p : StasheffIndex n)
    (h2 : p.s ≠ 2 ∨ p.r + 1 + p.t ≠ 2) (d : β) (hd : stasheffTargetDeg deg = d) :
    indexedStasheffTerm m x p d hd = 0 := by
  rcases h2 with h2 | h2
  · exact indexedStasheffTerm_eq_zero_of_inner_map_eq_zero m x p
      (fun d hd => by simp only [hm p.s h2]; rfl) d hd
  · exact indexedStasheffTerm_eq_zero_of_outer_map_eq_zero m x p
      (fun d hd => by simp only [hm _ h2]; rfl) d hd

/-- If `m` vanishes outside arity `2`, the Stasheff identities reduce to the one in arity `3`,
`±m₂(m₂(a₁, a₂), a₃) + m₂(a₁, m₂(a₂, a₃)) = 0`. -/
theorem indexedSatisfiesStasheff_of_arity_two
    (hm : ∀ (k : ℕ) [NeZero k], k ≠ 2 → ∀ obj : Fin (k + 1) → Obj, m obj = 0)
    (h3 : ∀ (obj : Fin (3 + 1) → Obj) (deg : Fin 3 → β)
      (x : ∀ i : Fin 3, ComposableHomType R obj i (deg i)) (d : β)
      (hd : stasheffTargetDeg deg = d),
      stasheffSign deg ⟨0, 2, 1, rfl, by norm_num⟩ •
          indexedStasheffTerm m x ⟨0, 2, 1, rfl, by norm_num⟩ d hd +
        indexedStasheffTerm m x ⟨1, 2, 0, rfl, by norm_num⟩ d hd = 0) :
    IndexedSatisfiesStasheff m := by
  intro n _ obj deg x d hd
  have hterm := indexedStasheffTerm_eq_zero_of_arity_ne_two m hm x
  rcases eq_or_ne n 3 with rfl | hn
  · rw [indexedStasheffSum, signedStasheffSum]
    refine (Fintype.sum_eq_add ⟨0, 2, 1, rfl, by norm_num⟩ ⟨1, 2, 0, rfl, by norm_num⟩
      (by decide) fun ⟨r, s, t, ht, hs⟩ ⟨h1, h2⟩ => smul_eq_zero_of_right _ ?_).trans ?_
    · exact (congrArg (_ + ·) ((congrArg (· • _) (Fin.prod_univ_zero _)).trans
        (one_smul _ _))).trans (h3 obj deg x d hd)
    · simp only [ne_eq, StasheffIndex.mk.injEq] at h1 h2
      exact hterm ⟨r, s, t, ht, hs⟩ (by dsimp only; omega) d hd
  · exact signedStasheffSum_eq_zero fun p => hterm p (by have := p.sum_eq; omega) d hd

end AInfinityTheory
