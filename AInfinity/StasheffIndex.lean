/-
Copyright (c) 2026 Annie Yao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Annie Yao, Marco David, Zhan Shi
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Module
public import AInfinity.Grading

/-! # Index triples of the Stasheff identities

The arity-n Stasheff identity is a signed sum over the triples (r, s, t) with
r + s + t = n and 1 ≤ s: the (r, s, t) summand applies an inner operation mₛ to the
s inputs after the first r, and an outer operation of arity r + 1 + t to the result together
with the remaining inputs. This file handles the bookkeeping attached to such a triple that does
not involve any hom spaces: the positions of the inputs and of the objects of the inner and outer
operations, their degrees, and the Koszul sign of the summand.

## Main definitions

* `AInfinityTheory.operationTargetDeg`, `AInfinityTheory.stasheffTargetDeg`: the degrees of
  mₙ(a₁, …, aₙ) and of the arity-n Stasheff identity.
* `AInfinityTheory.StasheffIndex`: the index triples (r, s, t) with r + s + t = n and
  1 ≤ s.
* `AInfinityTheory.StasheffIndex.leftInput`, `AInfinityTheory.StasheffIndex.innerInput`,
  `AInfinityTheory.StasheffIndex.rightInput`: the positions of the first r inputs, of the s inputs
  of the inner operation and of the last t inputs among the n inputs.
* `AInfinityTheory.StasheffIndex.innerObj`, `AInfinityTheory.StasheffIndex.outerObj`: the
  positions of the objects of the inner and of the outer operation among the n + 1 objects.
* `AInfinityTheory.StasheffIndex.middleIndex`: the position of the inner output among the inputs
  of the outer operation.
* `AInfinityTheory.stasheffObjIn`, `AInfinityTheory.stasheffObjOut`: the object strings of the
  inner and of the outer operation of the (r, s, t) summand.
* `AInfinityTheory.stasheffDegIn`, `AInfinityTheory.stasheffDegOut`: the input degrees of the
  inner and of the outer operation of the (r, s, t) summand.
* `AInfinityTheory.stasheffSign`: the Koszul sign of the (r, s, t) summand.
* `AInfinityTheory.signedStasheffSum`: the sum of a family of (r, s, t) terms with these signs.
  Both the Stasheff identities and the A∞-functor equations are sums of this form.

## Main results

* `AInfinityTheory.StasheffIndex.sum_leftInput_add_sum_innerInput_add_sum_rightInput`: the first r
  inputs, the s inputs of the inner operation and the last t inputs make up all n inputs.
* `AInfinityTheory.stasheffDegOut_sum`: the outer operation of the (r, s, t) summand has the
  degree of the arity-n Stasheff identity.
-/

@[expose] public section

namespace AInfinityTheory

universe v w

variable {n : ℕ}

section Degrees

variable {β : Type v} [AddCommGroup β] [Grading β] (deg : Fin n → β)

/-- The degree of mₙ(a₁, …, aₙ) for inputs aᵢ of degrees `deg i`, where mₙ itself
has degree 2 - n. -/
abbrev operationTargetDeg : β :=
  (∑ i, deg i) + (2 - n : ℤ) • degOne

/-- The degree of the arity-n Stasheff identity on inputs of degrees `deg`. -/
abbrev stasheffTargetDeg : β :=
  (∑ i, deg i) + (3 - n : ℤ) • degOne

lemma stasheffTargetDeg_eq_operationTargetDeg_add_degOne :
    stasheffTargetDeg deg = operationTargetDeg deg + degOne := by
  module

end Degrees

/-- An index triple (r, s, t) of the arity-n Stasheff identity: r + s + t = n and
1 ≤ s. -/
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

namespace StasheffIndex

/-- An index triple (r, s, t) is determined by the endpoints r < r + s of the nonempty
interval of inputs fed to the inner operation. -/
def equivLt : StasheffIndex n ≃ {x : Fin (n + 1) × Fin (n + 1) // x.1 < x.2} where
  toFun p := ⟨(⟨p.r, by have := p.sum_eq; omega⟩, ⟨p.r + p.s, by have := p.sum_eq; omega⟩),
    Fin.mk_lt_mk.2 (Nat.lt_add_of_pos_right p.one_le_s)⟩
  invFun x := ⟨x.1.1, x.1.2 - x.1.1, n - x.1.2, by have := x.1.2.isLt; omega,
    Nat.sub_pos_of_lt x.2⟩
  left_inv p := by have := p.sum_eq; ext <;> dsimp only <;> omega
  right_inv x := Subtype.ext <| Prod.ext rfl <| Fin.ext <| Nat.add_sub_cancel' x.2.le

/-- The index triples of the arity-n Stasheff identity form a finite type, through their
identification with pairs of endpoints. -/
instance : Fintype (StasheffIndex n) :=
  .ofEquiv _ equivLt.symm

lemma univ_one : (Finset.univ : Finset (StasheffIndex 1)) = {⟨0, 1, 0, rfl, le_rfl⟩} := by
  decide

lemma univ_two : (Finset.univ : Finset (StasheffIndex 2)) =
    {⟨0, 1, 1, rfl, le_rfl⟩, ⟨1, 1, 0, rfl, le_rfl⟩, ⟨0, 2, 0, rfl, one_le_two⟩} := by
  decide

lemma univ_three : (Finset.univ : Finset (StasheffIndex 3)) =
    {⟨0, 1, 2, rfl, le_rfl⟩, ⟨1, 1, 1, rfl, le_rfl⟩, ⟨2, 1, 0, rfl, le_rfl⟩,
      ⟨0, 2, 1, rfl, one_le_two⟩, ⟨1, 2, 0, rfl, one_le_two⟩, ⟨0, 3, 0, rfl, by decide⟩} := by
  decide

variable (p : StasheffIndex n)

/-- The inner operation of a Stasheff term has positive arity. -/
instance : NeZero p.s :=
  ⟨by have := p.one_le_s; omega⟩

/-- The outer operation of a Stasheff term has positive arity. -/
instance : NeZero (p.r + 1 + p.t) :=
  ⟨by omega⟩

/-! ### Positions of the inputs and objects of the inner and outer operations

The (r, s, t) summand cuts the n inputs into the first r inputs, the s inputs of the inner
operation and the last t inputs. It cuts the n + 1 objects into the objects r, …, r + s of the
inner operation and the objects 0, …, r and r + s, …, n of the outer operation. The maps below
record these positions. They are plain functions; an order-embedding layer in the style of
`Composition.embedding` and `Composition.boundary` can be added on top when it is needed. -/

/-- The position of the `j`-th of the first r inputs among the n inputs: `j` itself. -/
def leftInput (j : Fin p.r) : Fin n :=
  j.castLE ((Nat.le_add_right p.r p.s).trans (Nat.le.intro p.sum_eq))

/-- The position r + j of the `j`-th input of the inner operation among the n inputs. -/
def innerInput (j : Fin p.s) : Fin n :=
  (j.natAdd p.r).castLE (Nat.le.intro p.sum_eq)

/-- The position r + s + k of the `k`-th of the last t inputs among the n inputs. -/
def rightInput (k : Fin p.t) : Fin n :=
  (k.natAdd (p.r + p.s)).castLE p.sum_eq.le

/-- The position r + j of the `j`-th object of the inner operation among the n + 1 objects. -/
def innerObj (j : Fin (p.s + 1)) : Fin (n + 1) :=
  (j.natAdd p.r).castLE (Nat.succ_le_succ (Nat.le.intro p.sum_eq))

/-- The position of the `i`-th object of the outer operation among the n + 1 objects: the
outer objects are the objects 0, …, r and r + s, …, n, so the objects strictly between
positions r and r + s are skipped. -/
def outerObj (i : Fin (p.r + 1 + p.t + 1)) : Fin (n + 1) :=
  ⟨if (i : ℕ) ≤ p.r then (i : ℕ) else i + p.s - 1, by
    have := p.sum_eq; have := p.one_le_s; have := i.isLt; split_ifs <;> omega⟩

/-- The position r of the inner output among the inputs of the outer operation, of arity
r + 1 + t. -/
abbrev middleIndex : Fin (p.r + 1 + p.t) :=
  (Fin.last p.r).castAdd p.t

@[simp]
lemma val_leftInput (j : Fin p.r) : (p.leftInput j : ℕ) = j :=
  rfl

@[simp]
lemma val_innerInput (j : Fin p.s) : (p.innerInput j : ℕ) = p.r + j :=
  rfl

@[simp]
lemma val_rightInput (k : Fin p.t) : (p.rightInput k : ℕ) = p.r + p.s + k :=
  rfl

@[simp]
lemma val_innerObj (j : Fin (p.s + 1)) : (p.innerObj j : ℕ) = p.r + j :=
  rfl

lemma val_outerObj (i : Fin (p.r + 1 + p.t + 1)) :
    (p.outerObj i : ℕ) = if (i : ℕ) ≤ p.r then (i : ℕ) else i + p.s - 1 :=
  rfl

/-- Up to position r, the outer object string follows the original one. -/
@[simp]
lemma val_outerObj_of_le {i : Fin (p.r + 1 + p.t + 1)} (h : (i : ℕ) ≤ p.r) :
    (p.outerObj i : ℕ) = i :=
  ite_eq_left h

/-- After position r, the outer object string skips the s - 1 objects strictly inside the
inner block. -/
@[simp]
lemma val_outerObj_of_lt {i : Fin (p.r + 1 + p.t + 1)} (h : p.r < i) :
    (p.outerObj i : ℕ) = i + p.s - 1 :=
  ite_eq_right (not_le.2 h)

/-- The source of the `j`-th input of the inner operation is the `j`-th inner object. -/
@[simp]
lemma innerObj_castSucc (j : Fin p.s) : p.innerObj j.castSucc = (p.innerInput j).castSucc :=
  rfl

/-- The target of the `j`-th input of the inner operation is the `(j + 1)`-st inner object. -/
@[simp]
lemma innerObj_succ (j : Fin p.s) : p.innerObj j.succ = (p.innerInput j).succ :=
  rfl

/-- The outer object string starts at the object 0. -/
@[simp]
lemma outerObj_zero : p.outerObj 0 = 0 :=
  Fin.ext (p.val_outerObj_of_le (Nat.zero_le _))

/-- The outer object string ends at the object n. -/
@[simp]
lemma outerObj_last : p.outerObj (Fin.last _) = Fin.last n := by
  have := p.sum_eq
  have := p.one_le_s
  ext
  simp only [val_outerObj, Fin.val_last]
  split_ifs <;> omega

/-- Before the inner output, the source of an outer input is the source of the original
input. -/
@[simp]
lemma outerObj_left_castSucc (j : Fin p.r) :
    p.outerObj (j.castSucc.castAdd p.t).castSucc = (p.leftInput j).castSucc :=
  Fin.ext (p.val_outerObj_of_le j.isLt.le)

/-- Before the inner output, the target of an outer input is the target of the original
input. -/
@[simp]
lemma outerObj_left_succ (j : Fin p.r) :
    p.outerObj (j.castSucc.castAdd p.t).succ = (p.leftInput j).succ :=
  Fin.ext (p.val_outerObj_of_le j.isLt)

/-- The source of the inner output, as an outer input, is the first inner object. -/
@[simp]
lemma outerObj_middle_castSucc : p.outerObj p.middleIndex.castSucc = p.innerObj 0 :=
  Fin.ext (p.val_outerObj_of_le le_rfl)

/-- The target of the inner output, as an outer input, is the last inner object. -/
@[simp]
lemma outerObj_middle_succ :
    p.outerObj p.middleIndex.succ = p.innerObj (Fin.last p.s) := by
  have := p.one_le_s
  ext
  simp only [val_outerObj, Fin.val_succ, Fin.val_castAdd, Fin.val_last, val_innerObj]
  split_ifs <;> omega

/-- After the inner output, the source of an outer input is the source of the original
input. -/
@[simp]
lemma outerObj_right_castSucc (k : Fin p.t) :
    p.outerObj (k.natAdd (p.r + 1)).castSucc = (p.rightInput k).castSucc := by
  have := p.one_le_s
  ext
  simp only [val_outerObj, Fin.val_castSucc, Fin.val_natAdd, val_rightInput]
  split_ifs <;> omega

/-- After the inner output, the target of an outer input is the target of the original
input. -/
@[simp]
lemma outerObj_right_succ (k : Fin p.t) :
    p.outerObj (k.natAdd (p.r + 1)).succ = (p.rightInput k).succ := by
  have := p.one_le_s
  ext
  simp only [val_outerObj, Fin.val_succ, Fin.val_natAdd, val_rightInput]
  split_ifs <;> omega

/-- The first r inputs, the s inputs of the inner operation and the last t inputs make up
all n inputs. -/
@[to_additive /-- The first r inputs, the s inputs of the inner operation and the last t inputs
make up all n inputs. -/]
lemma prod_leftInput_mul_prod_innerInput_mul_prod_rightInput {M : Type*} [CommMonoid M]
    (f : Fin n → M) :
    (∏ j, f (p.leftInput j)) * (∏ j, f (p.innerInput j)) * ∏ k, f (p.rightInput k) = ∏ i, f i := by
  rw [← Fin.prod_congr' f p.sum_eq, Fin.prod_univ_add, Fin.prod_univ_add]
  rfl

end StasheffIndex

section ObjectStrings

variable {Obj : Type w} (X : Fin (n + 1) → Obj) (p : StasheffIndex n)

/-- The object string of the inner operation of the (r, s, t) summand: the objects of `X`
from position r to position r + s. -/
def stasheffObjIn : Fin (p.s + 1) → Obj :=
  fun i ↦ X (p.innerObj i)

/-- The object string of the outer operation of the (r, s, t) summand, obtained from `X` by
deleting the objects strictly between positions r and r + s. -/
def stasheffObjOut : Fin (p.r + 1 + p.t + 1) → Obj :=
  fun i ↦ X (p.outerObj i)

/-- The outer object string starts at `X 0`. -/
@[simp]
lemma stasheffObjOut_zero : stasheffObjOut X p 0 = X 0 :=
  congrArg X p.outerObj_zero

/-- The outer object string ends at `X (Fin.last n)`. -/
@[simp]
lemma stasheffObjOut_last : stasheffObjOut X p (Fin.last (p.r + 1 + p.t)) = X (Fin.last n) :=
  congrArg X p.outerObj_last

/-- Before the inner output, the source of an outer input is the source of the original
input. -/
@[simp]
lemma stasheffObjOut_left_castSucc (j : Fin p.r) :
    stasheffObjOut X p (j.castSucc.castAdd p.t).castSucc = X (p.leftInput j).castSucc :=
  congrArg X (p.outerObj_left_castSucc j)

/-- Before the inner output, the target of an outer input is the target of the original
input. -/
@[simp]
lemma stasheffObjOut_left_succ (j : Fin p.r) :
    stasheffObjOut X p (j.castSucc.castAdd p.t).succ = X (p.leftInput j).succ :=
  congrArg X (p.outerObj_left_succ j)

/-- The source of the inner output, as an outer input, is the first inner object. -/
@[simp]
lemma stasheffObjOut_middle_castSucc :
    stasheffObjOut X p p.middleIndex.castSucc = stasheffObjIn X p 0 :=
  congrArg X p.outerObj_middle_castSucc

/-- The target of the inner output, as an outer input, is the last inner object. -/
@[simp]
lemma stasheffObjOut_middle_succ :
    stasheffObjOut X p p.middleIndex.succ = stasheffObjIn X p (Fin.last p.s) :=
  congrArg X p.outerObj_middle_succ

/-- After the inner output, the source of an outer input is the source of the original
input. -/
@[simp]
lemma stasheffObjOut_right_castSucc (k : Fin p.t) :
    stasheffObjOut X p (k.natAdd (p.r + 1)).castSucc = X (p.rightInput k).castSucc :=
  congrArg X (p.outerObj_right_castSucc k)

/-- After the inner output, the target of an outer input is the target of the original
input. -/
@[simp]
lemma stasheffObjOut_right_succ (k : Fin p.t) :
    stasheffObjOut X p (k.natAdd (p.r + 1)).succ = X (p.rightInput k).succ :=
  congrArg X (p.outerObj_right_succ k)

end ObjectStrings

section Degrees

variable {β : Type v} [AddCommGroup β] [Grading β] (deg : Fin n → β) (p : StasheffIndex n)

/-- The input degrees of the inner operation mₛ of the (r, s, t) summand: the degrees of
the s inputs after the first r. -/
def stasheffDegIn : Fin p.s → β :=
  fun j ↦ deg (p.innerInput j)

/-- The degree of the output of the inner operation mₛ of the (r, s, t) summand. -/
def stasheffInnerDeg : β :=
  operationTargetDeg (stasheffDegIn deg p)

/-- The input degrees of the outer operation of the (r, s, t) summand: the degrees of the
first r inputs, then the degree of the inner output, then the degrees of the last t inputs. -/
def stasheffDegOut : Fin (p.r + 1 + p.t) → β :=
  Fin.append (Fin.snoc (fun j ↦ deg (p.leftInput j)) (stasheffInnerDeg deg p))
    fun k ↦ deg (p.rightInput k)

@[simp]
lemma stasheffDegOut_left (j : Fin p.r) :
    stasheffDegOut deg p (j.castSucc.castAdd p.t) = deg (p.leftInput j) := by
  simp [stasheffDegOut]

@[simp]
lemma stasheffDegOut_middle : stasheffDegOut deg p p.middleIndex = stasheffInnerDeg deg p := by
  simp [stasheffDegOut]

@[simp]
lemma stasheffDegOut_right (k : Fin p.t) :
    stasheffDegOut deg p (k.natAdd (p.r + 1)) = deg (p.rightInput k) := by
  simp [stasheffDegOut]

/-- The outer operation has the Stasheff target degree. -/
lemma stasheffDegOut_sum :
    operationTargetDeg (stasheffDegOut deg p) = stasheffTargetDeg deg := by
  have h : (n : ℤ) = p.r + p.s + p.t := by exact_mod_cast p.sum_eq.symm
  simp only [operationTargetDeg, stasheffTargetDeg, Fin.sum_univ_add, stasheffDegOut_left,
    stasheffDegOut_middle, stasheffDegOut_right, Fin.sum_univ_castSucc, stasheffInnerDeg,
    stasheffDegIn, ← p.sum_leftInput_add_sum_innerInput_add_sum_rightInput deg]
  rw [h]
  module

/-- The Koszul sign of the Stasheff term indexed by p = (r, s, t): (-1) raised to the sum of
the reduced degrees ‖a‖ = |a| - 1 of the last t inputs. -/
def stasheffSign : ℤˣ :=
  ∏ k : Fin p.t, (sign (deg (p.rightInput k) - degOne)).toMul

/-- The signed sum `∑ p, stasheffSign deg p • f p` over the index triples `p : StasheffIndex n`
of the arity-n Stasheff identity. Both the Stasheff identities and the A∞-functor equations are
sums of this form. -/
def signedStasheffSum {M : Type*} [AddCommGroup M] (f : StasheffIndex n → M) : M :=
  ∑ q, stasheffSign deg q • f q

variable {deg}

lemma signedStasheffSum_eq_zero {M : Type*} [AddCommGroup M] {f : StasheffIndex n → M}
    (h : ∀ q, f q = 0) :
    signedStasheffSum deg f = 0 :=
  Finset.sum_eq_zero fun q _ => smul_eq_zero_of_right _ (h q)

lemma map_signedStasheffSum {M N G : Type*} [AddCommGroup M] [AddCommGroup N] [FunLike G M N]
    [AddMonoidHomClass G M N] (g : G) (f : StasheffIndex n → M) :
    g (signedStasheffSum deg f) = signedStasheffSum deg fun q => g (f q) := by
  simp only [signedStasheffSum, map_sum, Units.smul_def, map_zsmul]

end Degrees

end AInfinityTheory
