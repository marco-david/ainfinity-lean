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
* `AInfinityTheory.StasheffIndex.leftEmb`, `AInfinityTheory.StasheffIndex.innerEmb`,
  `AInfinityTheory.StasheffIndex.rightEmb`: the positions of the first r inputs, of the s inputs
  of the inner operation and of the last t inputs among the n inputs.
* `AInfinityTheory.StasheffIndex.innerObjEmb`, `AInfinityTheory.StasheffIndex.outerObjEmb`: the
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

* `AInfinityTheory.StasheffIndex.sum_leftEmb_add_sum_innerEmb_add_sum_rightEmb`: the first r
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
inner operation and the objects 0, …, r and r + s, …, n of the outer operation. The order
embeddings below record these positions, in the way `Composition.embedding` and
`Composition.boundary` record the blocks of a composition. -/

/-- The positions 0, …, r - 1 of the first r inputs among the n inputs. -/
def leftEmb : Fin p.r ↪o Fin n :=
  Fin.castLEOrderEmb ((Nat.le_add_right p.r p.s).trans (Nat.le.intro p.sum_eq))

/-- The positions r, …, r + s - 1 of the inputs of the inner operation among the n inputs. -/
def innerEmb : Fin p.s ↪o Fin n :=
  (Fin.natAddOrderEmb p.r).trans (Fin.castLEOrderEmb (Nat.le.intro p.sum_eq))

/-- The positions r + s, …, n - 1 of the last t inputs among the n inputs. -/
def rightEmb : Fin p.t ↪o Fin n :=
  (Fin.natAddOrderEmb (p.r + p.s)).trans (Fin.castLEOrderEmb p.sum_eq.le)

/-- The positions r, …, r + s of the objects of the inner operation among the n + 1
objects. -/
def innerObjEmb : Fin (p.s + 1) ↪o Fin (n + 1) :=
  (Fin.natAddOrderEmb p.r).trans (Fin.castLEOrderEmb (Nat.succ_le_succ (Nat.le.intro p.sum_eq)))

/-- The positions 0, …, r and r + s, …, n of the objects of the outer operation among the
n + 1 objects: the objects strictly between positions r and r + s are skipped. -/
def outerObjEmb : Fin (p.r + 1 + p.t + 1) ↪o Fin (n + 1) :=
  OrderEmbedding.ofStrictMono
    (fun i ↦ ⟨if (i : ℕ) ≤ p.r then (i : ℕ) else i + p.s - 1, by
      have := p.sum_eq; have := p.one_le_s; have := i.isLt; split_ifs <;> omega⟩)
    (fun i j hij ↦ by have := p.one_le_s; simp only [Fin.lt_def] at hij ⊢; split_ifs <;> omega)

/-- The position r of the inner output among the inputs of the outer operation, of arity
r + 1 + t. -/
abbrev middleIndex : Fin (p.r + 1 + p.t) :=
  (Fin.last p.r).castAdd p.t

@[simp]
lemma val_leftEmb (j : Fin p.r) : (p.leftEmb j : ℕ) = j :=
  rfl

@[simp]
lemma val_innerEmb (j : Fin p.s) : (p.innerEmb j : ℕ) = p.r + j :=
  rfl

@[simp]
lemma val_rightEmb (k : Fin p.t) : (p.rightEmb k : ℕ) = p.r + p.s + k :=
  rfl

@[simp]
lemma val_innerObjEmb (j : Fin (p.s + 1)) : (p.innerObjEmb j : ℕ) = p.r + j :=
  rfl

@[simp]
lemma val_outerObjEmb (i : Fin (p.r + 1 + p.t + 1)) :
    (p.outerObjEmb i : ℕ) = if (i : ℕ) ≤ p.r then (i : ℕ) else i + p.s - 1 :=
  rfl

/-- The source of the `j`-th input of the inner operation is the `j`-th inner object. -/
@[simp]
lemma innerObjEmb_castSucc (j : Fin p.s) : p.innerObjEmb j.castSucc = (p.innerEmb j).castSucc :=
  rfl

/-- The target of the `j`-th input of the inner operation is the `(j + 1)`-st inner object. -/
@[simp]
lemma innerObjEmb_succ (j : Fin p.s) : p.innerObjEmb j.succ = (p.innerEmb j).succ :=
  rfl

/-- The outer object string starts at the object 0. -/
@[simp]
lemma outerObjEmb_zero : p.outerObjEmb 0 = 0 :=
  Fin.ext (by simp)

/-- The outer object string ends at the object n. -/
@[simp]
lemma outerObjEmb_last : p.outerObjEmb (Fin.last _) = Fin.last n := by
  have := p.sum_eq
  have := p.one_le_s
  ext
  simp only [val_outerObjEmb, Fin.val_last]
  split_ifs <;> omega

/-- Before the inner output, the source of an outer input is the source of the original
input. -/
@[simp]
lemma outerObjEmb_left_castSucc (j : Fin p.r) :
    p.outerObjEmb (j.castSucc.castAdd p.t).castSucc = (p.leftEmb j).castSucc :=
  Fin.ext (by simp [j.isLt.le])

/-- Before the inner output, the target of an outer input is the target of the original
input. -/
@[simp]
lemma outerObjEmb_left_succ (j : Fin p.r) :
    p.outerObjEmb (j.castSucc.castAdd p.t).succ = (p.leftEmb j).succ :=
  Fin.ext (by simp [j.isLt])

/-- The source of the inner output, as an outer input, is the first inner object. -/
@[simp]
lemma outerObjEmb_middle_castSucc : p.outerObjEmb p.middleIndex.castSucc = p.innerObjEmb 0 :=
  Fin.ext (by simp)

/-- The target of the inner output, as an outer input, is the last inner object. -/
@[simp]
lemma outerObjEmb_middle_succ :
    p.outerObjEmb p.middleIndex.succ = p.innerObjEmb (Fin.last p.s) := by
  have := p.one_le_s
  ext
  simp only [val_outerObjEmb, Fin.val_succ, Fin.val_castAdd, Fin.val_last, val_innerObjEmb]
  split_ifs <;> omega

/-- After the inner output, the source of an outer input is the source of the original
input. -/
@[simp]
lemma outerObjEmb_right_castSucc (k : Fin p.t) :
    p.outerObjEmb (k.natAdd (p.r + 1)).castSucc = (p.rightEmb k).castSucc := by
  have := p.one_le_s
  ext
  simp only [val_outerObjEmb, Fin.val_castSucc, Fin.val_natAdd, val_rightEmb]
  split_ifs <;> omega

/-- After the inner output, the target of an outer input is the target of the original
input. -/
@[simp]
lemma outerObjEmb_right_succ (k : Fin p.t) :
    p.outerObjEmb (k.natAdd (p.r + 1)).succ = (p.rightEmb k).succ := by
  have := p.one_le_s
  ext
  simp only [val_outerObjEmb, Fin.val_succ, Fin.val_natAdd, val_rightEmb]
  split_ifs <;> omega

/-- The first r inputs, the s inputs of the inner operation and the last t inputs make up
all n inputs. -/
@[to_additive /-- The first r inputs, the s inputs of the inner operation and the last t inputs
make up all n inputs. -/]
lemma prod_leftEmb_mul_prod_innerEmb_mul_prod_rightEmb {M : Type*} [CommMonoid M]
    (f : Fin n → M) :
    (∏ j, f (p.leftEmb j)) * (∏ j, f (p.innerEmb j)) * ∏ k, f (p.rightEmb k) = ∏ i, f i := by
  rw [← Fin.prod_congr' f p.sum_eq, Fin.prod_univ_add, Fin.prod_univ_add]
  rfl

end StasheffIndex

section ObjectStrings

variable {Obj : Type w} (X : Fin (n + 1) → Obj) (p : StasheffIndex n)

/-- The object string of the inner operation of the (r, s, t) summand: the objects of `X`
from position r to position r + s. -/
def stasheffObjIn : Fin (p.s + 1) → Obj :=
  fun i ↦ X (p.innerObjEmb i)

/-- The object string of the outer operation of the (r, s, t) summand, obtained from `X` by
deleting the objects strictly between positions r and r + s. -/
def stasheffObjOut : Fin (p.r + 1 + p.t + 1) → Obj :=
  fun i ↦ X (p.outerObjEmb i)

/-- The outer object string starts at `X 0`. -/
@[simp]
lemma stasheffObjOut_zero : stasheffObjOut X p 0 = X 0 :=
  congrArg X p.outerObjEmb_zero

/-- The outer object string ends at `X (Fin.last n)`. -/
@[simp]
lemma stasheffObjOut_last : stasheffObjOut X p (Fin.last (p.r + 1 + p.t)) = X (Fin.last n) :=
  congrArg X p.outerObjEmb_last

/-- Before the inner output, the source of an outer input is the source of the original
input. -/
@[simp]
lemma stasheffObjOut_left_castSucc (j : Fin p.r) :
    stasheffObjOut X p (j.castSucc.castAdd p.t).castSucc = X (p.leftEmb j).castSucc :=
  congrArg X (p.outerObjEmb_left_castSucc j)

/-- Before the inner output, the target of an outer input is the target of the original
input. -/
@[simp]
lemma stasheffObjOut_left_succ (j : Fin p.r) :
    stasheffObjOut X p (j.castSucc.castAdd p.t).succ = X (p.leftEmb j).succ :=
  congrArg X (p.outerObjEmb_left_succ j)

/-- The source of the inner output, as an outer input, is the first inner object. -/
@[simp]
lemma stasheffObjOut_middle_castSucc :
    stasheffObjOut X p p.middleIndex.castSucc = stasheffObjIn X p 0 :=
  congrArg X p.outerObjEmb_middle_castSucc

/-- The target of the inner output, as an outer input, is the last inner object. -/
@[simp]
lemma stasheffObjOut_middle_succ :
    stasheffObjOut X p p.middleIndex.succ = stasheffObjIn X p (Fin.last p.s) :=
  congrArg X p.outerObjEmb_middle_succ

/-- After the inner output, the source of an outer input is the source of the original
input. -/
@[simp]
lemma stasheffObjOut_right_castSucc (k : Fin p.t) :
    stasheffObjOut X p (k.natAdd (p.r + 1)).castSucc = X (p.rightEmb k).castSucc :=
  congrArg X (p.outerObjEmb_right_castSucc k)

/-- After the inner output, the target of an outer input is the target of the original
input. -/
@[simp]
lemma stasheffObjOut_right_succ (k : Fin p.t) :
    stasheffObjOut X p (k.natAdd (p.r + 1)).succ = X (p.rightEmb k).succ :=
  congrArg X (p.outerObjEmb_right_succ k)

end ObjectStrings

section Degrees

variable {β : Type v} [AddCommGroup β] [Grading β] (deg : Fin n → β) (p : StasheffIndex n)

/-- The input degrees of the inner operation mₛ of the (r, s, t) summand: the degrees of
the s inputs after the first r. -/
def stasheffDegIn : Fin p.s → β :=
  fun j ↦ deg (p.innerEmb j)

/-- The degree of the output of the inner operation mₛ of the (r, s, t) summand. -/
abbrev stasheffInnerDeg : β :=
  operationTargetDeg (stasheffDegIn deg p)

/-- The input degrees of the outer operation of the (r, s, t) summand: the degrees of the
first r inputs, then the degree of the inner output, then the degrees of the last t inputs. -/
def stasheffDegOut : Fin (p.r + 1 + p.t) → β :=
  Fin.append (Fin.snoc (fun j ↦ deg (p.leftEmb j)) (stasheffInnerDeg deg p))
    fun k ↦ deg (p.rightEmb k)

@[simp]
lemma stasheffDegOut_left (j : Fin p.r) :
    stasheffDegOut deg p (j.castSucc.castAdd p.t) = deg (p.leftEmb j) := by
  simp [stasheffDegOut]

@[simp]
lemma stasheffDegOut_middle : stasheffDegOut deg p p.middleIndex = stasheffInnerDeg deg p := by
  simp [stasheffDegOut]

@[simp]
lemma stasheffDegOut_right (k : Fin p.t) :
    stasheffDegOut deg p (k.natAdd (p.r + 1)) = deg (p.rightEmb k) := by
  simp [stasheffDegOut]

/-- The outer operation has the Stasheff target degree. -/
lemma stasheffDegOut_sum :
    operationTargetDeg (stasheffDegOut deg p) = stasheffTargetDeg deg := by
  have h : (n : ℤ) = p.r + p.s + p.t := by exact_mod_cast p.sum_eq.symm
  simp only [operationTargetDeg, stasheffTargetDeg, Fin.sum_univ_add, stasheffDegOut_left,
    stasheffDegOut_middle, stasheffDegOut_right, Fin.sum_univ_castSucc, stasheffInnerDeg,
    stasheffDegIn, ← p.sum_leftEmb_add_sum_innerEmb_add_sum_rightEmb deg]
  rw [h]
  module

/-- The Koszul sign of the Stasheff term indexed by p = (r, s, t): (-1) raised to the sum of
the reduced degrees ‖a‖ = |a| - 1 of the last t inputs. -/
def stasheffSign : ℤˣ :=
  ∏ k : Fin p.t, (sign (deg (p.rightEmb k) - degOne)).toMul

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
