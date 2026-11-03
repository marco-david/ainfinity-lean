/-
Copyright (c) 2026 Annie Yao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Annie Yao, Marco David, Zhan Shi
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import AInfinity.Grading
public import Mathlib.Tactic.Module

/-! # Index triples of the Stasheff identities

The arity-`n` Stasheff identity is a signed sum over the triples `(r, s, t)` with
`r + s + t = n` and `1 ≤ s`: the `(r, s, t)` summand applies an inner operation `mₛ` to the
inputs `a_{r+1}, …, a_{r+s}` and an outer operation `m_{r+1+t}` to the result together with the
remaining inputs. This file handles the bookkeeping attached to such a triple that does not
involve any hom spaces: the degrees and object strings of the inner and outer operations, and
the Koszul sign of the summand.

## Main definitions

* `AInfinityTheory.operationTargetDeg`, `AInfinityTheory.stasheffTargetDeg`: the degrees of
  `mₙ(a₁, …, aₙ)` and of the arity-`n` Stasheff identity.
* `AInfinityTheory.StasheffIndex`: the index triples `(r, s, t)` with `r + s + t = n` and
  `1 ≤ s`.
* `AInfinityTheory.stasheffDegOut`, `AInfinityTheory.stasheffObjOut`: the input degrees and the
  object string of the outer operation of the `(r, s, t)` summand.
* `AInfinityTheory.stasheffSign`: the Koszul sign of the `(r, s, t)` summand.
* `AInfinityTheory.signedStasheffSum`: the sum of a family of `(r, s, t)` terms with these signs.
  Both the Stasheff identities and the `A∞`-functor equations are sums of this form.
-/

@[expose] public section

namespace AInfinityTheory

universe v w

variable {β : Type v} [AddCommGroup β] [Grading β]
variable {n : ℕ}

/-- The degree of `mₙ(a₁, …, aₙ)` for inputs `aᵢ` of degrees `deg i`, where `mₙ` itself has
degree `2 - n`. -/
abbrev operationTargetDeg
    (deg : Fin n → β) : β :=
  (∑ i, deg i) + (2 - n : ℤ) • degOne

/-- Target degree of the arity-`n` Stasheff identity on inputs of degrees `deg`. -/
abbrev stasheffTargetDeg
    (deg : Fin n → β) : β :=
  (∑ i, deg i) + (3 - n : ℤ) • degOne

/-- The arity-`n` Stasheff identity has degree one more than the `n`-ary operation `mₙ`. -/
lemma stasheffTargetDeg_eq_operationTargetDeg_add_degOne
    (deg : Fin n → β) :
    stasheffTargetDeg deg = operationTargetDeg deg + degOne := by
  rw [stasheffTargetDeg, operationTargetDeg]
  module

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

/-- The only index triple in arity `1` is `(0, 1, 0)`. -/
lemma StasheffIndex.univ_one :
    (Finset.univ : Finset (StasheffIndex 1)) = {⟨0, 1, 0, rfl, le_rfl⟩} := by
  decide

/-- The index triples in arity `2`. -/
lemma StasheffIndex.univ_two : (Finset.univ : Finset (StasheffIndex 2)) =
    {⟨0, 1, 1, rfl, le_rfl⟩, ⟨1, 1, 0, rfl, le_rfl⟩, ⟨0, 2, 0, rfl, one_le_two⟩} := by
  decide

/-- The index triples in arity `3`. -/
lemma StasheffIndex.univ_three : (Finset.univ : Finset (StasheffIndex 3)) =
    {⟨0, 1, 2, rfl, le_rfl⟩, ⟨1, 1, 1, rfl, le_rfl⟩, ⟨2, 1, 0, rfl, le_rfl⟩,
      ⟨0, 2, 1, rfl, one_le_two⟩, ⟨1, 2, 0, rfl, one_le_two⟩, ⟨0, 3, 0, rfl, by decide⟩} := by
  decide

/-- The inner operation of a Stasheff term has positive arity. -/
instance (p : StasheffIndex n) : NeZero p.s :=
  ⟨by have := p.one_le_s; omega⟩

/-- The outer operation of a Stasheff term has positive arity. -/
instance (p : StasheffIndex n) : NeZero (p.r + 1 + p.t) :=
  ⟨by omega⟩

variable {Obj : Type w}
variable (X : Fin (n + 1) → Obj) (deg : Fin n → β)

section

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

/-- Helper: the inner object string `X r, …, X (r + s)`. -/
def stasheffObjIn : Fin (p.s + 1) → Obj :=
  fun j => X ((j.natAdd p.r).castLE (by have := p.sum_eq; omega))

/-- Helper: the outer object string `X 0, …, X r, X (r + s), …, X n` obtained by
collapsing the inner block. -/
def stasheffObjOut : Fin (p.r + 1 + p.t + 1) → Obj :=
  Fin.append (m := p.r + 1) (fun j : Fin (p.r + 1) => X (j.castLE (by have := p.sum_eq; omega)))
      (fun k : Fin (p.t + 1) =>
        X ((k.natAdd (p.r + p.s)).cast (by have := p.sum_eq; omega)))

/-- Up to the inner block, the outer object string agrees with the original one. -/
@[simp]
lemma stasheffObjOut_left
    (j : Fin (p.r + 1)) :
    stasheffObjOut X p (j.castLE (by omega)) =
      X (j.castLE (by have := p.sum_eq; omega)) := by
  simp [stasheffObjOut]

/-- After the inner block, the outer object string agrees with the original one, shifted by
`s - 1`. -/
@[simp]
lemma stasheffObjOut_right
    (k : Fin (p.t + 1)) :
    stasheffObjOut X p (k.natAdd (p.r + 1)) =
      X ((k.natAdd (p.r + p.s)).cast (by have := p.sum_eq; omega)) := by
  simp [stasheffObjOut]

/-- The outer object string starts at `X 0`. -/
@[simp]
lemma stasheffObjOut_zero : stasheffObjOut X p 0 = X 0 :=
  stasheffObjOut_left X p 0

/-- The outer object string ends at `X (Fin.last n)`. -/
@[simp]
lemma stasheffObjOut_last :
    stasheffObjOut X p (Fin.last (p.r + 1 + p.t)) = X (Fin.last n) :=
  (stasheffObjOut_right X p (Fin.last p.t)).trans (congrArg X (Fin.ext p.sum_eq))

/-- The outer operation has the Stasheff target degree. -/
lemma stasheffDegOut_sum :
    operationTargetDeg (stasheffDegOut deg p) = stasheffTargetDeg deg := by
  have h : (n : ℤ) = p.r + p.s + p.t := by exact_mod_cast p.sum_eq.symm
  simp only [operationTargetDeg, stasheffTargetDeg, Fin.sum_univ_add, stasheffDegOut_left,
    stasheffDegOut_middle, stasheffDegOut_right, Fin.sum_univ_castSucc, stasheffInnerDeg,
    stasheffDegIn, ← Fin.sum_congr' deg p.sum_eq]
  rw [h]
  module

variable {deg}

variable (deg) in
/-- The Koszul sign `(-1)^(‖a_{r+s+1}‖ + ⋯ + ‖aₙ‖)` of the Stasheff term indexed by
`p = (r, s, t)`, where `‖a‖ = |a| - 1` is the reduced degree of an input after the inner
operation. -/
def stasheffSign : ℤˣ :=
  ∏ k : Fin p.t, sign (deg ((k.natAdd (p.r + p.s)).cast p.sum_eq) - degOne)

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

end

end AInfinityTheory
