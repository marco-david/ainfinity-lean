/-
Copyright (c) 2026 Zhan Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhan Shi
-/
module

public import AInfinity.AInfinityCategory

/-! # `A∞`-categories with vanishing higher operations

Many `A∞`-categories, such as DG categories, have vanishing higher compositions `mₙ` for
`n ≥ 3`. Such a structure is determined by a differential `m₁` and a composition `m₂`, and its
Stasheff identities reduce to three identities in arities `1`, `2` and `3`: `m₁` squares to
zero, `m₁` is a derivation of `m₂` (the Leibniz rule), and `m₂` is associative, all with Koszul
signs. In arity at least `4`, every Stasheff term involves an operation of arity at least `3`,
and vanishes.

## Main definitions

* `AInfinityTheory.AInfinityCategoryStruct.ofArityLeTwo f g`: the `A∞`-category structure with
  `m₁` given by a family `f` of graded linear maps of degree `1`, `m₂` given by a family `g` of
  bilinear maps of degree `0`, and `mₙ = 0` for `n ≥ 3`.
* `AInfinityTheory.AInfinityCategory.ofArityLeTwo`: the `A∞`-category with these operations,
  from the Stasheff identities in arities `1`, `2` and `3`.

## Implementation notes

The operations of `AInfinityCategoryStruct.ofArityLeTwo f g` read a composable string of
objects `X` only at `X 0`, `X 1` and `X 2`. Hence, for a concrete index triple, a Stasheff term
is definitionally an expression in `f` and `g`. The hypotheses of
`AInfinityCategory.ofArityLeTwo` are stated in exactly the form produced by
`stasheffSum_arity_one`, `stasheffSum_arity_two` and `stasheffSum_arity_three`, with all
intermediate degrees free and constrained by equations, so that they apply without any
transport. As in Mathlib's `CochainComplex.HomComplex.Cochain.comp_assoc`, there is exactly one
equation per dependent degree; the remaining degree equations are derived inside the
statements, so callers never have to supply them.
-/

@[expose] public section

namespace AInfinityTheory

universe u v w

open GradedLinearQuiver

variable {β : Type v} [AddCommGroup β] [Grading β] {R : Type u} [CommRing R] {Obj : Type w}
  [GradedLinearQuiver β R Obj]
  (f : ∀ X Y : Obj, GradedLinearMap R (X →ᵍ[R, β] Y) (X →ᵍ[R] Y) degOne)
  (g : ∀ (X Y Z : Obj) (p q i : β), p + q = i →
    (X →ᵍ[R, β] Y) p →ₗ[R] (Y →ᵍ[R] Z) q →ₗ[R] (X →ᵍ[R] Z) i)

-- Arity 1: the differential squares to zero.
  (differential_differential :
    ∀ (X Y : Obj) {p q r : β} (hpq : p + degOne = q)
      (hqr : q + degOne = r) (a : (X →ᵍ[R] Y) p), (f X Y).v q r hqr ((f X Y).v p q hpq a) = 0)

-- Arity 2: the Leibniz rule.
  (leibniz :
    ∀ (X Y Z : Obj) {p q e p' q' d : β} (h : p + q = e)
      (hp : p + degOne = p') (hq : q + degOne = q') (he : e + degOne = d)
      (a : (X →ᵍ[R] Y) p) (b : (Y →ᵍ[R] Z) q),
      (sign (q - degOne)).toMul • g X Y Z p' q d (hp ▸ he ▸ h ▸ add_right_comm p degOne q)
          ((f X Y).v p p' hp a) b +
        g X Y Z p q' d (hq ▸ he ▸ h ▸ (add_assoc p q degOne).symm) a ((f Y Z).v q q' hq b) +
        (f X Z).v e d he (g X Y Z p q e h a b) = 0)

-- Arity 3: associativity of the composition.
  (assoc :
    ∀ (W X Y Z : Obj) {p q r e e' d : β} (h : p + q = e) (h' : q + r = e')
      (h₁ : e + r = d) (a : (W →ᵍ[R] X) p) (b : (X →ᵍ[R] Y) q) (c : (Y →ᵍ[R] Z) r),
      (sign (r - degOne)).toMul • g W Y Z e r d h₁ (g W X Y p q e h a b) c +
        g W X Z p e' d (h' ▸ h₁ ▸ h ▸ (add_assoc p q r).symm) a (g X Y Z q r e' h' b c) = 0)

/-- The `A∞`-category structure whose differential `m₁` is given by the graded linear maps `f`,
whose composition `m₂` is given by the bilinear maps `g`, and whose higher compositions `mₙ`
for `n ≥ 3` vanish. -/
abbrev AInfinityCategoryStruct.ofArityLeTwo : AInfinityCategoryStruct β R Obj where
  toGradedLinearQuiver := ‹_›
  m := AInfinityOperation.ofArityLeTwo (fun X ↦ .ofGradedLinearMap (f (X 0) (X 1)))
    (fun X ↦ .ofBilinear (g (X 0) (X 1) (X 2)))

namespace AInfinityCategoryStruct.ofArityLeTwo

/-- The higher compositions vanish in every arity other than `1` and `2`. -/
lemma m_eq_zero {k : ℕ} [NeZero k] (hk : k ∉ ({1, 2} : Set ℕ)) (X : Fin (k + 1) → Obj) :
    letI := ofArityLeTwo f g
    m (β := β) (R := R) X = 0 :=
  AInfinityOperation.ofArityLeTwo_eq_zero _ _ (by simp_all) (by simp_all) X

include differential_differential in
/-- The arity-one Stasheff identity holds as soon as the differential squares to zero. -/
lemma stasheffSum_eq_zero_of_arity_one {X : Fin (1 + 1) → Obj} {deg : Fin 1 → β}
    (x : ∀ i : Fin 1, ComposableHom β R X i (deg i)) {d : β} (hd : stasheffTargetDeg deg = d) :
    letI := ofArityLeTwo f g
    stasheffSum x d hd = 0 := by
  letI := ofArityLeTwo f g
  rw [stasheffSum_arity_one]
  exact differential_differential (X 0) (X 1) _ _ (x 0)

include leibniz in
/-- The arity-two Stasheff identity holds as soon as the Leibniz rule does. -/
lemma stasheffSum_eq_zero_of_arity_two {X : Fin (2 + 1) → Obj} {deg : Fin 2 → β}
    (x : ∀ i : Fin 2, ComposableHom β R X i (deg i)) {d : β} (hd : stasheffTargetDeg deg = d) :
    letI := ofArityLeTwo f g
    stasheffSum x d hd = 0 := by
  letI := ofArityLeTwo f g
  rw [stasheffSum_arity_two]
  exact leibniz (X 0) (X 1) (X 2) _ _ _ _ (x 0) (x 1)

include assoc in
/-- The arity-three Stasheff identity holds as soon as the composition is associative up to
the Koszul sign: the four terms involving an operation of arity `3` vanish. -/
lemma stasheffSum_eq_zero_of_arity_three {X : Fin (3 + 1) → Obj} {deg : Fin 3 → β}
    (x : ∀ i : Fin 3, ComposableHom β R X i (deg i)) {d : β} (hd : stasheffTargetDeg deg = d) :
    letI := ofArityLeTwo f g
    stasheffSum x d hd = 0 := by
  letI := ofArityLeTwo f g
  have hm := fun (k : ℕ) [NeZero k] hk X ↦ m_eq_zero (β := β) (R := R) f g (k := k) hk X
  rw [stasheffSum_arity_three,
    stasheffTerm_eq_zero_of_arity_notMem {1, 2} hm x ⟨0, 1, 2, rfl, le_rfl⟩ (by simp) d hd,
    stasheffTerm_eq_zero_of_arity_notMem {1, 2} hm x ⟨1, 1, 1, rfl, le_rfl⟩ (by simp) d hd,
    stasheffTerm_eq_zero_of_arity_notMem {1, 2} hm x ⟨2, 1, 0, rfl, le_rfl⟩ (by simp) d hd,
    stasheffTerm_eq_zero_of_arity_notMem {1, 2} hm x ⟨0, 3, 0, rfl, by decide⟩ (by simp) d hd]
  simp only [smul_zero, zero_add, add_zero]
  exact assoc (X 0) (X 1) (X 2) (X 3) _ _ _ (x 0) (x 1) (x 2)

/-- The Stasheff identities hold in every arity `n ≥ 4`: each Stasheff term involves an
operation of arity at least `3`, which vanishes. -/
lemma stasheffSum_eq_zero_of_four_le {n : ℕ} (hn : 4 ≤ n) {X : Fin (n + 1) → Obj}
    {deg : Fin n → β} (x : ∀ i : Fin n, ComposableHom β R X i (deg i)) {d : β}
    (hd : stasheffTargetDeg deg = d) :
    letI := ofArityLeTwo f g
    stasheffSum x d hd = 0 :=
  letI := ofArityLeTwo f g
  stasheffSum_eq_zero_of_arity_notMem {1, 2} (fun _ _ hk X ↦ m_eq_zero f g hk X)
    (fun p ↦ by
      have := p.sum_eq
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      omega)
    x d hd

end AInfinityCategoryStruct.ofArityLeTwo

open AInfinityCategoryStruct.ofArityLeTwo in
include differential_differential leibniz assoc in
/-- An `A∞`-category whose higher compositions `mₙ` for `n ≥ 3` vanish, with differential `m₁`
given by `f` and composition `m₂` given by `g`, from the Stasheff identities in arities `1`,
`2` and `3`: `m₁` squares to zero, `m₁` is a derivation of `m₂`, and `m₂` is associative, all
with Koszul signs. -/
abbrev AInfinityCategory.ofArityLeTwo : AInfinityCategory β R Obj where
  __ := AInfinityCategoryStruct.ofArityLeTwo f g
  stasheffSum_eq_zero {n} _ X deg x d hd := by
    rcases n with _ | _ | _ | _ | n
    · exact absurd rfl (NeZero.ne 0)
    · exact stasheffSum_eq_zero_of_arity_one f g differential_differential x hd
    · exact stasheffSum_eq_zero_of_arity_two f g leibniz x hd
    · exact stasheffSum_eq_zero_of_arity_three f g assoc x hd
    · exact stasheffSum_eq_zero_of_four_le f g (by omega) x hd

end AInfinityTheory
