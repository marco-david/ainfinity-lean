/-
Copyright (c) 2026 Zhan Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhan Shi
-/
module

public import Mathlib.Combinatorics.Enumerative.Composition
public import Mathlib.LinearAlgebra.Multilinear.Curry

/-! # Constructions on multilinear maps

This file builds multilinear maps in one or two variables from linear and bilinear maps,
for dependent families of modules. It saves proving the `map_update_add'` and
`map_update_smul'` fields of `MultilinearMap` by hand. It also composes a multilinear map in k
variables with k multilinear maps along a composition of `n` into k blocks.

## Main definitions

* `MultilinearMap.ofSubsingletonₗ'`: when `ι` has at most one element `i`, linear maps
  `M i →ₗ[R] N` are equivalent to multilinear maps on the family `M`.
* `LinearMap.uncurryFinTwo`: a bilinear map `M 0 →ₗ[R] M 1 →ₗ[R] N` as a multilinear map on a
  family `M` indexed by `Fin 2`.
* `MultilinearMap.compComposition`: the composite of a multilinear map in k variables with k
  multilinear maps, one on each block of a composition of `n`. Mathlib's `compAlongComposition`
  is the special case of continuous multilinear maps between constant families.

## Main results

* `MultilinearMap.map_eq_sum_units_smul_update`: expanding a multilinear map in one variable
  whose input is a sum with signs.

## Implementation notes

Mathlib's `MultilinearMap.ofSubsingleton` only covers non-dependent families `fun _ : ι ↦ M₂`.
It does not apply to a family such as `fun k : Fin 1 ↦ M k.castSucc`, because `k.castSucc` is
not definitionally equal to `0` for a variable `k : Fin 1`. Over a subsingleton every `M j`
is equal to `M i`, so `ofSubsingletonₗ'` is `ofSubsingletonₗ` followed by the casts
`LinearEquiv.cast : M j ≃ₗ[R] M i`, which reduce away when evaluated.

The declarations are generic and live in Mathlib's namespaces, as candidates for upstreaming.
`ofSubsingletonₗ'` is meant to be upstreamed as a generalisation of `MultilinearMap.ofSubsingletonₗ`
itself to dependent families, of which the constant family is the special case; the prime is a
stopgap until then.
-/

@[expose] public section

namespace MultilinearMap

variable {R : Type*} [CommSemiring R] {ι : Type*} {M : ι → Type*} {N : Type*}
  [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] [AddCommMonoid N] [Module R N]

/-- The dependent version of `MultilinearMap.ofSubsingletonₗ`: when `ι` has at most one element
`i`, a multilinear map on the family `M` is the same as a linear map on `M i`. Every `M j` is
`M i`, so this is `ofSubsingletonₗ` composed with the casts `M j ≃ₗ[R] M i`. -/
def ofSubsingletonₗ' [Subsingleton ι] (i : ι) : (M i →ₗ[R] N) ≃ₗ[R] MultilinearMap R M N :=
  (ofSubsingletonₗ R R (M i) N i).trans <|
    LinearEquiv.multilinearMapCongrLeft fun j ↦ LinearEquiv.cast (Subsingleton.elim j i)

@[simp]
theorem ofSubsingletonₗ'_apply_apply [Subsingleton ι] (i : ι) (f : M i →ₗ[R] N)
    (x : ∀ j, M j) : ofSubsingletonₗ' i f x = f (x i) :=
  rfl

@[simp]
theorem ofSubsingletonₗ'_symm_apply [Subsingleton ι] (i : ι) (f : MultilinearMap R M N)
    (x : ∀ j, M j) : (ofSubsingletonₗ' i).symm f (x i) = f x :=
  DFunLike.congr_fun ((ofSubsingletonₗ' i).apply_symm_apply f) x

end MultilinearMap

namespace LinearMap

variable {R : Type*} [CommSemiring R] {M : Fin 2 → Type*} {N : Type*}
  [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] [AddCommMonoid N] [Module R N]

/-- A bilinear map `M 0 →ₗ[R] M 1 →ₗ[R] N`, regarded as a multilinear map on the family `M` indexed
by `Fin 2`. -/
def uncurryFinTwo (f : M 0 →ₗ[R] M 1 →ₗ[R] N) : MultilinearMap R M N :=
  uncurryLeft <|
    (MultilinearMap.ofSubsingletonₗ' (M := fun i : Fin 1 ↦ M i.succ) 0).toLinearMap ∘ₗ f

@[simp]
theorem uncurryFinTwo_apply (f : M 0 →ₗ[R] M 1 →ₗ[R] N) (x : ∀ i, M i) :
    uncurryFinTwo f x = f (x 0) (x 1) :=
  rfl

@[simp]
theorem uncurryFinTwo_add (f g : M 0 →ₗ[R] M 1 →ₗ[R] N) :
    uncurryFinTwo (f + g) = uncurryFinTwo f + uncurryFinTwo g :=
  rfl

@[simp]
theorem uncurryFinTwo_smul (c : R) (f : M 0 →ₗ[R] M 1 →ₗ[R] N) :
    uncurryFinTwo (c • f) = c • uncurryFinTwo f :=
  rfl

end LinearMap

/-! ### Composition along a composition -/

namespace MultilinearMap

section CompComposition

variable {R : Type*} [Semiring R] {n : ℕ} (c : Composition n)
variable {M : Fin n → Type*} {N : Fin c.length → Type*} {P : Type*}
variable [∀ i, AddCommMonoid (M i)] [∀ l, AddCommMonoid (N l)] [AddCommMonoid P]
variable [∀ i, Module R (M i)] [∀ l, Module R (N l)] [Module R P]

/-- The composite of a multilinear map `g` in k variables with k multilinear maps `f l`, one on
each block of a composition `c` of `n` into k blocks: the multilinear map in n variables
`x ↦ g (f 0 (x on block 0), …, f (k - 1) (x on block k - 1))`. -/
def compComposition (g : MultilinearMap R N P)
    (f : ∀ l, MultilinearMap R (fun j ↦ M (c.embedding l j)) (N l)) : MultilinearMap R M P :=
  (domDomCongrLinearEquiv' R ℕ M P c.blocksFinEquiv.symm).symm (g.compMultilinearMap f)

@[simp]
theorem compComposition_apply (g : MultilinearMap R N P)
    (f : ∀ l, MultilinearMap R (fun j ↦ M (c.embedding l j)) (N l)) (x : ∀ i, M i) :
    compComposition c g f x = g fun l ↦ f l fun j ↦ x (c.embedding l j) :=
  rfl

end CompComposition

/-- A multilinear map is additive in each variable: if the `i`-th input is a signed sum, the value
is the signed sum of the values with the `i`-th input replaced by each summand. -/
lemma map_eq_sum_units_smul_update {R ι κ N : Type*} [Semiring R] [DecidableEq ι] [Fintype κ]
    {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [AddCommGroup N] [Module R N]
    (F : MultilinearMap R M N) (w : ∀ i, M i) (i : ι) (c : κ → ℤˣ) (y : κ → M i)
    (hw : w i = ∑ q, c q • y q) :
    F w = ∑ q, c q • F (Function.update w i (y q)) := by
  calc F w = F.toLinearMap w i (∑ q, c q • y q) := by
        rw [← hw, toLinearMap_apply, Function.update_eq_self]
    _ = ∑ q, c q • F (Function.update w i (y q)) := by
        simp only [_root_.map_sum, Units.smul_def, _root_.map_zsmul, toLinearMap_apply]

end MultilinearMap
