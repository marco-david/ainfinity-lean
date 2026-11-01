/-
Copyright (c) 2026 Zhan Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhan Shi
-/
module

public import Mathlib.LinearAlgebra.Multilinear.Curry

/-! # Multilinear maps in one and two variables

This file builds multilinear maps in one or two variables from linear and bilinear maps,
for dependent families of modules. It saves proving the `map_update_add'` and
`map_update_smul'` fields of `MultilinearMap` by hand.

## Main definitions

* `MultilinearMap.ofSubsingletonₗ'`: when `ι` has at most one element `i`, linear maps
  `M i →ₗ[R] N` are equivalent to multilinear maps on the family `M`.
* `LinearMap.uncurryFinTwo`: a bilinear map `M 0 →ₗ[R] M 1 →ₗ[R] N` as a multilinear map on a
  family `M` indexed by `Fin 2`.

## Implementation notes

Mathlib's `MultilinearMap.ofSubsingleton` only covers non-dependent families `fun _ : ι ↦ M₂`.
It does not apply to a family such as `fun k : Fin 1 ↦ M k.castSucc`, because `k.castSucc` is
not definitionally equal to `0` for a variable `k : Fin 1`. Over a subsingleton every `M j`
is equal to `M i`, so `ofSubsingletonₗ'` is `ofSubsingletonₗ` followed by the casts
`LinearEquiv.cast : M j ≃ₗ[R] M i`, which reduce away when evaluated.

The declarations are generic and live in Mathlib's namespaces, as candidates for upstreaming.
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

/-- A bilinear map `M 0 → M 1 → N`, regarded as a multilinear map on the family `M` indexed
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
