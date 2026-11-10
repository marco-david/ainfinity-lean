/-
Copyright (c) 2026 Zhan Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhan Shi
-/
module

public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Multilinear.Curry

/-! # Bilinear maps as multilinear maps in two variables

This file regards a bilinear map `M 0 →ₗ[R] M 1 →ₗ[R] N` on a family of modules `M` indexed by
`Fin 2` as a multilinear map on `M`. It saves proving the `map_update_add'` and
`map_update_smul'` fields of `MultilinearMap` by hand.

## Main definitions

* `LinearMap.uncurryFinTwo`: a bilinear map `M 0 →ₗ[R] M 1 →ₗ[R] N` as a multilinear map on a
  family `M` indexed by `Fin 2`.

## Implementation notes

The two variables are uncurried one at a time with Mathlib's `LinearMap.uncurryLeft`, the last
one landing in the multilinear maps on the empty family through
`MultilinearMap.constLinearEquivOfIsEmpty`. The declaration is generic and lives in Mathlib's
`LinearMap` namespace, as a candidate for upstreaming.
-/

@[expose] public section

namespace LinearMap

variable {R : Type*} [CommSemiring R] {M : Fin 2 → Type*} {N : Type*}
  [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] [AddCommMonoid N] [Module R N]

/-- A bilinear map `M 0 →ₗ[R] M 1 →ₗ[R] N`, regarded as a multilinear map on the family `M` indexed
by `Fin 2`. -/
def uncurryFinTwo (f : M 0 →ₗ[R] M 1 →ₗ[R] N) : MultilinearMap R M N :=
  uncurryLeft <| (multilinearCurryLeftEquiv R (fun i : Fin 1 ↦ M i.succ) N).symm.toLinearMap ∘ₗ
    f.compr₂ (MultilinearMap.constLinearEquivOfIsEmpty R R (fun i : Fin 0 ↦ M i.succ.succ) N)

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
